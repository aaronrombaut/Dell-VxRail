#!/bin/env python
# -*- coding:utf-8 -*-

# Copyright (c) 2015 Dell Inc. or its subsidiaries. All Rights Reserved.
#
# This software contains the intellectual property of Dell Inc. or is licensed to Dell Inc. from third parties.
# Use of this software and the intellectual property contained therein is expressly limited to the terms and 
# conditions of the License Agreement under which it is provided by or on behalf of Dell Inc. or its subsidiaries.

"""
Utility for VxRail Node Upgrade
Script Path at marvin: marvin/application/marvin_webapp/src/main/resources/scripts
"""

__version__ = '0.1'

import io
import os
import re
import sys
sys.path.append('/opt/vxrail/lib/')

sys.path.append('/opt/vxrail/bin/')
import copy
import enum
import json
import time
import glob
import shlex
import random
import shutil
import string
import hashlib
import logging
import zipfile
import argparse
import platform
import operator
import requests
import subprocess
import configparser
import xml.etree.ElementTree as ET

from io import BytesIO
from pyVim import connect as pyvim_connect
from pyVmomi import vim, vmodl

from requests.packages.urllib3.exceptions import InsecureRequestWarning
requests.packages.urllib3.disable_warnings(InsecureRequestWarning)


# Constant variables

SCRIPT_DIR = os.path.dirname(os.path.realpath(__file__))
RECOVERY_DIR = 'recovery'

MANIFEST_FILE = 'manifest.xml'
VXNODE_CONFIG_DIR_NAME = 'vxnode_config'
VXNODE_CONFIG_FILE_NAME = 'vxnode.config'
METADATA_FILE_NAME = 'VXRAIL-SYSTEM.MF'

SYSTEM_INIT_TIMEOUT = 300
PSERVICE_INIT_TIMEOUT = 900
FIRMWARE_UPDATE_TIMEOUT = 3600

# API version we plan to use
VIM_VERSION = 'vim.version.version10'

PTA_VIB_NAME = 'dellptagent'
PS_VIB_NAME = 'platform-service'

# User name to call PS API
PSA_ACCOUNT = 'pservice_agent'

ISM_RESET_SCRIPT_CONTENT = """\
#!/bin/sh

#run dcism-netmon-watchdog
echo -e "dcism-netmon-watchdog script, input value: $1"
if [ $1 == 'reset' ]; then
# After iSM installation, it will take about 2-3 minutes to initialization, so loop checking status
# If it is still not running after timeout, run stop/reset command
    echo "Try to get iSM status before calling reset command"
    if [ -e /opt/dell/srvadmin/iSM/bin/dchosmicli ]; then
        loop_times=0
        while [ $loop_times -lt 20 ]; do
            status=`/opt/dell/srvadmin/iSM/bin/dchosmicli 7 261`
            if [ $? -eq 0 ];  then
                echo "iSM is running, status result: $status"
                exit 0
            fi
            let loop_times++;
            echo "iSM status: $status, loop times: $loop_times"
            sleep 10
        done
        echo "iSM status is still not running after $loop_times times, call iSM stop and reset command"
    fi

    echo "Start to run iSM stop and reset command"
    if [ -e /etc/init.d/dcism-netmon-watchdog ]; then
        stop_value=`/etc/init.d/dcism-netmon-watchdog stop`
        echo "Stop iSM, return value: $stop_value, return code: $?"
        return_value=`/etc/init.d/dcism-netmon-watchdog start upgrade`
        if [ $? -eq 0 ]; then
            echo "Succeeded to run dcism-netmon-watchdog,return value: $return_value"
            if [ -e /opt/dell/srvadmin/iSM/bin/dchosmicli ]; then
                # After call reset command, it should wait for a while, then start to check, the max timeout is 200 seconds
                echo "Sleep 20 seconds, then start to check iSM status"
                sleep 20
                loop_times=0
                while [ $loop_times -lt 20 ]; do
                    ism_status=`/opt/dell/srvadmin/iSM/bin/dchosmicli 7 261`
                    if [ $? -eq 0 ];  then
                        echo "iSM is running, succeeded to reset it"
                        exit 0
                    fi
                    let loop_times++;
                    echo "iSM status: $ism_status, loop times: $loop_times"
                    sleep 10
                done
                echo "iSM status is still not running after $loop_times times, exit"
                exit 4
            else
                echo "Not find /opt/dell/srvadmin/iSM/bin/dchosmicli, sleep 180 seconds."
                sleep 180
                exit 2
            fi
        else
            echo "Failed to run dcism-netmon-watchdog,return value: $return_value"
            sleep 10
            exit 3
        fi
    else
        echo "Not find dcism-netmon-watchdog file, exit."
        exit 1
    fi
elif [ $1 == 'status' ]; then
    echo "Try to get iSM status"
    if [ -e /opt/dell/srvadmin/iSM/bin/dchosmicli ]; then
        loop_times=0
        while [ $loop_times -lt 20 ]; do
            status=`/opt/dell/srvadmin/iSM/bin/dchosmicli 7 261`
            if [ $? -eq 0 ];  then
                echo "iSM is running, status result: $status"
                exit 0
            fi
            let loop_times++;
            echo "iSM status: $status, loop times: $loop_times"
            sleep 10
        done
        echo "iSM status is still not running after $loop_times times, exit"
        exit 4
    else
        echo "Not find /opt/dell/srvadmin/iSM/bin/dchosmicli."
        exit 0
    fi
else
    echo "Input error value: $1"
    exit 1
fi
"""

CROWNHILL_CONFLICT_VIBS = [
    {'name': 'scsi-qedil'},
    {'name': 'dellptagent', 'relation': '<', 'version': '2.0'},
    {'name': 'dellptagent', 'relation': 'like', 'version': 'DEL.670'},
    {'name': 'dcism', 'relation': 'like', 'version': 'ESXi6'}
]

FP_ALTERNATIVE_VIBS = ['dellptagent', 'dcism', 'vmware-perccli64']

GENERIC_HOOK_TASKS = {
    'restore_ptagent_auth': {
        'type': "restore_ptagent_auth",
        'name': "Restore HTTP authentication setting for PTAgent",
        'install_order': -1,
        'async': False,
        'visible': True,
    }
}

ESXI_PATCH_HOOK_TASKS = {
    'revert_interrupt_mapping': {
        'type': "revert_interrupt_mapping",
        'name': "Revert interrupt mapping for E665/P675 with ESXi 6.7",
        'install_order': -1,
        'async': False,
        'visible': True,
    }
}

VLCM_MIN_RELEASE = "7.0.240"

#Version that start reduce ptagent dependence
REDUCE_PTA_VERSION = "7.0.240"

CUSTOMIZE_DRIVER_MIN_RELEASE = "7.0.300"
CUSTOMIZE_DRIVERS = [
    {'id': "MRVL-QLogic-FC", 'legacy_vibs': ['qlnativefc']},
]

DEPRECATED_DRIVER_MIN_RELEASE = "7.0.300"
DEPRECATED_DRIVERS = [
    {'id': "Intel-i40en-ens", 'legacy_vibs': ['i40en-ens']},
]

# Logging configuration

def setup_logger_handlers(logger_name):
    logger = logging.getLogger(logger_name)

    logger.setLevel(logging.DEBUG)
    # create file handler which logs even debug messages
    if platform.system() == 'VMkernel':
        log_file = os.path.join('/var/run/log', "%s.log" % logger_name)
    else:
        log_file = os.path.join(SCRIPT_DIR, "%s.log" % logger_name)
    file_handler = logging.FileHandler(log_file)
    file_handler.setLevel(logging.DEBUG)
    # create formatter and add it to the handlers
    formatter = logging.Formatter(
        "%(asctime)s %(name)s: [%(funcName)s] %(levelname)s - %(message)s",
        "%Y-%m-%d %H:%M:%S")
    file_handler.setFormatter(formatter)

    # add the handlers to the logger
    logger.addHandler(file_handler)

    return logger


logger = setup_logger_handlers('vxnode-upgrade')

# define mapping relationship for component in nodeManifestFile.xml
# and vxrail firmware list command
FIRMWARE_MAPPING = {
    'BIOS': 'bios',
    'BMC': 'bmc',
    'NIC_FIRMWARE': 'nic',
    'DISK_CTLR_FIRMWARE': 'disk_ctlr',
    'DISK_FIRMWARE': 'disk',
    'BACKPLANE_FIRMWARE': 'backplane',
    'BOSS_FIRMWARE': 'boss',
    'CPLD_FIRMWARE': 'cpld',
    'M2_SATA_FIRMWARE': 'm2sata',
    'PSU_FIRMWARE': 'psu',
    'PM_FIRMWARE': 'pm',
    'IDSDM_FIRMWARE': 'idsdm',
    'DCPM_FIRMWARE': 'dcpm',
}

# define the firmware components which has dependency on other compoment.
# idsdm has dependency on iDrac version
# dcpm has dependency on platform-service vib
RUNTIME_CHECK_FIRMWARE_LIST = ['idsdm', 'dcpm']


class TaskStatus(enum.IntEnum):
    NotStarted = 0
    Scheduled = 1
    Running = 2
    AwaitRestart = 3
    Canceled = 4
    Completed = 5
    Failed = 6


class TaskStateInfo(object):

    def __init__(self):
        self.status = TaskStatus.NotStarted
        self.progress = 0
        self.start_time = float('nan')
        self.end_time = float('nan')
        self.ps_job = ''

    def update(self, **kwargs):
        allowed_keys = [
            'status',
            'progress',
            'start_time',
            'end_time',
            'ps_job'
        ]
        self.__dict__.update(
            (k, v) for k, v in kwargs.items() if k in allowed_keys)

    def dumps(self):
        raw_data = "%d %d %f %f %s" % (
            self.status,
            self.progress,
            self.start_time,
            self.end_time,
            self.ps_job
        )
        return raw_data

    @classmethod
    def parse(cls, raw_data):
        obj = cls()
        raw_fields = raw_data.split()

        for (idx, value) in enumerate(raw_fields):
            if idx == 0:
                obj.status = TaskStatus(int(value))
            elif idx == 1:
                obj.progress = int(value)
            elif idx == 2:
                obj.start_time = float(value)
            elif idx == 3:
                obj.end_time = float(value)
            elif idx == 4:
                obj.ps_job = str(value)

        return obj

# Exceptions


class UpdateJobError(Exception):

    def __init__(self, message):
        super(UpdateJobError, self).__init__(message)


class TaskListException(Exception):

    def __init__(self, message):
        super(TaskListException, self).__init__(message)


class VxNodeUpgradeError(Exception):

    def __init__(self, message, exitcode=2):
        super(VxNodeUpgradeError, self).__init__(message)
        self.exitcode = exitcode


# Helper functions & classes

def equals_ignore_case(a, b):
    if isinstance(a, str):
        a = a.lower()

    if isinstance(b, str):
        b = b.lower()

    return operator.eq(a, b)


def contains_ignore_case(a, b):
    if isinstance(a, str):
        a = a.lower()
    else:
        for (idx, value) in enumerate(a):
            if isinstance(value, str):
                a[idx] = value.lower()

    if isinstance(b, str):
        b = b.lower()

    return operator.contains(a, b)


def compare_version_string(ver1, ver2):
    splitted1 = ver1.split('.')
    splitted2 = ver2.split('.')

    for (x, y) in zip(splitted1, splitted2):
        if x == y:
            continue
        if x.isdecimal() and y.isdecimal():
            x_number = int(x)
            y_number = int(y)
            return x_number - y_number
        else:
            if x > y:
                return 1
            else:
                return -1

    if len(splitted1) == len(splitted2):
        return 0
    else:
        return len(splitted1) - len(splitted2)

def str2bool(val):
    val = val.lower()
    if val in ('y', 'yes', 't', 'true', 'on', '1'):
        return True
    elif val in ('n', 'no', 'f', 'false', 'off', '0'):
        return False
    else:
        raise ValueError("Not a boolean string %r" % (val,))

def check_firmware_component(type_value):
    if type_value.lower().endswith('_firmware') or \
            equals_ignore_case(type_value, 'BIOS') or \
            equals_ignore_case(type_value, 'BMC'):
        return True
    else:
        return False


def check_esxi_vib_component(type_value):
    if equals_ignore_case(type_value, 'ESXi_VIB') or \
            equals_ignore_case(type_value, 'VXRAIL_'):
        return True
    else:
        return False

def is_dell_13G_platform(model):
    dell13g_name = re.compile(
        'VxRail\s+(E460F|E460|V470|V470F|P470F|P470|S470)',
        flags=re.I
    )
    return True if dell13g_name.search(model) else False


def is_dell_non_13G_platform(vender, model):
    if "dell" in vender.lower() and not is_dell_13G_platform(model):
        return True
    return False

def is_alton_amd_platform(model):
    alton_amd = re.compile(
        r'^VxRail\s+(E665|E665F|E665N|P675F|P675N)$',
        flags=re.I
    )
    return True if alton_amd.search(model) else False

def is_esxi_async_driver(version):
    match = re.search(r'-\d+OEM\.', version)

    if match:
        return True
    
    return False


def run_command(cmdstr, env=None, no_exc=False, universal_newlines=True, sensitive=None, cmd_id=None):
    """Run a external command the return it's output

    This function is used to invoke some external commands.
    And return it's output. The command is invoked with a shell

    Arguments:
        cmdstr {string} -- Command string to be executed

    Keyword Arguments:
        env {dict} -- The environment variables

    Returns:
        [string] -- The output of the command

    Raises:
        CalledProcessError -- If the process didn't exit successfully. this exception will be raised.
    """
    if isinstance(cmdstr, str):
        cmds = shlex.split(cmdstr)
    else:
        cmds = cmdstr
    proc = subprocess.Popen(cmds, stdout=subprocess.PIPE, stderr=subprocess.PIPE, env=env,
                            close_fds=True, shell=False, universal_newlines=universal_newlines)
    out, err = proc.communicate()
    if proc.returncode:
        # need to strip sensitive data before we logging it
        if sensitive is not None:
            to_replaced = '*' * len(sensitive)
            cmdstr = cmdstr.replace(sensitive, to_replaced)
            if out is not None:
                out = out.replace(sensitive, to_replaced)
            if err is not None:
                err = err.replace(sensitive, to_replaced)
        logger.error('Command "%s" failed with:\n\nOUT:\n%sERR:\n%s', cmd_id or cmdstr, out, err)
        if not no_exc:
            raise CalledProcessError(proc.returncode, cmd_id or cmdstr, err)
    return out


# password source table
PASSWORD_CHARACTERS = "abcdefghijklmnopqrstuvwxyz" \
                      "ABCDEFGHIJKLMNOPQRSTUVWXYZ" \
                      "0123456789" \
                      "!@#$%^&*()_+|[];,./<>?:`~"


def generate_new_password(num=32):
    """Create a random password

    Arguments:
        num {[int]} -- Then length of the password
    """
    seed = run_command('/usr/bin/openssl rand -hex %d' % num).strip()
    passwd_idx = [
        int(c[0] + c[1], 16) for c in zip(*([iter(seed)] * 2))
    ]
    passwd = [
        PASSWORD_CHARACTERS[i % len(PASSWORD_CHARACTERS)] for i in passwd_idx
    ]
    return ''.join(passwd)


class EsxCLIError(Exception):

    def __init__(self, returncode, cmd, output):
        self.returncode = returncode
        self.cmd = cmd
        self.output = output
        msg = "ESX command '{cmd}' returned non-zero exit status {returncode}".format(
            cmd=cmd, returncode=returncode)
        super(EsxCLIError, self).__init__(msg)


class EsxcliWrapper(object):
    """
    Helper class for EsxCli. Raise exception if the command failed.
    """

    def __init__(self):
        self._re_xmltag = re.compile(r'\{(.+)\}(.+)$')

    @staticmethod
    def _run_command(cmdstr):
        proc = subprocess.Popen(shlex.split(cmdstr), shell=False,
                                stderr=subprocess.PIPE,
                                stdout=subprocess.PIPE,
                                universal_newlines=False)
        stdout, stderr = proc.communicate()

        if not 'system account' in cmdstr and not 'system permission' in cmdstr:
            logger.debug('Output of command %s:%s', cmdstr, stdout)

        if proc.returncode != 0:
            if 'system account' in cmdstr or 'system permission' in cmdstr:
                logger.debug('clean up the cmdstr')
                cmdstr = ""

            err_msg = 'Command {0} failed.  RC: {1}. Details: {2}.'.format(
                cmdstr, proc.returncode, stderr
            )
            logger.error(err_msg)

            raise EsxCLIError(proc.returncode, cmdstr, stderr)
        return stdout

    def execute(self, cmdstr):
        # bug-2215484, while the output include non-ascii charactes,
        # universal_newlines = Ture cause read data failed. in python3.5,
        # no paramter to specify the encoding of output stream.
        output = EsxcliWrapper._run_command(
            'esxcli --formatter=xml ' + cmdstr)
        xmldata = ET.fromstring(output)

        m_xmlns = self._re_xmltag.match(xmldata.tag)
        if m_xmlns is not None:
            nsmap = {'esxcli': m_xmlns.group(1)}
        else:
            nsmap = None

        root = xmldata.find('esxcli:root', nsmap)
        if root and len(root) > 0:
            return self._parse_object(root[0], nsmap)
        else:
            return None

    def _parse_object(self, parent, nsmap):
        m_xmltag = self._re_xmltag.match(parent.tag)
        if m_xmltag is not None:
            tagname = m_xmltag.group(2)
        else:
            tagname = parent.tag

        if tagname == 'string':
            return parent.text
        elif tagname == 'integer':
            return int(parent.text)
        elif tagname == 'boolean':
            return str2bool(parent.text)
        elif tagname == 'structure':
            obj = dict()
            for field in parent.findall('esxcli:field', nsmap):
                key = field.attrib['name']
                if len(field) > 0:
                    value = self._parse_object(field[0], nsmap)
                    if value is not None:
                        obj[key] = value
            return obj
        elif tagname == 'list':
            obj = list()
            for child in parent:
                obj.append(self._parse_object(child, nsmap))
            return obj
        else:
            raise ValueError("Invalid tag '%s' for esxcli output" % tagname)

    def __call__(self, cmdstr):
        return self.execute(cmdstr)


ESXCLI = EsxcliWrapper()  # pylint: disable=E0012


class HostConnection(object):  # pylint: disable=too-many-public-methods
    """
    The helper class for capture common task interfacing with Web Service API.
    """

    def disconnect(self):
        """
        Disconnect the connection
        """
        self.content = None
        pyvim_connect.Disconnect(self.instance)
        self.instance = None

    def connect(self):
        """
        Establish the connection to the WebService API.
        """
        self.instance = pyvim_connect.Connect(user='vpxuser', version=VIM_VERSION)
        self.content = self.instance.content

    def __init__(self):
        self.instance = None
        self.content = None

    def __enter__(self):
        self.connect()
        return self

    def __exit__(self, exc_typ, exc_val, tback):
        self.disconnect()

    def _get_objects(self, types):
        """
        Helper function that return objects of types listed by @parm types
        """
        view = self.content.viewManager.CreateContainerView(self.content.rootFolder,
                                                            types, True)
        obj_list = view.view
        view.Destroy()
        return obj_list

    def get_all_vms(self):
        """
        Return all VMs in this host.
        """
        return self._get_objects([vim.VirtualMachine])

    def get_all_hosts(self):
        """
        Return visible host system object of this host.
        Since this module is intended to be connected to the host locally.
        This should only be one host returned.
        """
        return self._get_objects([vim.HostSystem])

    def wait_for_task(self, task, timeout=600):
        """
        Utility function that wait a ESX task finishing.
        This will raise the exception if it failed.
        """
        expiry = time.time() + timeout
        while time.time() < expiry:
            if task.info.state in ('success', 'error'):
                break
            time.sleep(1)
        else:
            raise Exception(
                'Task "%s" failed to complete before timeout' % str(task))
        if task.info.state == 'error':
            raise task.info.error

    def shutdown_all_vms(self):
        vms = self.get_all_vms()
        for vm in vms:
            if vm.summary.runtime.powerState == 'poweredOn':
                self.wait_for_task(vm.PowerOffVM_Task())
                logger.debug("Found running VM. Shutdown command has sent")
        logger.debug("There is no running VM")

    def remove_all_vms(self):
        vms = self.get_all_vms()
        for vm in vms:
            self.wait_for_task(vm.Destroy())
            logger.debug("Remove VM command has sent")

    def delete_single_vsan(self):
        host_sys = self.get_all_hosts()[0]
        vsan_sys = host_sys.configManager.vsanSystem
        if vsan_sys.config.enabled:
            vsan_spec = vim.VsanHostConfigInfo(enabled=False)
            task = vsan_sys.UpdateVsan_Task(vsan_spec)
            self.wait_for_task(task)
        if vsan_sys.config.storageInfo.diskMapping:
            task = vsan_sys.RemoveDiskMapping(vsan_sys.config.storageInfo.diskMapping)
            self.wait_for_task(task)
        logger.debug("Single node vSAN was deleted.")


class PServiceClient(object):
    """Simple client for talking over PS APIs."""

    def __init__(self, host="127.0.0.1", username=PSA_ACCOUNT, password=None, port=9090):
        """Creates client object

        :param host: IP
        :param username: username
        :param password: password
        :param port: port
        """

        self._host = host
        self._username = username
        self._password = password
        self._port = port
        self._logger = logger

    def _make_endpoint(self, resource_uri):
        return ('https://%(host)s:%(port)s%(resource_uri)s' % {
            'host': self._host,
            'port': self._port,
            'resource_uri': resource_uri})

    def _do_request(self, endpoint, method='get', payload=None, required_data=False):
        request_func = getattr(requests, method)
        verify_flag = False

        extra_args = {}
        if payload is not None:
            extra_args['headers'] = {'Content-Type': 'application/json'}
            extra_args['data'] = json.dumps(payload)

        try:
            resp = request_func(
                endpoint,
                auth=requests.auth.HTTPBasicAuth(self._username,
                                                 self._password),
                # TODO(ifarkas): enable cert verification
                verify=verify_flag,
                **extra_args)

        except requests.exceptions.RequestException as ex:
            error_msg = "A {error_type} error occurred while " \
                "communicating with {host}: {error}".format(
                    error_type=type(ex).__name__,
                    host=self._host,
                    error=ex)
            self._logger.error(error_msg)
            return None

        if not resp.ok:
            error_msg = "Invalid response status code:{status_code}, reason: {reason}".format(
                status_code=resp.status_code,
                reason=resp.reason)
            self._logger.error(error_msg)
            return None

        content_type = resp.headers['Content-Type']
        if content_type.split(';')[0] == 'application/json':
            return resp.json()
        elif required_data:
            error_msg = "Invalid response content {content_type}".format(
                content_type=content_type)
            self._logger.error(error_msg)

            return None

    def get(self, resource_uri, required_data=True):
        endpoint = self._make_endpoint(resource_uri)
        self._logger.debug('GET request %s' % endpoint)
        return self._do_request(endpoint, method='get', required_data=required_data)

    def post(self, resource_uri, payload, required_data=False):
        endpoint = self._make_endpoint(resource_uri)
        self._logger.debug('POST data %s' % payload)
        return self._do_request(endpoint, method='post', payload=payload, required_data=required_data)

    def checksum(self, path):
        """ Function to generate SHA512 code for DUP file. """
        with io.open(path, 'rb') as fp:
            sha512sum = hashlib.sha512()

            def _i_chunk():
                while True:
                    buf = fp.read(1024)
                    if buf:
                        yield buf
                    else:
                        break
            for chunk in _i_chunk():
                sha512sum.update(chunk)
            return sha512sum.hexdigest().upper()

    def get_fw_list(self, path):
        firmware_list = []
        fw_check_url = '/rest/ps/private/v1/lcm/fwcheck'

        reqest_body = {
            "FirmwareFolderPath": path,
            "CheckLevel": "Passed"
        }

        result = self.post(fw_check_url, reqest_body)

        if result:
            fw_list = result['Details']['Summary']
            for fw in fw_list:
                task = {
                    'type': "update_firmware",
                    'install_order': -1,
                    'async': True,
                    'visible': True,
                    'runtime_check': False,
                }
                task['name'] = "Update %s" % fw['Name']

                args = {}
                args['File'] = fw['File']

                if fw['DiscoveredVersion']:
                    args['installed_version'] = fw['DiscoveredVersion'][0]

                args['Version'] = fw['ExpectedVersion']
                args['UpgradeTime'] = 5
                task['args'] = args

                firmware_list.append(task)
        else:
            logger.debug("No firmware upgrade task returned from PS API")

        return firmware_list

    def update_firmware(self, fw_files):
        fw_upgrade_url = '/rest/ps/private/v1/lcm/fwupgrade'

        request_body = {
            "FirmwareFiles": [],
            "CheckPayloads": True,
            "CheckIDRACJobQueue": True,
            "AutoCleanRunningAndPendingJob": True,
            "UpgradeProgressTrackingLevel": "DEBUG",
            "AutoRetry": 3
        }

        for fw_file in fw_files:
            if fw_file.endswith(".EXE"):
                f = {}
                f['DUPName'] = fw_file
                f['FilePath'] = fw_file
                # from Magnus 7.0.350, Linzhi FWupdate update checksum has been changed to SHA512
                f['FileHash'] = self.checksum(f['FilePath'])
                f['Options'] = {"CheckVersion": True}
                request_body['FirmwareFiles'].append(f)

        result = self.post(fw_upgrade_url, request_body)

        if 'TaskID' in result['Details']:
            return result['Details']['TaskID']
        else:
            logger.debug('result: %s', result)
            return None

    def get_task_status(self, ps_task_id):
        status = "UNKNOWN"
        task_status = "NotStarted"
        status_url = "/rest/ps/private/v1/tasks/{task_id}".format(task_id=ps_task_id)

        result = self.get(status_url)

        if 'Status' in result:
            status = str(result['Status']).strip().upper()

        # logger.debug('Status: %s', status)

        if status == 'INITIATED':
            return status

        if status == 'COMPLETED':
            if result and 'Detail' in result.keys() and result['Detail']:
                task_status = str(result['Detail']['TaskStatus']).strip().upper()
                if task_status in ['COMPLETED',"SKIPPED"]:
                     return 'COMPLETED'
            return "ERROR"

        else:
            return "RUNNING"

class EsxSystemUtility(object):
    def __init__(self):
        self.ps_client = None

    def get_esxi_version(self):

        if platform.system() == 'VMkernel':
            esxi_version = platform.release()
            return esxi_version
        else:
            raise NotImplementedError("Current system is not supported")

    def get_esxi_system_version(self):
        if platform.system() == 'VMkernel':
            cmdline = 'system version get'
            result = ESXCLI.execute(cmdline)
            return result
        else:
            raise NotImplementedError("Current system is not supported")

    def get_esxi_account_list(self):
        if platform.system() == 'VMkernel':
            accounts = []
            esx_cmd = 'system account list'
            results = ESXCLI.execute(esx_cmd)

            for entry in results:
                username = entry.get('UserID', '').strip()
                if username:
                    accounts.append(username)

            return accounts
        else:
            raise NotImplementedError("Current system is not supported")

    def get_system_uptime(self):

        if platform.system() == 'VMkernel':
            esx_cmd = 'system stats uptime get'
            time_value = ESXCLI.execute(esx_cmd)  # in microseconds
            return time_value / (1000 * 1000)
        else:
            raise NotImplementedError("Current system is not supported")

    def get_hardware_platform(self):

        if platform.system() == 'VMkernel':
            esx_cmd = 'hardware platform get'
            hw_info = ESXCLI.execute(esx_cmd)
            return hw_info
        else:
            raise NotImplementedError("Current system is not supported")

    def get_firmware_list(self):
        firmware_list = []

        if platform.system() == 'VMkernel':
            esx_cmd = 'vxrail firmware list'
            results = ESXCLI.execute(esx_cmd)

            for entry in results:
                class_id = entry.get('id', '').strip()
                model = entry.get('model', '').strip()
                version = entry.get('version', '').strip()

                if class_id:
                    firmware_list.append({
                        'id': class_id,
                        'model': model,
                        'version': version
                    })

            return firmware_list
        else:
            raise NotImplementedError("Current system is not supported")

    def get_installed_vibs(self):
        '''
        Helper function to return installed VIB info by ESXi command
        @return: a dictionary of vib infor {name : version}
        For example:
        {'ixgben' : '1.6.5-1OEM.600.0.0.2768847'}
        '''
        installed_vibs = {}

        if platform.system() == 'VMkernel':
            esx_cmd = 'software vib list --rebooting-image'
            pending_results = ESXCLI.execute(esx_cmd)

            if pending_results:
                results = pending_results
            else:
                esx_cmd = 'software vib list'
                results = ESXCLI.execute(esx_cmd)

            for entry in results:
                name = entry.get('Name', '').strip()
                version = entry.get('Version', '').strip()
                if name:
                    # logger.debug("installed vib: %s, version: %s" % (name, version))
                    installed_vibs[name] = version

            return installed_vibs
        else:
            raise NotImplementedError("Current system is not supported")

    def get_installed_components(self):
        installed_pkgs = {}

        if platform.system() == 'VMkernel':
            esx_cmd = 'software component list --rebooting-image'
            pending_results = ESXCLI.execute(esx_cmd)

            if pending_results:
                results = pending_results
            else:
                esx_cmd = 'software component list'
                results = ESXCLI.execute(esx_cmd)

            for entry in results:
                name = entry.get('Name', '').strip()
                version = entry.get('Version', '').strip()
                if name:
                    # logger.debug("installed component: %s, version: %s" % (name, version))
                    installed_pkgs[name] = version

            return installed_pkgs
        else:
            raise NotImplementedError("Current system is not supported")


    def system_reboot(self):

        if platform.system() == 'VMkernel':
            cmdline = "reboot -f"
            self._exec_command(cmdline)
        else:
            raise NotImplementedError("Current system is not supported")

    def reset_ism_service(self):
        if platform.system() == 'VMkernel':
            script_path = os.path.join(SCRIPT_DIR, 'dcism-netmon-watchdog.sh')
            with open(script_path, 'w') as fp:
                fp.write(ISM_RESET_SCRIPT_CONTENT)
            cmdline = "sh %s reset" % script_path
            self._exec_command_with_output(cmdline)
        else:
            raise NotImplementedError("Current system is not supported")

    def destroy_node_vsan(self):
        if platform.system() == 'VMkernel':
            self.shutdown_all_vms()
            self.remove_all_vms()
            self.delete_single_vsan()
        else:
            raise NotImplementedError("Current system is not supported")

    def set_kernel_setting(self, setting, value):
        if platform.system() == 'VMkernel':
            logger.debug("Set kernel setting: %s=%s", setting, value)
            esx_cmd = "system settings kernel set -s {setting} -v {value}".format(setting=setting, value=value)
            result = ESXCLI.execute(esx_cmd)
            return result
        else:
            raise NotImplementedError("Current system is not supported")

    def enable_ptagent_auth(self, force=False):
        if platform.system() == 'VMkernel':
            if not force:
                cmdline = "/opt/dell/DellPTAgent/tools/pta_cfg get rest_auth_enabled"
                result = self._exec_command_with_output(cmdline)
                if result.returncode != 0:
                    logger.error("Failed to retrieve current value of rest_auth_enabled")
                    return

                if isinstance(result.stdout, bytes):
                    output = result.stdout.decode()
                else:
                    output = result.stdout
                value_match = re.search(r'Value:\s*(\S+)', output)
                if value_match is not None:
                    cfg_value = value_match.group(1)
                else:
                    logger.error("Failed to parse the output of pta_cfg!")
                    return

                if cfg_value.strip().lower != "true":
                    cmdline = "/opt/dell/DellPTAgent/tools/pta_cfg set rest_auth_enabled=True"
                    self._exec_command(cmdline)
                else:
                    logger.info("HTTP authentication on PTAgent is already enabled.")
            else:
                cmdline = "/opt/dell/DellPTAgent/tools/pta_cfg set rest_auth_enabled=True"
                self._exec_command(cmdline)
        else:
            raise NotImplementedError("Current system is not supported")

    def get_hostd_status(self):

        if platform.system() == 'VMkernel':
            try:
                connection = pyvim_connect.Connect(user='vpxuser')
                pyvim_connect.Disconnect(connection)
                return True
            except Exception:
                logger.warning("Hostd is not ready")
                return False
        else:
            logger.warning("The system is not ESXi!")
            return False

    def get_ptagent_status(self):

        if platform.system() == 'VMkernel':
            cmdline = "/etc/init.d/DellPTAgent status"
            result = self._exec_command_with_output(cmdline)
            if result and result.returncode == 0:
                output = result.stdout.strip()
                if output.find(b'DellPTAgent is running') != -1:
                    logger.debug('Dell PTAgent is running')
                    return True

            return False
        else:
            logger.warning("The system is not ESXi!")
            return False

    def disable_storage_scan_for_ptagent_service(self):

        if platform.system() == 'VMkernel':
            cmdline = "/opt/dell/DellPTAgent/tools/pta_cfg get in_band_device_scan_enabled"
            result = self._exec_command_with_output(cmdline)
            logger.info("returncode=%d" % result.returncode)
            logger.info("stdout=%r" % result.stdout)
            if result and result.returncode != 0:
                logger.warn(
                    "returncode=%d, failed to disable storage scan for ptagent." % result.returncode)
                return False
            if result.stdout.find(b'Value: False') != -1:
                logger.info("Already disable storage scan for ptagent.")
                return True
            cmdline = "/opt/dell/DellPTAgent/tools/pta_cfg set in_band_device_scan_enabled=False"
            result = self._exec_command_with_output(cmdline)
            logger.info("returncode=%d" % result.returncode)
            logger.info("stdout=%r" % result.stdout)
            if result and result.returncode != 0:
                logger.warn(
                    "returncode=%d, failed to disable storage scan for ptagent." % result.returncode)
                return False
            else:
                logger.info(
                    "returncode=%d, succeeded to disable storage scan for ptagent." % result.returncode)
                return True
        else:
            raise NotImplementedError("Current system is not supported")

    def start_ptagent_service(self):

        if platform.system() == 'VMkernel':
            cmdline = "/etc/init.d/DellPTAgent start"
            self._exec_command(cmdline)
        else:
            raise NotImplementedError("Current system is not supported")

    def restart_pservice(self):

        if platform.system() == 'VMkernel':
            cmdline = "/etc/init.d/vxrail-pservice restart"
            self._exec_command(cmdline)
        else:
            raise NotImplementedError("Current system is not supported")

    def get_pservice_status(self):

        if platform.system() == 'VMkernel':
            esx_cmd = 'vxrail agent get'
            try:
                result = ESXCLI.execute(esx_cmd)
                status = result.get('initialized', False)
                return status
            except EsxCLIError:
                logger.error("Get Platform Service status failed")
                return False
        else:
            logger.warning("The system is not ESXi!")
            return False

    def get_maintenance_mode(self):

        if platform.system() == 'VMkernel':
            esx_cmd = "system maintenanceMode get"
            results = ESXCLI.execute(esx_cmd)
            if isinstance(results, str) and (results.lower() == 'enabled'):
                return True
            return False
        else:
            logger.warning("The system is not ESXi!")
            return False

    def set_maintenance_mode(self, value, ignore_errors=False):

        if platform.system() == 'VMkernel':
            try:
                current = self.get_maintenance_mode()
                if current != value:
                    if value:
                        esx_cmd = "system maintenanceMode set -e true -m noAction"
                        ESXCLI.execute(esx_cmd)
                        logger.info('Enter maintenance mode')
                    else:
                        esx_cmd = "system maintenanceMode set -e false"
                        ESXCLI.execute(esx_cmd)
                        logger.info('Exit maintenance mode')
                else:
                    logger.debug(
                        "Current maintenance mode is already {}.".format(current))
            except EsxCLIError as e:
                if ignore_errors:
                    logger.warning("Ignore esxcli error: {}".format(e))
                else:
                    raise
        else:
            raise NotImplementedError("Current system is not supported")

    def check_system_ready(self):
        # after rebooting, we need to check the sysytem status
        # if hostd, platform service, ptagent started?
        if not esxutil.get_hostd_status():
            logger.error('Hostd is not ready')
            return False

        # ignore PTA check, since there is no PTA at Quanta
#        if not esxutil.get_ptagent_status():
#            logger.error('Dell PTAgent is not running')
#            return False

        if not esxutil.get_pservice_status():
            logger.error('VxRail Platform Service is not running')
            return False

        return True

    def install_software_vib(self, vib_url, nosigcheck=False):

        if platform.system() == 'VMkernel':
            extras = ""
            if nosigcheck:
                extras += '--no-sig-check '

            logger.debug('Try to install VIB: %s' % vib_url)
            _, ext = os.path.splitext(os.path.basename(vib_url))
            if ext == '.zip':
                esx_cmd = 'software vib install -d {depot} {extras}'.format(
                    depot=vib_url, extras=extras)
            else:
                esx_cmd = 'software vib install -v {viburl} {extras}'.format(
                    viburl=vib_url, extras=extras)

            result = ESXCLI.execute(esx_cmd)

            message = result.get('Message')
            logger.debug('Message: %s', message)
            reboot_required = result.get('RebootRequired', False)
            # install successfully
            logger.debug('VIB %s is successfully installed.', vib_url)

            if reboot_required:
                logger.debug(
                    'The system needs to be rebooted for the changes to be effective.')
            return reboot_required
        else:
            raise NotImplementedError("Current system is not supported")

    def update_software_vib(self, vib_url, nosigcheck=False):

        if platform.system() == 'VMkernel':
            extras = ""
            if nosigcheck:
                extras += '--no-sig-check '

            logger.debug('Try to update VIB: %s' % vib_url)
            _, ext = os.path.splitext(os.path.basename(vib_url))
            if ext == '.zip':
                esx_cmd = 'software vib update -d {depot} {extras}'.format(
                    depot=vib_url, extras=extras)
            else:
                esx_cmd = 'software vib update -v {viburl} {extras}'.format(
                    viburl=vib_url, extras=extras)

            result = ESXCLI.execute(esx_cmd)

            message = result.get('Message')
            logger.debug('Message: %s', message)
            reboot_required = result.get('RebootRequired', False)
            # update successfully
            logger.debug('VIB %s is successfully updated.', vib_url)

            if reboot_required:
                logger.debug(
                    'The system needs to be rebooted for the changes to be effective.')
            return reboot_required
        else:
            raise NotImplementedError("Current system is not supported")

    def remove_software_vib(self, vibname, live_install=False):

        if platform.system() == 'VMkernel':
            logger.debug("Try to remove software VIB %s", vibname)
            if live_install:
                esx_cmd = 'software vib remove -n {vibname}'.format(
                    vibname=vibname)
            else:
                esx_cmd = 'software vib remove --no-live-install -n {vibname}'.format(
                    vibname=vibname)
            result = ESXCLI.execute(esx_cmd)

            message = result.get('Message', '')
            logger.debug('Message : %s', message)
            reboot_required = result.get('RebootRequired', False)
            # remove successfully
            logger.debug('VIB %s is successfully removed.', vibname)

            if reboot_required:
                logger.debug(
                    'The system needs to be rebooted for the changes to be effective.')
            return reboot_required
        else:
            raise NotImplementedError("Current system is not supported")

    def remove_software_component(self, component_name):
    
        if platform.system() == 'VMkernel':
            logger.debug("Try to remove software component %s", component_name)

            esx_cmd = 'software component remove -n {component_name}'.format(
                component_name=component_name)

            result = ESXCLI.execute(esx_cmd)

            message = result.get('Message', '')
            logger.debug('Message : %s', message)
            reboot_required = result.get('RebootRequired', False)
            # remove successfully
            logger.debug('Component %s is successfully removed.', component_name)

            if reboot_required:
                logger.debug(
                    'The system needs to be rebooted for the changes to be effective.')
            return reboot_required
        else:
            raise NotImplementedError("Current system is not supported")

    def apply_software_component(self, bundle_url, nosigcheck=False):

        if platform.system() == 'VMkernel':
            extras = ""
            if nosigcheck:
                extras += '--no-sig-check '

            logger.debug('Try to install component: %s' % bundle_url)
            esx_cmd = 'software component apply -d {depot} {extras}'.format(
                depot=bundle_url, extras=extras)

            result = ESXCLI.execute(esx_cmd)

            message = result.get('Message')
            logger.debug('Message: %s', message)
            reboot_required = result.get('RebootRequired', False)
            # install successfully
            logger.debug('Component %s is successfully installed.', bundle_url)

            if reboot_required:
                logger.debug(
                    'The system needs to be rebooted for the changes to be effective.')
            return reboot_required
        else:
            raise NotImplementedError("Current system is not supported")

    def validate_esxi_patch(self, profile_name, patch_url):

        if platform.system() == 'VMkernel':
            logger.debug("Try to update ESXi patch %s", patch_url)
            esx_cmd = 'software profile validate -p {profile} -d {depot}'.format(
                profile=profile_name, depot=patch_url)
            result = ESXCLI.execute(esx_cmd)

            profile_vibs = result.get('VIBsinValidationProfileOnly', [])
            if len(profile_vibs) > 0:
                logger.debug('The ESXi patch is newer than current system.')
                return True
            else:
                logger.debug('The ESXi patch has already been installed')
                return False
        else:
            raise NotImplementedError("Current system is not supported")

    def update_esxi_patch(self, profile_name, patch_url, nosigcheck=False):

        if platform.system() == 'VMkernel':
            extras = ""
            if nosigcheck:
                extras += '--no-sig-check '
            esx_cmd = 'software profile update -p {profile} -d {depot} {extras}'.format(
                profile=profile_name, depot=patch_url, extras=extras)
            result = ESXCLI.execute(esx_cmd)

            message = result.get('Message')
            logger.debug('Message: %s', message)
            reboot_required = result.get('RebootRequired', False)
            # update successfully
            logger.debug('ESXi patch update is successfully completed.')

            if reboot_required:
                logger.debug(
                    'The system needs to be rebooted for the changes to be effective.')
            return reboot_required
        else:
            raise NotImplementedError("Current system is not supported")

    def prepare_esxi_account(self, username, password):
        if platform.system() == 'VMkernel':

            accounts = self.get_esxi_account_list()

            if username not in accounts:
                logger.debug("Trying to create temporary account")
                esx_cmd = 'system account add --id {0} -p {1} -c {1}'.format(username, password)
            else:
                esx_cmd = 'system account set --id {0} -p {1} -c {1}'.format(username, password)

            ESXCLI.execute(esx_cmd)

            esx_cmd = 'system permission set --id {0} --role Admin'.format(username)
            ESXCLI.execute(esx_cmd)
        else:
            raise NotImplementedError("Current system is not supported")

    def remove_esxi_account(self, username):
        if platform.system() == 'VMkernel':

            accounts = self.get_esxi_account_list()

            if username in accounts:
                logger.debug("Trying to reomve temporary account")
                esx_cmd = 'system permission unset --id {0}'.format(username)
                ESXCLI.execute(esx_cmd)

                esx_cmd = 'system account remove --id {0}'.format(username)
                ESXCLI.execute(esx_cmd)
        else:
            raise NotImplementedError("Current system is not supported")

    def get_esxi_profiles(self, patch_url):
        if platform.system() == 'VMkernel':
            esx_cmd = 'software sources profile list -d {depot}'.format(
                depot=patch_url)
            result = ESXCLI.execute(esx_cmd)

            logger.debug('Available ESXi image profiles: %s', result)
            return result
        else:
            raise NotImplementedError("Current system is not supported")

    def get_esxi_profile_info(self, profile_name, patch_url):
        if platform.system() == 'VMkernel':
            esx_cmd = 'software sources profile get -p {profile_name} -d {depot}'.format(
                profile_name=profile_name, depot=patch_url)
            result = ESXCLI.execute(esx_cmd)

            logger.debug('Profile name: %s', result.get("Name"))
            logger.debug('Profile VIBs: %s', result.get("VIBs"))
            return result
        else:
            raise NotImplementedError("Current system is not supported")

    def get_valid_image_profile(self, patch_url):
        profiles = self.get_esxi_profiles(patch_url)
        valid_profile = None

        for profile in profiles:
            profile_name = profile.get("Name")

            # Eliminate the 'security-only' and any that don't have tools.
            if profile_name.endswith("s-standard") or profile_name.endswith("-no-tools"):
                continue

            if profile_name:
                valid_profile = profile_name
                break

        return valid_profile

    def get_vxrail_task(self, ps_task_id):

        if platform.system() == 'VMkernel':
            esx_cmd = "vxrail task get -t {task_id}".format(task_id=ps_task_id)
            result = ESXCLI.execute(esx_cmd)

            status = result.get('status', '').strip().upper()
            logger.debug('Status: %s', status)

            return status
        else:
            raise NotImplementedError("Current system is not supported")

    def update_vxrail_firmware(self, fw_files):

        if platform.system() == 'VMkernel':
            logger.debug("Try to upgrade firmware set: %s", fw_files)

            if fw_files and len(fw_files) > 0:
                esx_cmd = "vxrail firmware upgrade -n -f " + \
                    ' -f '.join(fw_files)
                result = ESXCLI.execute(esx_cmd)

                message = result.get('message', '').strip()
                logger.debug('Message: %s', message)
                status = result.get('status', '').strip()
                logger.debug('Status: %s', status)
                ps_task_id = result.get('task', '').strip()
                logger.debug('PS Task: %s',  message)

                return ps_task_id
            return None
        else:
            raise NotImplementedError("Current system is not supported")

    @staticmethod
    def _exec_command(command, check=False):
        logger.debug("Run: {}".format(command))

        try:
            result = subprocess.run(shlex.split(command),
                                    stdin=subprocess.DEVNULL,
                                    stdout=subprocess.DEVNULL,
                                    stderr=subprocess.DEVNULL,
                                    shell=False,
                                    check=check)
            logger.debug("returncode=%d" % result.returncode)
        except subprocess.CalledProcessError as e:
            logger.exception("Error occurred during command execution")
            raise

        return result.returncode

    @staticmethod
    def _exec_command_with_output(command):
        logger.debug("Run: {}".format(command))

        try:
            result = subprocess.run(shlex.split(command),
                                    stdout=subprocess.PIPE,
                                    stderr=subprocess.STDOUT,
                                    shell=False,
                                    check=False)
            logger.debug("returncode=%d" % result.returncode)
            logger.debug("stdout=%r" % result.stdout)
        except subprocess.CalledProcessError as e:
            logger.error("Error occurred during command execution")
            return None

        return result

    def shutdown_all_vms(self):
        with HostConnection() as connection:
            connection.shutdown_all_vms()

    def remove_all_vms(self):
        with HostConnection() as connection:
            connection.remove_all_vms()

    def delete_single_vsan(self):
        with HostConnection() as connection:
            connection.delete_single_vsan()


esxutil = EsxSystemUtility()


class SystemInfo(object):

    def __init__(self):
        self._oem_vendor = None
        self._system_model = None
        self._esxi_version = None
        self._firmware_list = {}
        self._fw_model_list = []
        self._fw_nic_models = []
        self._software_vibs = {}
        self._software_components = {}

    def load(self, ignore_firmware=False):
        hw_info = esxutil.get_hardware_platform()
        if hw_info:
            self._oem_vendor, self._system_model = self._parse_platform_info(
                hw_info)

        self._esxi_version = esxutil.get_esxi_system_version().get('Version', '')

        self.reload_software_vibs()
        self.is_esxcli_support_fwupdate = self.check_esxcli_support_fwupdate()

        if not self.is_esxcli_support_fwupdate and not ignore_firmware:
            password = generate_new_password()
            esxutil.prepare_esxi_account(PSA_ACCOUNT, password)
            esxutil.ps_client = PServiceClient(password=password)

        if compare_version_string(self._esxi_version, "7.0") >= 0:
            self.reload_software_components()

        if not ignore_firmware:
            self.reload_firmware_list()

    def reload_firmware_list(self):
        if self.is_esxcli_support_fwupdate:
            fw_list = esxutil.get_firmware_list()
            self._firmware_list = fw_list
            self._fw_model_list, self._fw_nic_models = self._make_model_list(
                fw_list)

    def reload_software_vibs(self):
        self._software_vibs = esxutil.get_installed_vibs()

    def reload_software_components(self):
        self._software_components = esxutil.get_installed_components()

    def _parse_platform_info(self, hw_info):
        raw_model = hw_info.get('ProductName', '')
        raw_vendor = hw_info.get('VendorName', '')
        logger.debug("raw_model={raw_model}, raw_vendor={raw_vendor}".format(
            raw_model=raw_model, raw_vendor=raw_vendor))

        if contains_ignore_case(raw_vendor, 'QUANTA') or \
                contains_ignore_case(raw_model, 'QUANTA'):
            vendor_name = 'QUANTA'
            system_model = raw_model
        elif contains_ignore_case(raw_vendor, 'DELL') or \
                raw_model.startswith('VxRail '):
            vendor_name = 'DELL'
            system_model = raw_model
        else:
            console.invalid_vendor(raw_vendor)
            raise VxNodeUpgradeError(
                'Node upgrade failed due to invalid vendor: %s' % raw_vendor)

        logger.debug("vendor_name: {vendor_name}".format(
            vendor_name=vendor_name))
        logger.debug("system_model: {system_model}".format(
            system_model=system_model))
        return (vendor_name, system_model)

    def _make_model_list(self, fw_list):
        all_models = set()
        nic_models = set()

        for item in fw_list:
            class_id = item['id']
            model = item['model']

            if model:
                all_models.add(model)

                if class_id == 'nic':
                    nic_models.add(model)

        return list(all_models), list(nic_models)

    @property
    def oem_vendor(self):
        return self._oem_vendor

    @property
    def system_model(self):
        return self._system_model

    @property
    def esxi_version(self):
        return self._esxi_version

    @property
    def firmware_list(self):
        return self._firmware_list

    @property
    def device_model_list(self):
        return self._fw_model_list

    @property
    def nic_model_list(self):
        return self._fw_nic_models

    @property
    def software_vibs(self):
        return self._software_vibs

    @property
    def software_components(self):
        return self._software_components

    @property
    def is_ptagent_installed(self):
        if self.query_vib_version(PTA_VIB_NAME):
            return True

        return False

    #From AS, the legacy esxcli method is not supporte fwupdate
    def check_esxcli_support_fwupdate(self):

        if self._system_model and is_dell_13G_platform(self._system_model):
            logger.debug("This is 13G platform")
            return True

        if not self.is_ptagent_installed:
            return False

        ps_version = self.query_vib_version(PS_VIB_NAME)
        if ps_version and compare_version_string(ps_version,REDUCE_PTA_VERSION) < 0 :
            return True

        return False

    def query_vib_version(self, name):
        return self._software_vibs.get(name, None)

    def query_component_version(self, name):
        return self._software_components.get(name, None)

    def check_installed_vib(self, name, version, build):
        version_string = '-'.join([version, build])

        installed_version = self.query_vib_version(name)

        if installed_version == version_string:
            return True
        else:
            return False

    def check_installed_component(self, name, version):
        installed_version = self.query_component_version(name)

        if installed_version == version:
            return True
        else:
            return False

    def check_installed_firmware(self, class_id, version, models=None):
        found_versions = []

        logger.debug(
            "Check firmware package {id='%s', models=%s, version='%s'}:", class_id, models, version)

        for item in self._firmware_list:
            if not models:
                if item['id'] == class_id:
                    found_versions.append(item['version'])
            else:
                if item['id'] == class_id \
                        and item['model'] in models:
                    found_versions.append(item['version'])
        logger.debug("\tfound_versions = %s", found_versions)

        if len(found_versions) > 0:
            return all(compare_version_string(v, version) >= 0 for v in found_versions)
            # return all(v == version for v in found_versions)
        else:
            return False

    def get_bmc_version(self):
        for item in self._firmware_list:
            if item['id'] == 'bmc':
                return item['version']

        return None


class TaskListBuilder(object):

    def __init__(self, manifest, sysinfo, bundle_dir):
        self.manifest = manifest
        self.sysinfo = sysinfo
        self._bundle_dir = bundle_dir
        self._esxi_version = None
        self._system_model = None
        self._vxrail_version = None
        self._vxrail_build = None

    def _extract_args(self, element, properties=[]):
        items = {}

        for name in properties:
            logger.debug('name: %s', name)
            for iter in element.iterfind(name):
                arg_name = name.split('/')[0]
                text = iter.text or ""
                logger.debug('arg_name: %s', arg_name)
                logger.debug('iter.text: %s', text)
                if arg_name in items:
                    items[arg_name] = items[arg_name] + ';' + text.strip()
                else:
                    items[arg_name] = text.strip()

        return items

    def _parse_esxi_patch(self, element):
        task = {
            'type': "esxi_patch",
            'name': "Install ESXi VMware patch",
            'async': False,
            'visible': True,
        }

        task['install_order'] = int(element.get('InstallOrder'))
        task['args'] = self._extract_args(element, [
            'ComponentType',
            'DisplayName',
            'Version',
            'Build',
            'File',
            'Size',
            'HighestFormatVersionSupported',
        ])

        return task

    def _vlcm_bundle_info(self, file_path):
        _, ext = os.path.splitext(os.path.basename(file_path))
        is_vlcm_pkg = False

        if ext == '.zip':
            with zipfile.ZipFile(file_path, 'r') as bundle:
                filelist = bundle.namelist()
                index_url = 'index.xml'
                vendor_url = 'vendor-index.xml'
                metadata_url = 'metadata.zip'

                if index_url in filelist:
                    index_xml = ET.fromstring(bundle.read(index_url))
                    indexfile_node = index_xml.find('./vendor/indexfile')
                    if indexfile_node is not None:
                        vendor_url = indexfile_node.text

                if vendor_url in filelist:
                    vendor_xml = ET.fromstring(bundle.read(vendor_url))
                    url_node = vendor_xml.find('./metadata/url')
                    if url_node is not None:
                        metadata_url = url_node.text

                if metadata_url not in filelist:
                    raise VxNodeUpgradeError("Metadata url '%s' does not exist in the bundle %s" %
                                             (metadata_url, file_path))

                meta_zipdata = BytesIO(bundle.read(metadata_url))
                with zipfile.ZipFile(meta_zipdata, 'r') as meta_zip:
                    vmware_xml = ET.fromstring(meta_zip.read('vmware.xml'))

            name_node = vmware_xml.find('./bulletin/componentNameSpec')
            version_node = vmware_xml.find('./bulletin/componentVersionSpec')

            if (name_node is not None) and \
                (version_node is not None):
                # Careful! "is not None" must be used to test if element is found
                # Otherwise, elements with no subelements will test as False
                # See also: https://docs.python.org/3/library/xml.etree.elementtree.html#element-objects
                name = name_node.attrib['name']
                version = version_node.attrib['version']
                # Is a component bundle zip
                is_vlcm_pkg = True

        if is_vlcm_pkg:
            logger.info("Bundle %s is a vLCM component package" % file_path)
            return (name, version)
        else:
            logger.info("Bundle %s is a VIB package" % file_path)
            return None

    def _query_installed_driver_version(self, driver_id, legacy_vibs=None):
        sysinfo = self.sysinfo

        installed_version = sysinfo.query_component_version(driver_id)

        if (not installed_version) and legacy_vibs:
            for vib_name in legacy_vibs:
                vib_version = sysinfo.query_vib_version(vib_name)
                if vib_version:
                    installed_version = vib_version
                    break
        
        return installed_version

    def _is_component_type_driver(self, driver_id):
        sysinfo = self.sysinfo
        return sysinfo.query_component_version(driver_id)

    def _customize_driver_info(self, driver_id):
        payload_dir = os.path.join(self._bundle_dir, 'bundles', 'customize')
        xmlroot = self._xmlroot
        driver_info = None

        for file in glob.glob(os.path.join(payload_dir, '*.zip')):
            bundle_info = self._vlcm_bundle_info(file)
            if bundle_info \
                and bundle_info[0] == driver_id:
                driver_info = {
                    'id': bundle_info[0],
                    'version': bundle_info[1],
                    'location': "standalone",
                    'file_url': file,                        
                }
                break

        if not driver_info:
            # the specified driver not found in payload directory,
            # seek in manifest        
            for child in xmlroot.findall('Package'):
                child_type = child.find('ComponentType')
                if child_type is not None \
                        and equals_ignore_case(child_type.text, 'ESXi'):
                    esxi_group = child

            if esxi_group:
                for child in esxi_group.findall('Package'):
                    child_type = child.find('ComponentType')
                    if child_type is not None:
                        component_type = child_type.text or ""
                        if check_esxi_vib_component(component_type):
                            vib_task = self._parse_install_vib(child)
                            package_type = vib_task['package_type']
                            pkg_compname = vib_task.get('component_name')
                            pkg_compversion = vib_task.get('component_version')

                            if package_type == 'component' \
                                and pkg_compname == driver_id:
                                driver_info = {
                                    'id': pkg_compname,
                                    'version': pkg_compversion,
                                    'location': "manifest",
                                    'file_url': "",
                                }
                                break

        return driver_info

    def _parse_install_vib(self, element):
        task = {
            'type': "install_vib",
            'async': False,
            'visible': True,
            'package_type': 'vib',
        }

        task['name'] = "Install %s" % element.find('DisplayName').text
        task['install_order'] = int(element.get('InstallOrder'))
        task['args'] = self._extract_args(element, [
            'ComponentType',
            'DisplayName',
            'Version',
            'Build',
            'SystemName',
            'File',
            'Size',
            'ReplaceTargetInfo/ReplaceTarget/SystemName',
        ])

        component_type = task['args'].get('ComponentType', '')
        display_name = task['args'].get('DisplayName', '')
        if equals_ignore_case(display_name, 'VxRail VIB') or \
                equals_ignore_case(component_type, 'VXRAIL_'):
            task['args']['SystemName'] = "vmware-marvin"

        pkg_file = task['args'].get('File', '')
        file_path = os.path.join(self._bundle_dir, pkg_file)
        vlcm_bundle_info = self._vlcm_bundle_info(file_path)

        if vlcm_bundle_info:
            task['package_type'] = 'component'
            task['component_name'] = vlcm_bundle_info[0]
            task['component_version'] = vlcm_bundle_info[1]

        return task

    def _parse_update_firmware(self, element):
        task = {
            'type': "update_firmware",
            'async': True,
            'visible': True,
            'runtime_check': False,
        }

        task['name'] = "Update %s" % element.find('DisplayName').text
        task['install_order'] = int(element.get('InstallOrder'))
        task['args'] = self._extract_args(element, [
            'ComponentType',
            'DisplayName',
            'Version',
            'Build',
            'File',
            'Size',
        ])

        nic_models = self._extract_target_models(element, 'TargetNicModelInfo')
        component_models = self._extract_target_models(
            element, 'TargetComponentModelInfo')
        fw_models = nic_models + component_models
        if fw_models:
            task['args']['FirmwareModels'] = fw_models
        else:
            task['args']['FirmwareModels'] = None

        return task

    def _add_accomplish_tasks(self, task_list):
        amended_tasks = []
        is_pending = False

        accomplish_task = {
            'type': "accomplish_fwupdate",
            'name': "Accomplish firmware update jobs",
            'install_order': -1,
            'async': False,
            'visible': False,
        }

        reboot_task = {
            'type': "system_reboot",
            'name': "Reboot ESXi host",
            'install_order': -1,
            'async': False,
            'visible': True,
        }

        bmc_version = self.sysinfo.get_bmc_version()
        bmc_tasks = [t for t in task_list if 'args' in t and equals_ignore_case(
            t['args'].get('ComponentType'), 'BMC')]
        if (bmc_version and compare_version_string(bmc_version, '3.30.30.30') > 0) and len(bmc_tasks) > 1:
            skipped = bmc_tasks[0]
            logger.info("Skip an interim BMC task: %s" % skipped)
            task_list.remove(skipped)

        for task in task_list:
            if 'args' in task and equals_ignore_case(task['args'].get('ComponentType'), 'BMC'):
                if is_pending:
                    amended_tasks.append(copy.copy(accomplish_task))
                    amended_tasks.append(copy.copy(reboot_task))
                amended_tasks.append(task)
                amended_tasks.append(copy.copy(accomplish_task))
                is_pending = False
            elif task['async']:
                is_pending = True
                amended_tasks.append(task)
            elif is_pending:
                amended_tasks.append(copy.copy(accomplish_task))
                is_pending = False
                amended_tasks.append(task)
            else:
                amended_tasks.append(task)

        if is_pending:
            amended_tasks.append(copy.copy(accomplish_task))
            is_pending = False

        task_list[:] = amended_tasks

    def _add_reboot_task_fw_esxi_patch(self, task_list):
        reboot_task = {
            'type': "system_reboot",
            'name': "Reboot ESXi host",
            'install_order': -1,
            'async': False,
            'visible': True,
        }

        for task in task_list:
            index = task_list.index(task)
            # ESXi Patch install order is 100, we need to do system reboot after updated ESXi Patch
            # Insert system reboot task before install order which is greater than 100
            if task['install_order'] > 100:
                task_list.insert(index, copy.copy(reboot_task))
                break
            # Insert system reboot task at end of the list if there is no ESXi Patch task
            elif index == len(task_list) - 1:
                task_list.append(copy.copy(reboot_task))
                break

    # For Platform and PTAgent need be live install, and non-live install task should be late than them
    def _find_end_of_live_install_task(self, task_list):
        live_install_vibs=["platform-service","dellptagent"]
        insert_index = -1
        for task in task_list:
            index = task_list.index(task)
            # There may also ptagent task after OS reboot, so here we only search task before reboot OS task, install_order < 100
            if task['install_order'] < 100 and 'args' in task:
                if 'SystemName' in task['args'] and task['args']['SystemName'] in live_install_vibs:
                    insert_index = index
        return insert_index

    def _add_esxi_prehook_tasks(self, task_list, hooks):
        amend_tasks = list()

        for idx, task in enumerate(task_list):
            if task['type'] == 'esxi_patch':
                esxi_idx = idx
                break

        if esxi_idx >= 0:
            for key in hooks:
                hook_task = ESXI_PATCH_HOOK_TASKS[key]
                task_list.insert(esxi_idx, hook_task)

    def _prepend_hook_tasks(self, task_list, hooks):
        for key in hooks:
            hook_task = GENERIC_HOOK_TASKS[key]
            task_list.insert(0, hook_task)

    def _add_destroy_vsan_tasks(self, task_list):
        destroy_vsan_task = {
            'type': "destroy_vsan",
            'name': "Destroy single node VSAN",
            'install_order': -1,
            'async': False,
            'visible': True,
        }

        task_list.insert(0, copy.copy(destroy_vsan_task))

    def _insert_reduce_pta_task(self, task_list):
        reduce_pta_dependence_task = {
            'type': "reduce_ptagent_dependence",
            'name': "Reduce dependence on Dell PTAgent",
            'install_order': -1,
            'async': False,
            'visible': True,
            'time_required': 1,
        }
        # task_list.insert(0, copy.copy(reduce_pta_dependence_task))

        # Insert reduce ptagent dependence task after the first system reboot
        # to make sure platform.conf changed successfully
        insert_pos = -1
        for idx, task in enumerate(task_list):
            if task['type'] == 'system_reboot':
                insert_pos = idx + 1
                break
        
        if insert_pos >= 0:
            task_list.insert(insert_pos, copy.copy(reduce_pta_dependence_task))

    def _insert_reset_ism_task(self, task_list):
        reset_ism_task = {
            'type': "reset_ism",
            'name': "Reset iSM service configuration",
            'install_order': -1,
            'async': False,
            'visible': True,
        }

        if self.sysinfo.oem_vendor == 'DELL':
            for task in task_list:
                index = task_list.index(task)
                if 'system_reboot' == task['type']:
                    task_list.insert(index + 1, copy.copy(reset_ism_task))
                    break

    def _append_vxnode_config_task(self, task_list):
        vxnode_config_task = {
            'type': "vxnode_config",
            'name': "Change VxRail node configuration",
            'install_order': -1,
            'async': False,
            'visible': True,
        }

        task_list.append(vxnode_config_task)

    def _append_non_vlcm_task(self, task_list, post_component_tasks):
        esxi_version = self.sysinfo.esxi_version

        remove_non_vlcm_task = {
            'type': "remove_non_vlcm",
            'name': "Remove vxrail-non-vlcm VIB to enable vLCM management",
            'install_order': -1,
            'async': False,
            'visible': True,
        }


        if compare_version_string(esxi_version, "7.0") >= 0:
            task_list.append(remove_non_vlcm_task)

    def _append_runtime_reboot_task(self, task_list):
        reboot_task = {
            'type': "system_reboot",
            'name': "Reboot ESXi host",
            'install_order': -1,
            'async': False,
            'visible': True,
            'runtime_check': True,
        }

        task_list.append(copy.copy(reboot_task))

    def _add_customize_driver_tasks(self, task_list,
                                    unaligned_drivers, unaligned_driver_vibs, extra_customize_pkgs):
        for driver_id in reversed(unaligned_drivers):
            legacy_vibs = unaligned_driver_vibs.get(driver_id)

            remove_task = {
                'type': "remove_component",
                'name': "Remove component package {}".format(driver_id),
                'install_order': -1,
                'async': False,
                'visible': True,
                'package_type': 'component',
                'component_name': driver_id,
                'args': dict(),
            }

            if legacy_vibs:
                remove_task['args']['LegacyVIBs'] = legacy_vibs

            index = self._find_end_of_live_install_task(task_list)
            task_list.insert(index+1, remove_task)

        insert_pos = -1
        for idx, task in enumerate(task_list):
            if task['type'] == 'system_reboot':
                insert_pos = idx + 1
                break
        else:
            insert_pos = len(task_list)

        for payload_info in reversed(extra_customize_pkgs):
            driver_id = payload_info['id']
            file_url = payload_info['file_url']
            full_version = payload_info['version']
            version_partition = full_version.partition('-')
            short_version = version_partition[0]
            build_number = version_partition[2]

            install_task = {
                'type': "install_component",
                'name': "Install component package {}".format(driver_id),
                'install_order': -1,
                'async': False,
                'visible': True,
                'package_type': 'component',
                'component_name': driver_id,
            }
            install_task['args'] = {
                'Version': short_version,
                'Build': build_number,
                'File': file_url,
            }

            task_list.insert(insert_pos, install_task)

    def _add_deprecated_driver_tasks(self, task_list, deprecated_dirvers):
        for driver in reversed(deprecated_dirvers):
            driver_id = driver.get('id')
            legacy_vibs = driver.get('legacy_vibs')

            remove_task = {
                'type': "remove_component",
                'name': "Remove component package {}".format(driver_id),
                'install_order': -1,
                'async': False,
                'visible': True,
                'package_type': 'component',
                'component_name': driver_id,
                'args': dict(),
            }

            if legacy_vibs:
                remove_task['args']['LegacyVIBs'] = legacy_vibs

            index = self._find_end_of_live_install_task(task_list)
            task_list.insert(index+1, remove_task)

    def _extract_target_models(self, element, child_name):
        model_info = element.find(child_name)
        defined_models = []

        if model_info is not None:
            for child in model_info.findall('Model'):
                defined_models.append(child.text)

        return defined_models

    def _extract_child_value(self, element, child_name):
        child = element.find(child_name)
        if child is not None:
            return child.text
        else:
            return None

    def _parse_target_info(self, element):
        target_info = {}

        def update_target_info(key, value):
            if value:
                target_info[key] = value

        comp_element = element.find('ComponentType')
        if comp_element is not None and \
                equals_ignore_case(comp_element.text, "NIC_Firmware"):
            nic_firmware = True
        else:
            nic_firmware = False

        target_hardware = self._extract_child_value(
            element, 'TargetHardwareInfo')
        update_target_info('hardware', target_hardware)

        target_models = self._extract_target_models(element, 'TargetModelInfo')
        update_target_info('models', target_models)

        if nic_firmware:
            nic_models = self._extract_target_models(
                element, 'TargetNicModelInfo')
            update_target_info('nic_models', nic_models)

        component_models = self._extract_target_models(
            element, 'TargetComponentModelInfo')
        update_target_info('component_models', component_models)

        return target_info

    def _match_current_system(self, target_info, ignore_component=False):
        sysinfo = self.sysinfo
        matched = True

        if 'hardware' in target_info:
            oem_vendor = sysinfo.oem_vendor
            target_hardware = target_info['hardware']
            hw_match = equals_ignore_case(target_hardware, oem_vendor)
            logger.debug("hardware matched: %s", hw_match)
            matched &= hw_match

        if 'models' in target_info:
            system_model = sysinfo.system_model
            target_models = target_info['models']
            if target_models:
                model_match = operator.contains(target_models, system_model)
                logger.debug("models matched: %s", model_match)
                matched &= model_match

        if not ignore_component and 'nic_models' in target_info:
            system_fw_models = sysinfo.nic_model_list
            nic_models = target_info['nic_models']
            nic_match = False
            if nic_models:
                for model in nic_models:
                    if model in system_fw_models:
                        nic_match = True
                        break
            logger.debug("nic matched: %s", nic_match)
            matched &= nic_match

        if not ignore_component and 'component_models' in target_info:
            system_fw_models = sysinfo.device_model_list
            component_models = target_info['component_models']
            component_match = False
            if component_models:
                for model in component_models:
                    if model in system_fw_models:
                        component_match = True
                        break
            logger.debug("component matched: %s", component_match)
            matched &= component_match

        return matched

    def _filter_alternative_tasks(self, task_list, alternative_group):
        esxi_version = self.sysinfo.esxi_version

        for vib_name, alternatives in alternative_group.items():
            logger.debug("Alternative tasks found for '%s': %s",
                         vib_name, alternatives)
            if len(alternatives) > 0:
                alternatives.sort(key=lambda t: t['install_order'])
                # Select different VIB on the basis of current ESXi version
                if compare_version_string(esxi_version, "7.0") >= 0:
                    removed = alternatives[0]
                else:
                    removed = alternatives[-1]

                if removed in task_list:
                    logger.debug("Skip unwanted task: %s, type: %s" % (removed['name'], removed['package_type']))
                    task_list.remove(removed)

    def _combine_manifest_firmware_tasks(self, manifest_tasks, ps_api_fw_tasks):
        combined_tasks = []
        ps_vib_task_found = False

        for manifest_task in manifest_tasks:
            if 'args' in manifest_task.keys() and 'SystemName' in manifest_task['args'].keys():
                vib_name = manifest_task['args']['SystemName']
                if PS_VIB_NAME == vib_name:
                    ps_vib_task_found = True
                    combined_tasks.append(manifest_task)
                    for fw_task in ps_api_fw_tasks:
                        combined_tasks.append(fw_task)
                else:
                    combined_tasks.append(manifest_task)
            else:
                combined_tasks.append(manifest_task)

        if not ps_vib_task_found:
            combined_tasks = ps_api_fw_tasks
            for manifest_task in manifest_tasks:
                combined_tasks.append(manifest_task)

        return combined_tasks

    def build(self, ignore_target=False, ignore_customize_drivers=[]):
        sysinfo = self.sysinfo

        root = ET.fromstring(self.manifest)

        required_tasks = []
        manifest_tasks = []
        firmware_tasks = []

        alternative_groups = dict()
        post_component_tasks = []
        esxi_group = None
        vxrail_version = root.get("Version")
        build_id = root.get("Build")
        esxi_version = sysinfo.esxi_version
        system_model = sysinfo.system_model

        self._xmlroot = root
        self._esxi_version = esxi_version
        self._system_model = system_model
        self._vxrail_version = vxrail_version
        self._vxrail_build = build_id

        unaligned_drivers = list()
        unaligned_driver_vibs = dict()
        extra_customize_pkgs = list()
        deprecated_dirvers = list()

        if compare_version_string(vxrail_version, CUSTOMIZE_DRIVER_MIN_RELEASE) >= 0:
            for driver in CUSTOMIZE_DRIVERS:
                driver_id = driver['id']
                legacy_vibs = driver.get('legacy_vibs')

                # bypass customize driver operations according to "--bypass-customize-drivers" argument.
                if driver_id in ignore_customize_drivers:
                    continue

                installed_version = self._query_installed_driver_version(driver_id,
                                                                         legacy_vibs=legacy_vibs)
                payload_version = None
                payload_location = None
                payload_info = self._customize_driver_info(driver_id)
                if payload_info:
                    payload_version = payload_info['version']
                    payload_location = payload_info['location']
                    logger.debug("Customize driver payload: %s", payload_info)

                logger.debug("Customize driver %s: %s (installed)",
                             driver_id, installed_version)
                logger.debug("Customize driver %s: %s (required)",
                             driver_id, payload_version)

                # remove unaligned async driver on ESXi 7.0+ only
                if compare_version_string(esxi_version, "7.0") >= 0 \
                        and installed_version \
                        and is_esxi_async_driver(installed_version):
                    if not (payload_version and compare_version_string(installed_version, payload_version) <= 0):
                        logger.debug(
                            "The installed customize driver version is not same as the payload in recovery bundle.")
                        logger.debug(
                            "About to remove unaligned customize driver %s in the beginning", driver_id)
                        unaligned_drivers.append(driver_id)
                        if legacy_vibs:
                            unaligned_driver_vibs[driver_id] = legacy_vibs
                    elif payload_version and compare_version_string(installed_version, payload_version) == 0:
                        if not self._is_component_type_driver(driver_id):
                            logger.debug(
                                "Driver %s is not component type in system. Installed version is %s.",
                                driver_id, installed_version)
                            logger.debug(
                                "About to remove this VIB type driver %s in the beginning", driver_id)
                            unaligned_drivers.append(driver_id)
                            unaligned_driver_vibs[driver_id] = legacy_vibs

                if payload_version \
                        and payload_location == "standalone":
                    if (installed_version != payload_version) or (not self._is_component_type_driver(driver_id)):
                        logger.debug(
                            "The installed customize driver version is not same as the payload in recovery bundle.")
                        logger.debug(
                            "About to install the standalone customize driver %s separately", driver_id)
                        extra_customize_pkgs.append(payload_info)

            logger.info("Unaligned customize drivers: %s", unaligned_drivers)
            logger.info("Extra customize drivers: %s", extra_customize_pkgs)

        # [Eger] add Workaround for ens unsigned driver
        if compare_version_string(vxrail_version, DEPRECATED_DRIVER_MIN_RELEASE) >= 0:
            for driver in DEPRECATED_DRIVERS:
                driver_id = driver.get('id')
                legacy_vibs = driver.get('legacy_vibs')

                installed_version = self._query_installed_driver_version(
                    driver_id,
                    legacy_vibs=legacy_vibs)

                if installed_version:
                    deprecated_dirvers.append(driver)

            logger.info("Drivers wait to be removed: %s", deprecated_dirvers)

        for child in root.findall('Package'):
            child_type = child.find('ComponentType')
            if child_type is not None \
                    and equals_ignore_case(child_type.text, 'ESXi'):
                esxi_group = child
                # if current esxi match system, no need to add esxi patch to task list
                patch_version = self._extract_child_value(
                    child, 'Version').strip()
                patch_build = self._extract_child_value(child, 'Build').strip()
                system_version = esxutil.get_esxi_system_version()
                esxi_patch_task = self._parse_esxi_patch(child)
                
                if unaligned_drivers:
                    # force apply esxi patch if async driver is about to be removed
                    manifest_tasks.append(esxi_patch_task)                    
                else:
                    if system_version.get('Version', '') == patch_version \
                            and system_version.get('Build', '').endswith('-' + patch_build):
                        logger.debug('ESXi patch version is the same with current '
                                    'ESXi system version, no need to upgrade it.')
                    else:
                        manifest_tasks.append(esxi_patch_task)
                break

        if esxi_group:
            for child in esxi_group.findall('Package'):
                child_type = child.find('ComponentType')
                target_info = self._parse_target_info(child)
                logger.debug("target_info = %s", target_info)
                if not ignore_target:
                    matched = self._match_current_system(target_info)
                    machine_matched = self._match_current_system(
                        target_info, ignore_component=True)
                else:
                    matched = True
                    machine_matched = True
                logger.debug("system matched: %s", matched)

                if child_type is not None:
                    component_type = child_type.text or ""
                    if check_esxi_vib_component(component_type):
                        vib_task = self._parse_install_vib(child)
                        vib_name = vib_task['args']['SystemName']
                        vib_version = vib_task['args']['Version']
                        vib_build = vib_task['args']['Build']
                        package_type = vib_task['package_type']

                        if vib_name == PTA_VIB_NAME and not sysinfo.is_esxcli_support_fwupdate and \
                                is_dell_non_13G_platform(sysinfo.oem_vendor, sysinfo.system_model):
                            continue

                        if vib_name in FP_ALTERNATIVE_VIBS \
                                and vib_task['install_order'] < 1000:
                            if vib_name not in alternative_groups:
                                alternative_groups[vib_name] = list()
                            alternative_groups[vib_name].append(vib_task)

                        if compare_version_string(esxi_version, "7.0") < 0 and \
                            vib_task['install_order'] < 1000:
                            # ESXi 6.x
                            installed = sysinfo.check_installed_vib(
                                vib_name, vib_version, vib_build)
                            logger.debug("vib installed: %s", installed)

                            # install VIB or component on ESXi 6.x
                            if matched and not installed:
                                # VXP-32634, ESXi 7.0 U3 need to reboot immediately after patch update.
                                # In latest ESXi 7.0, we can directly use component to install, so skip the vib task on ESXi 7.0
                                # logger.debug("vib_name: %s vib_version: %s install_order: %s" %(vib_name, vib_version, str(vib_task['install_order'])))
                                if vib_task['install_order'] <= 100:
                                    manifest_tasks.append(vib_task)

                            if package_type == 'component' and \
                                vib_name not in FP_ALTERNATIVE_VIBS:
                                # convert vib to component after reboot to ESXi 7.x
                                component_task = vib_task.copy()
                                component_task['type'] = 'install_component'

                                post_component_tasks.append(component_task)
                        else:
                            # ESXi 7.0 or reboot to ESXi 7.0 from previous ESXi 6.x
                            if package_type == 'component' and \
                                    compare_version_string(vxrail_version, VLCM_MIN_RELEASE) >= 0:
                                # install component on ESXi 7.x
                                component_name = vib_task['component_name']
                                component_version = vib_task['component_version']
                                vib_task['type'] = 'install_component'

                                if component_name in unaligned_drivers:
                                    installed = False
                                else:
                                    installed = sysinfo.check_installed_component(
                                        component_name, component_version)
                                logger.debug("component installed: %s", installed)

                                if matched and not installed:
                                    # VXP-25188, Skip Dell PTAgent install task starting from 7.0.240 on 14G or newer platform
                                    if vib_name == PTA_VIB_NAME and vib_task['install_order'] > 1000 and \
                                            is_dell_non_13G_platform(self.sysinfo.oem_vendor, self.sysinfo.system_model):
                                        continue
                                    manifest_tasks.append(vib_task)
                            else:
                                # install VIB on ESXi 7.x
                                installed = sysinfo.check_installed_vib(
                                    vib_name, vib_version, vib_build)
                                logger.debug("vib installed: %s", installed)

                                if matched and not installed:
                                    manifest_tasks.append(vib_task)
                    elif check_firmware_component(component_type):
                        if not sysinfo.is_esxcli_support_fwupdate:
                            logger.warning("%s is not used for fwupdate, skip to build firmware task from manifest.xml" % PTA_VIB_NAME)
                            continue

                        if component_type.upper() not in FIRMWARE_MAPPING:
                            logger.error("Unrecognized firmware component type: %s" % component_type)
                            continue

                        fw_task = self._parse_update_firmware(child)
                        fw_class_id = FIRMWARE_MAPPING[component_type.upper()]
                        fw_version = fw_task['args']['Version']
                        fw_models = fw_task['args']['FirmwareModels']

                        installed = sysinfo.check_installed_firmware(
                            fw_class_id, fw_version, models=fw_models)
                        logger.debug("firmware installed: %s", installed)

                        if matched and not installed:
                            manifest_tasks.append(fw_task)
                        # need further runtime check on matched machine
                        elif (fw_class_id in RUNTIME_CHECK_FIRMWARE_LIST and machine_matched
                            and not installed):
                            fw_task['runtime_check'] = True
                            manifest_tasks.append(fw_task)
                    else:
                        logger.info('Unsupport component type [%s], ignore it.', component_type)

        if len(manifest_tasks) > 0:
            manifest_tasks.sort(key=lambda t: t['install_order'])
            required_tasks = manifest_tasks
            for task in manifest_tasks:
                name = task['name']
                install_type = task['type'].split('_')[-1]
                install_order = task['install_order']
                logger.debug("manifest_task: %4d %9s %s", install_order, install_type, name)

        if not sysinfo.is_esxcli_support_fwupdate and is_dell_non_13G_platform(self.sysinfo.oem_vendor, self.sysinfo.system_model):
            logger.debug("%s is not used for fwupdate, trying to get firmware upgrade tasks from PS api" % PTA_VIB_NAME)
            firmware_tasks = esxutil.ps_client.get_fw_list(self._bundle_dir + '/bundles')

            if len(firmware_tasks) > 0:
                for firmware_task in firmware_tasks:
                    logger.debug("firmware_task: %s", firmware_task['name'])
                required_tasks = self._combine_manifest_firmware_tasks(manifest_tasks, firmware_tasks)
            else:
                logger.debug("There is no firmware update tasks from PS API")
                esxutil.remove_esxi_account(PSA_ACCOUNT)

        if len(required_tasks) > 0:
            # Only for FP and later releases
            if compare_version_string(vxrail_version, "7.0") > 0:
                self._filter_alternative_tasks(required_tasks, alternative_groups)

            self._add_reboot_task_fw_esxi_patch(required_tasks)
            self._add_accomplish_tasks(required_tasks)

        if unaligned_drivers or extra_customize_pkgs:
            self._add_customize_driver_tasks(
                required_tasks, unaligned_drivers, unaligned_driver_vibs, extra_customize_pkgs)

        if deprecated_dirvers:
            self._add_deprecated_driver_tasks(
                required_tasks, deprecated_dirvers)

        # We will need to remove PTAgent on AS or later release after first system reboot on Non 13G platform
        if (compare_version_string(vxrail_version, VLCM_MIN_RELEASE) >= 0 \
            and is_dell_non_13G_platform(self.sysinfo.oem_vendor, self.sysinfo.system_model)):
            self._insert_reduce_pta_task(required_tasks)

        self._insert_reset_ism_task(required_tasks)

        # From 7.0.100, Day 0 will not create VSAN on node
        # If node upgrade to VxRail > 7.0.100, destroy vsan to make the result match re-image.
        # Note: for VxRail = 7.0.100, VxRail can handle it.
        if (compare_version_string(vxrail_version, "7.0.100") > 0
                and is_dell_non_13G_platform(self.sysinfo.oem_vendor, self.sysinfo.system_model)):
            self._add_destroy_vsan_tasks(required_tasks)

        if self.sysinfo.is_esxcli_support_fwupdate or is_dell_13G_platform(self.sysinfo.system_model):
            self._prepend_hook_tasks(required_tasks, hooks=['restore_ptagent_auth'])

        if re.match(r'^6.7.\d+$', esxi_version) \
            and compare_version_string(vxrail_version, "7.0") > 0 \
            and is_alton_amd_platform(system_model):
            self._add_esxi_prehook_tasks(required_tasks, hooks=['revert_interrupt_mapping'])

        if len(post_component_tasks) > 0:
            post_component_tasks.sort(key=lambda t: t['install_order'])
            for task in post_component_tasks:
                name = task['name']
                install_order = task['install_order']
                logger.debug("post_component_task: %4d %s", install_order, name)

            required_tasks.extend(post_component_tasks)

        if compare_version_string(vxrail_version, VLCM_MIN_RELEASE) >= 0:
            self._append_non_vlcm_task(required_tasks, post_component_tasks)

        # From 7.0.240, need to add "disk_group_type" with value "unconfigured" to vxnode.config
        # to match with Day0
        if (compare_version_string(vxrail_version, VLCM_MIN_RELEASE) >= 0 \
            and is_dell_non_13G_platform(self.sysinfo.oem_vendor, self.sysinfo.system_model)):
            self._append_vxnode_config_task(required_tasks)

        self._append_runtime_reboot_task(required_tasks)

        task_id = 1
        for task in required_tasks:
            task['id'] = task_id
            task['vxrail_version'] = vxrail_version
            task['build_id'] = build_id
            task_id += 1

        return required_tasks


class JobPermit(enum.IntEnum):
    ALL = 0
    DISABLE_ESXI = 1
    DISABLE_REBOOT = 2
    DISABLE_OTHERS = 4
    DISABLE_ALL = DISABLE_ESXI | DISABLE_REBOOT | DISABLE_OTHERS

    @classmethod
    def parse_conditions(cls, dryrun=False, reboot_only=False, skip_esxi=False):
        permit = JobPermit.ALL

        if dryrun:
            permit = JobPermit.DISABLE_ALL
        elif reboot_only:
            permit |= JobPermit.DISABLE_ESXI
            permit |= JobPermit.DISABLE_OTHERS
        elif skip_esxi:
            permit |= JobPermit.DISABLE_ESXI

        return permit


class TaskListManager(object):

    def __init__(self, bundle_dir,
                 hostname='localhost',
                 sysinfo=None,
                 permit_mode=JobPermit.ALL,
                 downgrade_mode=False,
                 basedir=SCRIPT_DIR,
                 nosigcheck=False,
                 ignore_customize_drivers=[]):
        self._basedir = basedir
        self._hostname = hostname
        self._bundle_dir = bundle_dir
        self._permit_mode = permit_mode
        self._downgrade_mode = downgrade_mode
        self._nosigcheck = nosigcheck
        self._ignore_customize_drivers = ignore_customize_drivers

        if sysinfo is not None:
            self._sysinfo = sysinfo
        else:
            self._sysinfo = SystemInfo()
            self._sysinfo.load()

        self._tasklist_file = os.path.join(
            self._basedir,
            'updates',
            "{hostname}_tasks.json".format(hostname=hostname)
        )
        self._reboot_counter_file = os.path.join(
            self._basedir,
            'updates',
            "{hostname}_reboot-counter.json".format(hostname=hostname)
        )

        self._tasks = []
        self._status_store = {}
        self._reboot_counter = 0
        self._reboot_required = False
        self._current_task_id = None
        self._pending_task_ids = []

        self._completed = False
        self._has_error = False
        self._await_restart = False
        self._restart_mode = None  # TODO: implement enumerate modes

    def get_task_data_dir(self):
        data_dir = os.path.dirname(self._tasklist_file)
        return data_dir

    def delete_task_data(self):
        # delete updates folder
        logger.debug('Try to clear task data')
        updates_dir = os.path.join(self._basedir, 'updates')
        shutil.rmtree(updates_dir, ignore_errors=True)
        self._tasks.clear()
        self._status_store.clear()
        self._current_task_id = None
        self._pending_task_ids.clear()
        self._completed = False
        self._has_error = False
        self._await_restart = False
        self._restart_mode = None

    def _get_task_from_ids(self, ids):
        results = []

        for task in self._tasks:
            if task['id'] in ids:
                results.append(task)

        return results

    def _next_task(self):
        current_idx = -1

        for idx, task in enumerate(self._tasks):
            if task['id'] == self._current_task_id:
                current_idx = idx
                break
        else:
            raise TaskListException("Current task id '%s' is invalid" %
                                    self._current_task_id)

        next_idx = current_idx + 1
        if next_idx < len(self._tasks):
            next_task = self._tasks[next_idx]
            self._current_task_id = next_task['id']
        else:
            self._completed = True
            self._current_task_id = None

    def _read_manifest_xml(self):
        manifest_path = os.path.join(self._bundle_dir, MANIFEST_FILE)
        xml = None

        if os.path.isfile(manifest_path):
            with open(manifest_path, 'r') as fp:
                xml = fp.read()
        else:
            raise TaskListException(
                "Manifest file not found: %s" % manifest_path)

        return xml

    def generate(self, ignore_target=False):
        manifest_xml = self._read_manifest_xml()

        builder = TaskListBuilder(manifest_xml, self._sysinfo, self._bundle_dir)
        self._tasks = builder.build(ignore_target=ignore_target,
                                    ignore_customize_drivers=self._ignore_customize_drivers)

        if len(self._tasks) > 0:
            first_task = self._tasks[0]
            self._current_task_id = first_task['id']

        for task in self._tasks:
            tid = task['id']
            self._status_store[tid] = TaskStateInfo()

    def _get_task_status_file(self, task_id):
        data_dir = self.get_task_data_dir()

        filename = "{hostname}_task-{id}.stat".format(
            hostname=self._hostname, id=task_id)

        return os.path.join(data_dir, filename)

    def _load_task_status(self, task_id):
        task_filepath = self._get_task_status_file(task_id)

        state_info = TaskStateInfo()

        if os.path.isfile(task_filepath):
            with open(task_filepath, 'r') as fp:
                raw_data = fp.readline()
            state_info = TaskStateInfo.parse(raw_data)

        return state_info

    def _save_task_status(self, task_id, **kwargs):
        task_filepath = self._get_task_status_file(task_id)
        tmpfile = task_filepath + ".tmp"
        state_info = self._status_store[task_id]
        state_info.update(**kwargs)

        # make sure the status file is updated atomically
        # see https://stackoverflow.com/questions/2333872/atomic-writing-to-file-with-python/2333979
        fp = open(tmpfile, 'w')
        fp.write(state_info.dumps())
        fp.flush()
        os.fsync(fp.fileno())
        fp.close()
        os.rename(tmpfile, task_filepath)

    def load(self):
        catalog_file = self._tasklist_file
        reboot_file = self._reboot_counter_file

        # load task list file and task status files
        if os.path.isfile(catalog_file):
            with open(catalog_file, 'r') as fp:
                payload = json.load(fp)
            self._tasks = payload.get('tasks', [])
            self._status_store = {}
            self._pending_task_ids = []

            current_found = False
            current_status = None
            for task in self._tasks:
                task_id = task['id']

                status_info = self._load_task_status(task_id)
                status_code = status_info.status

                if not current_found:
                    if status_code not in [TaskStatus.Completed, TaskStatus.Canceled]:
                        self._current_task_id = task_id
                        current_found = True
                        current_status = status_code

                self._status_store[task_id] = status_info

            if not current_found:
                self._completed = True
            elif current_status is TaskStatus.Failed:
                self._has_error = True

        if os.path.isfile(reboot_file):
            with open(reboot_file, 'r') as fp:
                raw_data = fp.read().strip()

            if raw_data and raw_data.isdecimal():
                self._reboot_counter = int(raw_data)
            else:
                self._reboot_counter = 0
            logger.debug("Loading reboot_counter: %d" % self._reboot_counter)

    def save(self):
        catalog_file = self._tasklist_file
        tmpfile = catalog_file + ".tmp"
        data_dir = os.path.dirname(catalog_file)

        payload = {
            'tasks': self._tasks
        }

        if os.path.exists(data_dir):
            shutil.rmtree(data_dir, ignore_errors=True)
        os.makedirs(data_dir)

        # make sure the task catalog file is updated atomically
        # see https://stackoverflow.com/questions/2333872/atomic-writing-to-file-with-python/2333979
        fp = open(tmpfile, 'w')
        json.dump(payload, fp, indent=4)
        fp.flush()
        os.fsync(fp.fileno())
        fp.close()
        os.rename(tmpfile, catalog_file)

        self.save_reboot_counter()

    def save_reboot_counter(self):
        reboot_filepath = self._reboot_counter_file
        tmpfile = reboot_filepath + ".tmp"
        raw_data = "%d" % self._reboot_counter

        # make sure the status file is updated atomically
        # see https://stackoverflow.com/questions/2333872/atomic-writing-to-file-with-python/2333979
        fp = open(tmpfile, 'w')
        fp.write(raw_data)
        fp.flush()
        os.fsync(fp.fileno())
        fp.close()
        os.rename(tmpfile, reboot_filepath)

    def _do_system_reboot(self):
        try:
            esxutil.system_reboot()
        except Exception as e:
            raise UpdateJobError(e)

    def _do_ism_reset(self):
        try:
            esxutil.reset_ism_service()
        except Exception as e:
            raise UpdateJobError(e)

    def _do_destroy_vsan(self):
        try:
            esxutil.destroy_node_vsan()
        except Exception as e:
            raise UpdateJobError(e)

    def _do_revert_interrupt_mapping(self):
        try:
            esxutil.set_kernel_setting('iovDisableIR', 'FALSE')
        except Exception as e:
            raise UpdateJobError(e)

    def _do_restore_ptagent_auth(self):
        try:
            esxutil.enable_ptagent_auth()
        except Exception as e:
            raise UpdateJobError(e)

    def _do_esxi_patch(self, profile_name, patch_url, conflict_vibs=None):
        sysinfo = self._sysinfo

        reboot_required = False

        try:
            if conflict_vibs:
                for vib in conflict_vibs:
                    vib_name = vib['name']
                    relation = vib.get('relation')
                    target_version = vib.get('version')

                    installed_version = sysinfo.query_vib_version(vib_name)

                    if installed_version:
                        # no version constraint
                        if not relation:
                            esxutil.remove_software_vib(vib_name)
                        elif target_version:
                            version_cmp = compare_version_string(
                                installed_version, target_version)
                            if relation == '=' and version_cmp == 0:
                                esxutil.remove_software_vib(vib_name)
                            elif relation == '<' and version_cmp < 0:
                                esxutil.remove_software_vib(vib_name)
                            elif relation == '<=' and version_cmp <= 0:
                                esxutil.remove_software_vib(vib_name)
                            elif relation == '>=' and version_cmp >= 0:
                                esxutil.remove_software_vib(vib_name)
                            elif relation == '>' and version_cmp > 0:
                                esxutil.remove_software_vib(vib_name)
                            elif relation == 'like' and target_version in installed_version:
                                esxutil.remove_software_vib(vib_name)
                            else:
                                logger.info("No matched constraints, skip removing %s",
                                            vib_name)
                        else:
                            logger.warn(
                                "Constraint requires a valid version value")
                    else:
                        logger.info("No such vib '%s' installed, skip removing",
                                    vib_name)

            installable = esxutil.validate_esxi_patch(profile_name, patch_url)
            if installable:
                reboot_required = esxutil.update_esxi_patch(profile_name, patch_url,
                                          nosigcheck=self._nosigcheck)
            else:
                logger.warning(
                    "Nothing need to be updated in ESXi patch %s" % profile_name)

            if reboot_required:
                self._reboot_required = True

        except Exception as e:
            # Keep the same logic with LCM
            # if exception is throw when executing the command - Failed
            # if returnCode != 0 - Failed
            # (returnCode !=0, ESXCLI.execute will throw exception)
            raise UpdateJobError(e)

    def _do_wait_for_pservice(self):
        expiry = time.time() + PSERVICE_INIT_TIMEOUT

        started = esxutil.get_pservice_status()
        while expiry > time.time() and not started:
            time.sleep(30)
            started = esxutil.get_pservice_status()

            if started:
                logger.info(
                    "The updated Platform Service is now ready!")
                break
            else:
                logger.warning(
                    "The updated Platform Service is not ready ...")

        if not started:
            raise UpdateJobError(
                "Timed out waiting for Platform Service initialization!")

    def _do_install_vib(self, vib_url, system_name=None, replace_target=None, as_vlcm_pkg=False):
        sysinfo = self._sysinfo

        reboot_required = False

        try:
            if replace_target:
                try:
                    # about to remove the obsolete target vibs
                    obsolete_vibs = replace_target.split(';')
                    logger.info('Try to remove obsolete target VIBs ...')
                    for vibname in obsolete_vibs:
                        if sysinfo.query_vib_version(vibname):
                            reboot_required = esxutil.remove_software_vib(vibname)
                        else:
                            logger.info("No such vib '%s' installed, skip removing",
                                        vibname)
                    logger.info('All obsolete target VIBs have been removed.')
                except EsxCLIError as e:
                    if 'NoMatchError' not in str(e):
                        raise

            if as_vlcm_pkg:
                reboot_required = esxutil.apply_software_component(vib_url,
                                                 nosigcheck=self._nosigcheck)
            elif system_name:
                if system_name in sysinfo.software_vibs \
                        and (not self._downgrade_mode):
                    # VIB already installed, use 'software vib update'
                    reboot_required = esxutil.update_software_vib(vib_url,
                                                nosigcheck=self._nosigcheck)
                else:
                    # VIB not installed, use 'software vib install'
                    reboot_required = esxutil.install_software_vib(vib_url,
                                                nosigcheck=self._nosigcheck)

            if reboot_required:
                self._reboot_required = True

            # post-installation steps
            if system_name:
                if system_name == PTA_VIB_NAME:
                    esxutil.disable_storage_scan_for_ptagent_service()
                    esxutil.start_ptagent_service()
                elif system_name == PS_VIB_NAME:
                    self._do_wait_for_pservice()
        except UpdateJobError:
            raise
        except Exception as e:
            # Keep the same logic with LCM
            # if exception is throw when executing the command - Failed
            # if returnCode != 0 - Failed
            # (returnCode !=0, ESXCLI.execute will throw exception)
            raise UpdateJobError(e)

    def _do_remove_non_vlcm(self):
        sysinfo = self._sysinfo

        try:
            if sysinfo.query_vib_version('vxrail-non-vlcm'):
                esxutil.remove_software_vib('vxrail-non-vlcm', live_install=True)
        except UpdateJobError:
            raise
        except Exception as e:
            # Keep the same logic with LCM
            # if exception is throw when executing the command - Failed
            # if returnCode != 0 - Failed
            # (returnCode !=0, ESXCLI.execute will throw exception)
            raise UpdateJobError(e)

    def _do_remove_component(self, component_name, legacy_vibs=None):
        sysinfo = self._sysinfo

        try:
            if sysinfo.query_component_version(component_name):
                esxutil.remove_software_component(component_name)
            elif legacy_vibs:
                for vib_name in legacy_vibs:
                    if sysinfo.query_vib_version(vib_name):
                        esxutil.remove_software_vib(vib_name)
        except UpdateJobError:
            raise
        except Exception as e:
            # Keep the same logic with LCM
            # if exception is throw when executing the command - Failed
            # if returnCode != 0 - Failed
            # (returnCode !=0, ESXCLI.execute will throw exception)
            raise UpdateJobError(e)

    def _do_update_vxrail_version(self, vxrail_version, build_id):

        new_vxrail_version = vxrail_version + '-' + build_id

        element_name = 'version'
        metadata_file = os.path.join(self._basedir, METADATA_FILE_NAME)
        logger.debug("trying to update vxrail version to %s" % new_vxrail_version)

        try:
            if os.path.isfile(metadata_file):
                tree = ET.parse(metadata_file)
                root = tree.getroot()
                version = root.find(element_name)
                version.text = new_vxrail_version
                tree.write(metadata_file)
            else:
                logger.warning("metadata file: '%s' does not exist" % metadata_file)

        except UpdateJobError:
            raise
        except Exception as e:
            # Keep the same logic with LCM
            # if exception is throw when executing the command - Failed
            # if returnCode != 0 - Failed
            # (returnCode !=0, ESXCLI.execute will throw exception)
            raise UpdateJobError(e)

    def _do_change_diskgroup_type(self):
        vxnode_config_dir = os.path.join(self._basedir, VXNODE_CONFIG_DIR_NAME)
        vxnode_config_file = os.path.join(vxnode_config_dir, VXNODE_CONFIG_FILE_NAME)

        vxnode_config = {}

        try:
            if os.path.exists(vxnode_config_dir):
                if os.path.isfile(vxnode_config_file):
                    logger.debug("vxnode config file: '%s exist, read and then add diskgroup type" % vxnode_config_file)
                    with open(vxnode_config_file, 'r') as fp:
                        vxnode_config = json.load(fp)
            else:
                os.makedirs(vxnode_config_dir)
                logger.debug("created vxnode config directory: %s" % vxnode_config_dir)

            f_obj = open(vxnode_config_file, 'w')
            vxnode_config["disk_group_type"] = "unconfigured"
            f_obj.write(json.dumps(vxnode_config, indent=4, sort_keys=True))
            f_obj.flush()
            os.fsync(f_obj.fileno())
            f_obj.close()

        except UpdateJobError:
            raise
        except Exception as e:
            # Keep the same logic with LCM
            # if exception is throw when executing the command - Failed
            # if returnCode != 0 - Failed
            # (returnCode !=0, ESXCLI.execute will throw exception)
            raise UpdateJobError(e)

    def _do_platform_config_change(self):
        platform_conf_file = '/etc/config/vxrail/platform.conf'

        try:
            if os.path.exists(platform_conf_file):
                do_change = False
                conf = configparser.ConfigParser()
                conf.read(platform_conf_file, encoding="utf-8")
                sections = conf.sections()

                if 'general' in sections:
                    if conf.has_option('general', 'agent_backend'):
                        if not 'none' == str(conf.get('general', 'agent_backend')):
                            do_change = True
                    else:
                        logger.debug(
                            "option name: agent_backend does not exist.")
                        do_change = True
                else:
                    logger.debug("section name: general does not exist.")

                if do_change:
                    conf.set('general', 'agent_backend', 'none')
                    conf.write(open(platform_conf_file, 'w'))
                    logger.debug("done for write to platform.conf")
            else:
                logger.debug("file: '%s' does not exist." % platform_conf_file)

        except UpdateJobError:
            raise
        except Exception as e:
            # Keep the same logic with LCM
            # if exception is throw when executing the command - Failed
            # if returnCode != 0 - Failed
            # (returnCode !=0, ESXCLI.execute will throw exception)
            raise UpdateJobError(e)

    def _do_reduce_ptagent_dependence(self):
        sysinfo = self._sysinfo

        try:
            if sysinfo.query_vib_version(PTA_VIB_NAME):
                logger.debug("dellptagent found, trying to set agent_backend=none to platform.conf and then remove it")
                self._do_platform_config_change()
                esxutil.remove_software_vib(PTA_VIB_NAME, live_install=True)
            else:
                logger.debug("dellptagent not found, trying to set agent_backend=none to platform.conf")
                self._do_platform_config_change()
        except UpdateJobError:
            raise
        except Exception as e:
            # Keep the same logic with LCM
            # if exception is throw when executing the command - Failed
            # if returnCode != 0 - Failed
            # (returnCode !=0, ESXCLI.execute will throw exception)
            raise UpdateJobError(e)


    def _do_accomplish_fwupdate(self, task):
        task_id = task['id']

        def _psjob_is_running(status):
            if status not in ['COMPLETED', "ERROR"]:
                return True
            else:
                return False

        try:
            fw_list = []
            processing_items = copy.copy(self.pending_tasks)
            found_psjob = False
            ps_task_id = self._status_store[task_id].ps_job

            if ps_task_id:
                try:
                    if self._sysinfo.is_esxcli_support_fwupdate:
                        status = esxutil.get_vxrail_task(ps_task_id)
                    else:
                        status = esxutil.ps_client.get_task_status(ps_task_id)

                    if status:
                        found_psjob = True
                    else:
                        ps_task_id = ''
                except EsxCLIError as e:
                    logger.error(e, exc_info=True)
                    ps_task_id = ''

            if not found_psjob:
                for fw_task in processing_items:
                    fw_url = os.path.join(
                        self._bundle_dir, fw_task['args']['File'])
                    fw_list.append(fw_url)

                if not fw_list:
                    logger.warning("No pending firmware tasks!")
                    self._pending_task_ids = []
                    return []

                # schedule all fw upgrade
                if self._sysinfo.is_esxcli_support_fwupdate:
                    ps_task_id = esxutil.update_vxrail_firmware(fw_list)
                else:
                    ps_task_id = esxutil.ps_client.update_firmware(fw_list)

                if not ps_task_id:
                    raise UpdateJobError(
                        'Platform Service firmware upgrade task ID is empty')
                # update ps_task_id to accomplish_fwupdate job
                self._save_task_status(task_id, ps_job=ps_task_id)

            # check ps task status
            expiry = time.time() + FIRMWARE_UPDATE_TIMEOUT

            if self._sysinfo.is_esxcli_support_fwupdate:
                status = esxutil.get_vxrail_task(ps_task_id)
            else:
                status = esxutil.ps_client.get_task_status(ps_task_id)

            while expiry > time.time() and _psjob_is_running(status):
                time.sleep(30)
                if self._sysinfo.is_esxcli_support_fwupdate:
                    status = esxutil.get_vxrail_task(ps_task_id)
                else:
                    status = esxutil.ps_client.get_task_status(ps_task_id)
                logger.debug('Checking PS job status: %s', status)
                if not _psjob_is_running(status):
                    break

            if _psjob_is_running(status):
                raise UpdateJobError(
                    'Platform Service firmware task timed out!')
            elif status == 'ERROR':
                raise UpdateJobError(
                    "Firmware upgrade failed via Platform Service!")

            self._pending_task_ids = []

            esxutil.remove_esxi_account(PSA_ACCOUNT)

            return processing_items
        except UpdateJobError:
            raise
        except Exception as e:
            # Keep the same logic with LCM
            # if exception is throw when executing the command - Failed
            # if returnCode != 0 - Failed
            # (returnCode !=0, ESXCLI.execute will throw exception)
            raise UpdateJobError(e)

    def _execute_task(self, task):
        permit_mode = self._permit_mode
        task_type = task['type']
        task_id = task['id']
        forward = True

        try:
            if task_type == 'system_reboot':
                runtime_check = task.get('runtime_check', False)
                reboot_required = self._reboot_required
                if (permit_mode & JobPermit.DISABLE_REBOOT) or \
                    (runtime_check and not reboot_required):
                    self._task_cancelled(task)
                else:
                    self._task_started(task)
                    console.system_reboot(task)
                    self._task_await_restart(task)
                    self._do_system_reboot()
                    forward = False
            elif task_type == 'esxi_patch':
                if permit_mode & JobPermit.DISABLE_ESXI:
                    self._task_cancelled(task)
                else:
                    self._task_started(task)
                    # Extract arguments from task
                    patch_url = os.path.join(
                        self._bundle_dir, task['args']['File'])
                    vxrail_version = task['vxrail_version']
                    profile_name = esxutil.get_valid_image_profile(patch_url)

                    if compare_version_string(vxrail_version, "7.0") >= 0:
                        self._do_esxi_patch(profile_name, patch_url,
                                            conflict_vibs=CROWNHILL_CONFLICT_VIBS)
                    else:
                        self._do_esxi_patch(profile_name, patch_url)
                    self._refresh_software_pkgs()
                    self._task_completed(task)
            elif task_type == 'install_vib':
                if permit_mode & JobPermit.DISABLE_OTHERS:
                    self._task_cancelled(task)
                else:
                    self._task_started(task)
                    vib_system_name = task['args']['SystemName']
                    replace_target = task['args'].get(
                        'ReplaceTargetInfo', None)
                    vib_url = os.path.join(
                        self._bundle_dir, task['args']['File'])
                    self._do_install_vib(
                        vib_url,
                        system_name=vib_system_name,
                        replace_target=replace_target)
                    self._refresh_software_pkgs()
                    self._task_completed(task)
            elif task_type == 'install_component':
                if permit_mode & JobPermit.DISABLE_OTHERS:
                    self._task_cancelled(task)
                else:
                    self._task_started(task)
                    vib_system_name = task['args'].get(
                        'SystemName', None)
                    replace_target = task['args'].get(
                        'ReplaceTargetInfo', None)
                    pkg_url = os.path.join(
                        self._bundle_dir, task['args']['File'])
                    self._do_install_vib(
                        pkg_url,
                        system_name=vib_system_name,
                        replace_target=replace_target,
                        as_vlcm_pkg=True)
                    self._refresh_software_pkgs()
                    self._task_completed(task)
            elif task_type == 'update_firmware':
                runtime_check = task.get('runtime_check', False)
                if permit_mode & JobPermit.DISABLE_OTHERS:
                    self._task_cancelled(task)
                elif runtime_check and self._sysinfo.is_esxcli_support_fwupdate:
                    self._do_wait_for_pservice()
                    self._refresh_firmware_list()

                    fw_class_id = FIRMWARE_MAPPING[
                        task['args']['ComponentType'].upper()]
                    fw_version = task['args']['Version']
                    fw_models = task['args']['FirmwareModels']
                    installed = self._sysinfo.check_installed_firmware(
                        fw_class_id, fw_version, models=fw_models)
                    if fw_models:
                        matched = any(fw['id'] == fw_class_id and fw['model'] in fw_models
                                      for fw in self._sysinfo.firmware_list)
                    else:
                        matched = any(fw['id'] == fw_class_id
                                      for fw in self._sysinfo.firmware_list)

                    # do update if device exists and firmware version is not equal
                    if matched and not installed:
                        self._task_started(task)
                        self._pending_task_ids.append(task_id)
                        self._task_scheduled(task)
                    else:
                        self._task_cancelled(task)
                else:
                    self._task_started(task)
                    self._pending_task_ids.append(task_id)
                    self._task_scheduled(task)
            elif task_type == 'accomplish_fwupdate':
                if permit_mode & JobPermit.DISABLE_OTHERS:
                    self._task_cancelled(task)
                else:
                    self._task_started(task)
                    self._do_wait_for_pservice()
                    related_jobs = self._do_accomplish_fwupdate(task)
                    for job in related_jobs:
                        self._task_completed(job)
                    self._task_completed(task)
            elif task_type == 'reset_ism':
                if permit_mode & JobPermit.DISABLE_OTHERS:
                    self._task_cancelled(task)
                else:
                    self._task_started(task)
                    self._do_ism_reset()
                    self._task_completed(task)
            elif task_type == 'destroy_vsan':
                if permit_mode & JobPermit.DISABLE_OTHERS:
                    self._task_cancelled(task)
                else:
                    self._task_started(task)
                    self._do_destroy_vsan()
                    self._task_completed(task)
            elif task_type == 'revert_interrupt_mapping':
                if permit_mode & JobPermit.DISABLE_OTHERS:
                    self._task_cancelled(task)
                else:
                    self._task_started(task)
                    self._do_revert_interrupt_mapping()
                    self._task_completed(task)
            elif task_type == 'restore_ptagent_auth':
                if permit_mode & JobPermit.DISABLE_OTHERS:
                    self._task_cancelled(task)
                else:
                    self._task_started(task)
                    self._do_restore_ptagent_auth()
                    self._task_completed(task)
            elif task_type == 'vxnode_config':
                if permit_mode & JobPermit.DISABLE_OTHERS:
                    self._task_cancelled(task)
                else:
                    self._task_started(task)
                    self._do_change_diskgroup_type()
                    self._do_update_vxrail_version(task['vxrail_version'], task['build_id'])
                    self._task_completed(task)
            elif task_type == 'remove_non_vlcm':
                if permit_mode & JobPermit.DISABLE_OTHERS:
                    self._task_cancelled(task)
                else:
                    self._task_started(task)
                    self._do_remove_non_vlcm()
                    self._task_completed(task)
            elif task_type == 'remove_component':
                if permit_mode & JobPermit.DISABLE_OTHERS:
                    self._task_cancelled(task)
                else:
                    self._task_started(task)
                    component_name = task['component_name']
                    legacy_vibs = task['args'].get('LegacyVIBs')
                    self._do_remove_component(
                        component_name, legacy_vibs=legacy_vibs)
                    self._task_completed(task)
            elif task_type == 'reduce_ptagent_dependence':
                if permit_mode & JobPermit.DISABLE_OTHERS:
                    self._task_cancelled(task)
                else:
                    self._task_started(task)
                    self._do_reduce_ptagent_dependence()
                    self._task_completed(task)
            else:
                raise NotImplementedError(
                    "Unsupported task type '%s'" % task_type)
        except UpdateJobError as e:
            logger.error(e, exc_info=True)
            self._task_failed(task)
            for job in self.pending_tasks:
                self._task_failed(job)
            self._pending_task_ids = []
            return False

        return forward

    def _task_started(self, task):
        task_id = task['id']
        self._save_task_status(task_id,
                               status=TaskStatus.Running,
                               start_time=time.time())
        console.job_started(task)

    def _task_completed(self, task):
        task_id = task['id']
        self._save_task_status(task_id,
                               status=TaskStatus.Completed,
                               end_time=time.time())
        console.job_completed(task)

    def _task_cancelled(self, task):
        task_id = task['id']
        self._save_task_status(task_id,
                               status=TaskStatus.Canceled,
                               end_time=time.time())
        console.job_cancelled(task)

    def _task_scheduled(self, task):
        task_id = task['id']
        self._save_task_status(task_id,
                               status=TaskStatus.Scheduled)

    def _task_await_restart(self, task):
        task_id = task['id']
        self._save_task_status(task_id,
                               status=TaskStatus.AwaitRestart)
        self._await_restart = True

    def _task_failed(self, task):
        task_id = task['id']
        self._save_task_status(task_id,
                               status=TaskStatus.Failed,
                               end_time=time.time())
        self._has_error = True
        console.job_failed(task)

    def _refresh_firmware_list(self):
        self._sysinfo.reload_firmware_list()

    def _refresh_software_pkgs(self):
        esxi_version = self._sysinfo.esxi_version

        if compare_version_string(esxi_version, "7.0") >= 0:
            self._sysinfo.reload_software_components()

        self._sysinfo.reload_software_vibs()

    def run_current_task(self):
        current_task = self.current_task
        status_code = self.current_status
        sysinfo = self._sysinfo

        if current_task is None:
            raise TaskListException("No tasks available to run")

        task_id = self._current_task_id
        state_info = self._status_store[task_id]
        is_async = current_task['async']

        forward = False

        if status_code is TaskStatus.Completed:
            self._task_completed(current_task)
            forward = True
        elif status_code is TaskStatus.Canceled:
            self._task_cancelled(current_task)
            forward = True
        elif status_code is TaskStatus.Failed:
            self._task_failed(current_task)
            forward = False
        elif status_code is TaskStatus.AwaitRestart:
            now_time = time.time()
            start_time = state_info.start_time
            uptime = esxutil.get_system_uptime()

            logger.debug("Determine whether reboot is completed:")
            logger.debug("now_time={now_time}, start_time={start_time}, uptime={uptime}".format(
                now_time=now_time, start_time=start_time, uptime=uptime))

            if (now_time - start_time) > uptime:
                self._reboot_counter += 1
                self.save_reboot_counter()
                self._task_completed(current_task)
                forward = True
            else:
                console.system_reboot(current_task)
                self._task_await_restart(current_task)
                self._do_system_reboot()
                forward = False
        elif status_code in [TaskStatus.Scheduled, TaskStatus.Running]:
            if is_async:
                # check firmware version
                fw_class_id = FIRMWARE_MAPPING[current_task['args']
                                               ['ComponentType'].upper()]
                fw_version = current_task['args']['Version']
                fw_models = current_task['args']['FirmwareModels']

                if sysinfo.check_installed_firmware(fw_class_id, fw_version, models=fw_models):
                    # firmware upgraded successfully
                    self._task_completed(current_task)
                else:
                    # not scheduled
                    self._pending_task_ids.append(task_id)
                forward = True
            else:
                forward = self._execute_task(current_task)
        elif status_code is TaskStatus.NotStarted:
            forward = self._execute_task(current_task)
        else:
            raise TaskListException(
                "Invalid task status code: {}".format(status_code))

        if forward:
            self._next_task()

        return forward

    @property
    def catalog_exists(self):
        return os.path.exists(self._tasklist_file)

    @property
    def tasks(self):
        return self._tasks

    @property
    def reboot_counter(self):
        return self._reboot_counter

    @property
    def current_task(self):
        if self._current_task_id:
            results = self._get_task_from_ids([self._current_task_id])
            if len(results) > 0:
                return results[0]

        return None

    @property
    def current_status(self):
        return self.get_task_status(self._current_task_id)

    @property
    def pending_tasks(self):
        return self._get_task_from_ids(self._pending_task_ids)

    @property
    def completed(self):
        return self._completed

    @property
    def await_restart(self):
        return self._await_restart

    @property
    def has_error(self):
        return self._has_error

    def get_task_status(self, task_id):
        if task_id is not None:
            state_info = self._status_store[task_id]
            return state_info.status
        else:
            return None


class RecoveryBundleManager(object):

    def __init__(self, bundle_path="", basedir=SCRIPT_DIR):
        self._basedir = basedir
        self.bundle_path = bundle_path
        self._archive_exists = False
        self._content_exists = False

    def get_bundle_data_dir(self):
        if self.release:
            return os.path.join(self._basedir, RECOVERY_DIR, self.release)
        else:
            return None

    def delete_bundle_data(self):
        logger.debug('Try to clear bundle data')
        extract_dir = self.get_bundle_data_dir()
        if extract_dir and os.path.exists(extract_dir):
            shutil.rmtree(extract_dir, ignore_errors=True)
            self._content_exists = False

    def _scan_determined_recovery_bundle(self):
        pkg_file = os.path.basename(self.bundle_path)

        if os.path.isfile(self.bundle_path):
            pattern = re.compile(r'^recoveryBundle-(.+).zip$')
            result = re.match(pattern, pkg_file)
            if not result:
                raise VxNodeUpgradeError(
                    "Unrecoginized recovery bundle '%s'" % pkg_file)

            self.release = result.group(1)
            self._archive_exists = True
            return True

        return False

    def _scan_latest_recovery_bundle(self):
        pattern = re.compile(r'^recoveryBundle-(.+).zip$')
        found_release = None
        found_bundle = None
        for pkg_file in os.listdir(self._basedir):
            result = re.match(pattern, pkg_file)
            if result:
                pkg_release = result.group(1)
                if found_bundle and found_release:
                    if compare_version_string(pkg_release, found_release) > 0:
                        found_bundle = os.path.join(self._basedir, pkg_file)
                        found_release = pkg_release
                else:
                    found_bundle = os.path.join(self._basedir, pkg_file)
                    found_release = pkg_release

        if found_bundle:
            self.bundle_path = found_bundle
            self.release = found_release
            self._archive_exists = True
            return True

        return False

    def _scan_content(self):
        extract_dir = self.get_bundle_data_dir()
        manifest_path = os.path.join(extract_dir, MANIFEST_FILE)
        bundles_dir = os.path.join(extract_dir, 'bundles')

        if os.path.isfile(manifest_path) and os.path.isdir(bundles_dir):
            if os.listdir(bundles_dir):
                self._content_exists = True
                return True

        return False

    def scan(self):
        found = False

        if self.bundle_path:
            found = self._scan_determined_recovery_bundle()
        else:
            found = self._scan_latest_recovery_bundle()

        if found:
            self._scan_content()

    @property
    def archive_exists(self):
        logger.debug("Bundle archive exists = %s" % self._archive_exists)
        return self._archive_exists

    @property
    def content_exists(self):
        logger.debug("Bundle content exists = %s" % self._content_exists)
        return self._content_exists

    def extract_bundle(self, keep=True, force=False):
        bundle_path = self.bundle_path
        extract_dir = self.get_bundle_data_dir()

        if force and extract_dir and os.path.exists(extract_dir):
            shutil.rmtree(extract_dir, ignore_errors=True)
            self._content_exists = False

        if self.archive_exists:
            if os.path.exists(extract_dir):
                raise VxNodeUpgradeError(
                    "Recovery bundle directory '%s' already exists" % extract_dir)

            if os.path.isfile(bundle_path):
                os.makedirs(extract_dir)

                bundle = zipfile.ZipFile(bundle_path, 'r')
                bundle.extractall(extract_dir)
                bundle.close()
                self._scan_content()

                if not keep:
                    os.remove(bundle_path)
            else:
                raise VxNodeUpgradeError(
                    "Recovery bundle '%s' not found" % bundle_path)
        else:
            raise VxNodeUpgradeError("No available recovery bundle")


class ConsoleWriter(object):

    def __init__(self, verbose=True):
        self.has_blank = True
        self.finished = False
        self.verbose = verbose

    def _insert_blank(self):
        if not self.has_blank:
            print()
            self.has_blank = True

    def _print(self, message, visible=True):
        logger.info(message)
        if visible:
            print(message)

    def show_initializing(self):
        self._print(
            "System services initializing, please wait ...", self.verbose)
        self.has_blank = False

    def show_hostname(self, nodename):
        self._print("Hostname: %s" % nodename, self.verbose)
        self.has_blank = False

    def show_recovery_bundle(self, bundle_path):
        self._print("Recovery bundle: %s" % bundle_path, self.verbose)
        self.has_blank = False

    def show_reloading(self, data_dir):
        self._print("Reloading upgrade tasks from %s/ ..." %
                    data_dir, self.verbose)
        self.has_blank = False

    def show_past_failure(self):
        self._print("Past failure detected!", self.verbose)
        self.has_blank = False

    def show_retry(self):
        self._print("Attempt to retry node upgrade ...", self.verbose)
        self.has_blank = False

    def show_extracting(self, data_dir):
        self._print("Extracting bundle to %s/ ..." % data_dir, self.verbose)
        self.has_blank = False

    def show_task_info(self, tasklist, resumption=False):
        visible = self.verbose
        num_tasks = len(tasklist.tasks)

        if resumption:
            self._print("Reloaded %d tasks:" % num_tasks, visible)
        else:
            self._print("Generated %d tasks:" % num_tasks, visible)

        for task in tasklist.tasks:
            task_id = task['id']
            is_visible = task['visible']
            task_status = tasklist.get_task_status(task_id)

            if is_visible:
                self._print("  <{type}> {name} (id={task_id}, {status})".format(
                    type=task['type'],
                    name=task['name'],
                    task_id=task_id,
                    status=task_status.name
                ), visible)

        self.has_blank = False

    def bundle_not_found(self, bundle_package):
        self._print("Recovery bundle %s not found" %
                    bundle_package, self.verbose)
        self.has_blank = False

    def invalid_vendor(self, vendor_name):
        self._print("Invalid vendor name %s" % vendor_name, self.verbose)
        self.has_blank = False

    def job_started(self, task):
        is_visible = task['visible']

        if is_visible:
            self._insert_blank()
            self._print("[JOB-STARTED] {name} (id={task_id})".format(
                name=task['name'],
                task_id=task['id']
            ))
        self.has_blank = True

    def job_completed(self, task):
        is_visible = task['visible']

        if is_visible:
            self._insert_blank()
            self._print("[JOB-COMPLETED] {name} (id={task_id})".format(
                name=task['name'],
                task_id=task['id']
            ))
        self.has_blank = True

    def job_cancelled(self, task):
        is_visible = task['visible']

        if is_visible:
            self._insert_blank()
            self._print("[JOB-CANCELLED] {name} (id={task_id})".format(
                name=task['name'],
                task_id=task['id']
            ))
        self.has_blank = True

    def job_failed(self, task):
        is_visible = task['visible']

        if is_visible:
            self._insert_blank()
            self._print("[JOB-FAILED] {name} (id={task_id})".format(
                name=task['name'],
                task_id=task['id']
            ))
        self.has_blank = True

    def upgrade_error(self, message=""):
        self._insert_blank()
        if message:
            self._print("[ERROR] %s" % message)
        else:
            self._print("[ERROR] Unknown error exception.")
        self.has_blank = True
        self.finished = True

    def upgrade_done(self, message=""):
        self._insert_blank()
        self._print("[DONE] Node upgrade is done.")
        self.has_blank = True
        self.finished = True

    def system_reboot(self, task=None):
        self._insert_blank()
        if task:
            self._print("[SYSTEM-REBOOT] {name} (id={task_id})".format(
                name=task['name'],
                task_id=task['id']
            ))
        else:
            self._print("[SYSTEM-REBOOT] System is being rebooted.")
        self.has_blank = True
        self.finished = True


console = ConsoleWriter()


def parse_args(sys_args):
    parser = argparse.ArgumentParser()
    parser.add_argument('-H', '--host',
                        help="Host name of this VxRail node")
    parser.add_argument('-b', '--bundle',
                        help='File of VxRail recovery bundle the node will be upgrade to')
    parser.add_argument('-D', metavar='DIR', dest='workdir',
                        help="Specifiy the alternative working directory for upgrade")
    parser.add_argument('--force', action='store_true',
                        default=False, help="Force node upgrade from the beginning")
    parser.add_argument('--verbose', action='store_true',
                        default=False, help="Show verbose output information")
    parser.add_argument('--timeout', default=SYSTEM_INIT_TIMEOUT,
                        help="Timeout for sytem preparation")
    parser.add_argument('--skip-esxi', action='store_true',
                        default=False, help="Skip ESXi patch installation when upgrade")
    parser.add_argument('--reboot-only', action='store_true',
                        default=False, help="Perform reboot action only")
    parser.add_argument('-N', '--dry-run', action="store_true",
                        default=False, help="Do not make any changes on current system.")
    parser.add_argument('--bypass', action="store_true",
                        default=False, help="Bypass target matching to list all possible tasks; Also implies '--dry-run'.")
    parser.add_argument('--bypass-customize-drivers',
                        help="Bypass customize driver operations by a comma-separated component name list.")
    parser.add_argument('--keep', action="store_true",
                        default=False, help="Keep intermediate data and status when upgrade done")
    parser.add_argument('-x', '--max-restart', type=int,
                        default=3, help="The maximum number of system restart (default: 3)")
    parser.add_argument('--downgrade', action='store_true',
                        default=False, help="Support bundle downgrade if target package is lower than installed version")
    parser.add_argument('--no-sig-check', dest='nosigcheck', action="store_true",
                        default=False, help="Bypass signing verification for VIB and patch installation")

    args = parser.parse_args(sys_args)

    if args.host is None:
        args.host = platform.node()

    if args.workdir is None:
        args.workdir = SCRIPT_DIR

    if args.bundle:
        args.bundle = os.path.realpath(args.bundle)

    if args.bypass:
        args.dry_run = True

    if args.bypass_customize_drivers:
        args.ignore_customize_drivers = args.bypass_customize_drivers.split(',')
    else:
        args.ignore_customize_drivers = []

    logger.debug("Command line arguments:")
    logger.debug(args)

    return args


def system_prepare(timeout=SYSTEM_INIT_TIMEOUT, hostd_only=False):
    # check if system is ready for upgrade
    # timeout is 300 seconds by default
    msg_shown = False
    expiry = time.time() + timeout

    if platform.system() != 'VMkernel':
        raise NotImplementedError("Current system is not supported")

    if hostd_only:
        is_ready = esxutil.get_hostd_status()
    else:
        is_ready = esxutil.check_system_ready()
    while expiry > time.time() and not is_ready:
        time.sleep(30)
        if hostd_only:
            is_ready = esxutil.get_hostd_status()
        else:
            is_ready = esxutil.check_system_ready()

        if is_ready:
            break
        else:
            if not msg_shown:
                console.show_initializing()
                msg_shown = True
            logger.warning('The system is not ready for upgrade......')

    if not is_ready:
        raise VxNodeUpgradeError('The system is not ready for node upgrade')

    logger.info('The system is ready for upgrade')

    try:
        esxutil.shutdown_all_vms()
    except Exception as e:
        logger.error(e, exc_info=True)
        logger.error('Fail to shutdown running VMs')
        raise VxNodeUpgradeError("Fail to shutdown running VMs")
    # do not change maintenance mode to avoid vSAN volume offline


def cleanup_stage_data(bundle_data_dir, task_data_dir):
    if bundle_data_dir and os.path.exists(bundle_data_dir):
        shutil.rmtree(bundle_data_dir, ignore_errors=True)
        logger.debug("Bundle directory %s has been deleted" %
                     bundle_data_dir)
    if task_data_dir and os.path.exists(task_data_dir):
        shutil.rmtree(task_data_dir, ignore_errors=True)
        logger.debug("Task directory %s has been deleted" % task_data_dir)


def main(sys_args):
    args = parse_args(sys_args)
    force_upgrade = args.force
    bypass_mode = args.bypass

    sysinfo = SystemInfo()
    console.verbose = args.verbose
    permit_mode = JobPermit.parse_conditions(dryrun=args.dry_run,
                                             skip_esxi=args.skip_esxi,
                                             reboot_only=args.reboot_only)

    bundle = RecoveryBundleManager(
        bundle_path=args.bundle, basedir=args.workdir)
    bundle_data_dir = None
    task_data_dir = None

    tasklist = None
    resumption = False

    console.show_hostname(args.host)
    bundle.scan()

    if not bypass_mode:
        if not bundle.content_exists or force_upgrade:
            system_prepare(args.timeout)
            sysinfo.load()
        else:
            system_prepare(args.timeout, hostd_only=True)
            sysinfo.load(ignore_firmware=True)


    if bundle.archive_exists:
        bundle_data_dir = bundle.get_bundle_data_dir()
        tasklist = TaskListManager(
            bundle_dir=bundle_data_dir,
            hostname=args.host,
            sysinfo=sysinfo,
            permit_mode=permit_mode,
            downgrade_mode=args.downgrade,
            nosigcheck=args.nosigcheck,
            ignore_customize_drivers=args.ignore_customize_drivers,
        )
        task_data_dir = tasklist.get_task_data_dir()
        stage_exists = bundle.content_exists and tasklist.catalog_exists
        stage_empty = (not bundle.content_exists) and (
            not tasklist.catalog_exists)
        stage_broken = bundle.content_exists ^ tasklist.catalog_exists

        logger.debug("bundle_data_dir={}; task_data_dir={}".format(
            bundle_data_dir, task_data_dir))
        logger.debug("stage_exists={}; stage_empty={}; stage_broken={}".format(
            stage_exists, stage_empty, stage_broken))
        console.show_recovery_bundle(bundle.bundle_path)

        if stage_broken and not force_upgrade:
            raise VxNodeUpgradeError(
                "Integrity checking has failed for task resumption")

        tasks_found = False
        if force_upgrade:
            cleanup_stage_data(bundle_data_dir, task_data_dir)
        elif stage_exists:
            console.show_reloading(task_data_dir)
            tasklist.load()
            if tasklist.reboot_counter > args.max_restart:
                raise VxNodeUpgradeError(
                    "The maximum number of system restart exceeded")
            elif tasklist.has_error:
                console.show_past_failure()
                console.show_retry()
                cleanup_stage_data(bundle_data_dir, task_data_dir)
            else:
                resumption = True
                tasks_found = True

        if not tasks_found:
            if not bypass_mode and not sysinfo.firmware_list:
                sysinfo.reload_firmware_list()

            console.show_extracting(bundle_data_dir)
            bundle.extract_bundle()
            tasklist.generate(ignore_target=bypass_mode)
            logger.debug("Task list has been generated")
            tasklist.save()
            logger.debug("Task list has been saved")
            resumption = False
    else:
        console.bundle_not_found(args.bundle)
        raise VxNodeUpgradeError(
            "No recovery bunldes are eligible for node upgrade")

    console.show_task_info(tasklist, resumption)

    while not tasklist.completed:
        forward = tasklist.run_current_task()
        if not forward:
            logger.debug("Task list has no forward task")
            break
    # end of task loop

    if args.dry_run:
        esxutil.remove_esxi_account(PSA_ACCOUNT)

    if tasklist.completed:
        if not args.keep:
            cleanup_stage_data(bundle_data_dir, task_data_dir)
        console.upgrade_done()
        # do not change maintenance mode to avoid vSAN volume offline
    elif tasklist.has_error:
        console.upgrade_error("Node upgrade aborted due to task failure.")
        # do not change maintenance mode to avoid vSAN volume offline


if __name__ == "__main__":
    logger.info("Starting VxRail node upgrade script %s ..." % __version__)

    try:
        logger.info("Current running system:")
        logger.info(platform.uname())

        main(sys.argv[1:])

        if not console.finished:
            logger.warning("The program has unexpectedly finished")

    except VxNodeUpgradeError as e:
        logger.error(e, exc_info=True)
        console.upgrade_error(str(e))
        esxutil.remove_esxi_account(PSA_ACCOUNT)

        sys.exit(e.exitcode)
    except Exception as e:
        logger.critical(e, exc_info=True)
        console.upgrade_error()
        esxutil.remove_esxi_account(PSA_ACCOUNT)

        sys.exit(1)
