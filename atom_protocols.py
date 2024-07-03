# -*- coding: utf-8 -*-
# @Time : 25/03/2024 17:34
# @Author : Qingyu Zhang
# @Email : qingyu.zhang.23@ucl.ac.uk
# @Institution : UCL
# @FileName: atom_protocols.py
# @Software: PyCharm
# @Blog ：https://github.com/alfredzhang98

import os
import time
import math
import logging
from enum import Enum, auto
import threading
from threading import Thread, Event
from typing import Any, Dict, List, Type, Union, Tuple, Callable, get_origin, get_args
import hashlib
import binascii
import bcrypt
from crccheck.crc import Crc16

'''
See this guide: https://alfredzhang98.notion.site/1ebabd414334452586bec7ad4c06f983?pvs=4
pip install AtomEncryption-0.0.1-py3-none-any.whl
'''
class ProtocolStatus:
    p_ture = 1
    p_false = 0
    p_error = -1

    class DecodeErrorType(Enum):
        def _generate_next_value_(name, start, count, last_values):
            if count == 0:
                return 0
            return -count

        NO_ERROR = 0
        HEADER_ERROR = auto()
        SEQ_ERROR = auto()
        UUID_ERROR = auto()
        PACKAGE_NUM_ERROR = auto()
        DATA_NUM_PER_ERROR = auto()
        VPP_ERROR = auto()
        CMD_ERROR = auto()

    class Functions(Enum):
        SPP = 0x10
        STEAM = 0x20
        RADIO = 0x30
        VIDEO = 0x40

    class Direction:
        # send
        send_start = 0x00
        send_need_none_feedback = 0x00
        send_need_sync_feedback = 0x10
        send_end = 0x7F
        # reply
        reply_start = 0x80
        # 0x90 is the reply of the sync feedback
        reply_end = 0xFF

    class SeqSysCMD:
        class SPP(Enum):
            SEND_CMD_NONE = auto()
            SEND_AUTHENTICATION = auto()
            SEND_TOTAL_INFO = auto()
            send_total_info = auto()
            SEND_LOST_PACKAGE = auto()
            SEND_WRONG_DATA = auto()

    class ProtocolsLength:
        __temp = 0
        header_length = 4
        __temp = 0 + header_length
        seq_length = 2
        __temp = __temp + seq_length
        uuid_length = 2
        __temp = __temp + uuid_length
        package_num_length = 4
        __temp = __temp + package_num_length
        data_num_per_package_length = 2
        __temp = __temp + data_num_per_package_length
        # crc16
        vpp_length = 2
        __temp = __temp + vpp_length
        cmd_length = 2
        __temp = __temp + cmd_length
        total_crc_length = __temp - cmd_length
        total_length = __temp


class DictManager:
    def __init__(self, expected_format: Any, stack_length: int = 0xFFFF):
        self.max_stack_length = stack_length
        self.expected_format = expected_format
        self.data = {}
        self.min_key = None
        self.last_key = None

    def insert(self, key: Any, value: Any):
        self.pop_over_stack()
        key_format, value_format = self._get_key_value_formats()
        if not self._validate_format(key, key_format) or not self._validate_format(value, value_format):
            raise ValueError(f"Incorrect data format: The expected format is {self.expected_format}")
        self.data[key] = value
        self.update_min_max_keys(key)

    def append_next(self, value: Any):
        self.pop_over_stack()
        _, value_format = self._get_key_value_formats()
        if not self._validate_format(value, value_format):
            raise ValueError(f"Incorrect data format: The expected format is {self.expected_format}")
        next_key = (self.last_key + 1) if self.last_key != None else 0
        self.insert(next_key, value)

    def get_min_key(self):
        return self.min_key

    def get_min_value(self):
        if self.min_key != None:
            return self.data[self.min_key]
        return None
    
    def get_stack(self):
        return self.data
    
    def pop(self, key: Any) -> Any:
        result = None
        if key in self.data:
            result = self.data.pop(key)
            self.update_min_max_keys_after_pop(key)
        return result

    def pop_min(self) -> Any:
        result = None
        if self.min_key != None:
            result = self.data.pop(self.min_key)
            self.min_key = min(self.data.keys(), default=None)
        return result

    def pop_over_stack(self) -> None:
        while len(self.data) > self.max_stack_length:
            self.pop_min()

    def get_stack_length(self) -> int:
        return len(self.data)

    def _get_key_value_formats(self):
        args = get_args(self.expected_format)
        key_format = args[0] if len(args) > 0 else Any
        value_format = args[1] if len(args) > 1 else Any
        return key_format, value_format

    def _validate_format(self, value: Any, expected_format: Any) -> bool:
        origin = get_origin(expected_format)
        if origin == dict:
            if not isinstance(value, dict):
                return False
            key_type, val_type = get_args(expected_format)
            for k, v in value.items():
                if not self._validate_format(k, key_type) or not self._validate_format(v, val_type):
                    return False
        elif origin == list:
            if not isinstance(value, list):
                return False
            sub_format = get_args(expected_format)[0] if get_args(expected_format) else Any
            for item in value:
                if not self._validate_format(item, sub_format):
                    return False
        elif origin == tuple:
            if not isinstance(value, tuple) or len(value) != len(get_args(expected_format)):
                return False
            for item, sub_format in zip(value, get_args(expected_format)):
                if not self._validate_format(item, sub_format):
                    return False
        elif origin == Union:
            if not any(self._validate_format(value, sub_format) for sub_format in get_args(expected_format)):
                return False
        else:
            if expected_format == Any:
                return True
            return isinstance(value, expected_format)
        return True

    def update_min_max_keys(self, key: Any):
        if self.min_key == None or key < self.min_key:
            self.min_key = key
        if self.last_key == None or key > self.last_key:
            self.last_key = key

    def update_min_max_keys_after_pop(self, key: Any):
        if key == self.min_key:
            self.min_key = min(self.data.keys(), default=None)
        if key == self.last_key:
            self.last_key = max(self.data.keys(), default=None)


class TypeSwitch:
    @staticmethod
    def int_list_to_str(int_list: List[int]) -> str:
        return ''.join(chr(i) for i in int_list)

    @staticmethod
    def str_to_int_list(string: str) -> List[int]:
        return [ord(c) for c in string]

    @staticmethod
    def int_list_to_tuple(int_list: List[int]) -> Tuple:
        return tuple(int_list)

    @staticmethod
    def tuple_to_int_list(u_tuple: Tuple) -> List[int]:
        return list(u_tuple)

    @staticmethod
    def char_list_to_int_list(char_list: List[str]) -> List[int]:
        return [ord(c) for c in char_list]

    @staticmethod
    def int_list_to_char_list(int_list: List[int]) -> List[str]:
        return [chr(i) for i in int_list]

    @staticmethod
    def char_list_to_str(char_list: List[str]) -> str:
        return ''.join(char_list)

    @staticmethod
    def str_to_char_list(string: str) -> List[str]:
        return list(string)

    @staticmethod
    def hex_string_to_int_list(hex_string: str) -> List[int]:
        """Convert a hex string to a list of integers."""
        return [int(hex_string[i:i + 2], 16) for i in range(0, len(hex_string), 2)]

    @staticmethod
    def int_list_to_hex_string(int_list: List[int]) -> list[str]:
        """Convert a list of integers to a list of hex strings without '0x' prefix and padded with zeros if
        necessary."""
        return ['{:02x}'.format(number) for number in int_list]

    @staticmethod
    def bytes_to_int_list(b: bytes) -> List[int]:
        return list(b)

    @staticmethod
    def int_list_to_bytes(int_list: List[int]) -> bytes:
        return bytes(int_list)

    @staticmethod
    def bytes_to_str(b: bytes, encoding='utf-8') -> str:
        return b.decode(encoding)

    @staticmethod
    def str_to_bytes(s: str, encoding='utf-8') -> bytes:
        return s.encode(encoding)

    @staticmethod
    def int_to_int_list(n: int, specified_length: int = None, order: str = "msb") -> List[int]:
        byte_list = []
        while n:
            byte_list.append(n & 0xFF)
            n >>= 8
        if order == 'msb':
            byte_list.reverse()
        if specified_length != None:
            additional_length = specified_length - len(byte_list)
            if additional_length < 0:
                raise ValueError("Specified length is less than the generated list length.")
            # 对于msb，高位在前；对于lsb，高位在后
            byte_list = ([0] * additional_length + byte_list) if order == 'msb' else (
                        byte_list + [0] * additional_length)
        return byte_list

    @staticmethod
    def int_list_to_int(byte_list: List[int], order: str = "msb") -> int:
        if order == 'lsb':
            byte_list = byte_list[::-1]
        result = 0
        for byte in byte_list:
            result = (result << 8) | byte
        return result

class Hash:
        '''
        hasher = IrreversibleEncryptionTools.Hash()
        salt = hasher.generate_salt()
        hashed_data_sha256 = hasher.hash_data("your_password_here", 'sha256', salt)
        hashed_data_bcrypt = hasher.hash_data("your_password_here", 'bcrypt')
        print(hashed_data_sha256)
        print(hashed_data_bcrypt)
        verification_result = hasher.verify_bcrypt_hash("your_password_here", hashed_data_bcrypt)
        print(verification_result)
        '''
        @staticmethod
        def hash_data(data, algorithm='sha256', salt=None):
            """
            Hash the data with specified algorithm and an optional salt.
            Supported algorithms: 'sha256', 'sha512', 'md5', 'bcrypt'.
            """
            if algorithm in ['sha1', 'sha256', 'sha512', 'md5']:
                hash_object = hashlib.new(algorithm)
                if salt:
                    hash_object.update(salt.encode() + data.encode())
                else:
                    hash_object.update(data.encode())
                return hash_object.hexdigest()
            elif algorithm == 'bcrypt':
                if salt == None:
                    salt = bcrypt.gensalt()
                return bcrypt.hashpw(data.encode(), salt).decode()
            else:
                raise ValueError(f"Unsupported algorithm: {algorithm}")

        @staticmethod
        def generate_salt(length=16):
            """
            Generate a random salt of specified length.
            """
            salt = os.urandom(length)
            return binascii.hexlify(salt).decode()

        @staticmethod
        def verify_bcrypt_hash(data, hashed):
            """
            Verify if the data matches the hashed value using bcrypt.
            """
            return bcrypt.checkpw(data.encode(), hashed.encode())

def singletonDecorator(cls):
    instances = {}
    def get_instance(*args, **kwargs):
        if cls not in instances:
            instances[cls] = cls(*args, **kwargs)
        return instances[cls]

    return get_instance

# @singletonDecorator
class AtomProtocols:
    """
    SPP:
        SPP Decode:
    """

    def __init__(self, send_interface: Callable[[List[int], int], bool],
                 receive_interface: Callable[[], List[int]],
                 belongs: str,
                 header: Tuple[int] = (0xE5, 0x5E, 0xF2, 0x2F),
                 package_length: int = 1024,
                 function: ProtocolStatus.Functions = ProtocolStatus.Functions.SPP,
                 authentication_info: str = "atom_default"):
        """
        :param header: default is (0xE5, 0x5E, 0xF2, 0x2F)
        :param belongs: master / slave
        :param package_length: default package length per send
        :param function: SPP / Steam or others
        :param authentication_info: This info should be same in receiver and sender
        :param send_interface: Must put in by user Callable[[List[int], int], int] input: Data and Data_len Return: Int
        :param receive_interface: Must put in by user Callable[] input: Data and Data_len Return: Int
        """
        # Logger
        logging.basicConfig(level=logging.NOTSET, format='%(asctime)s - %(levelname)s - %(name)s - %(message)s')
        self.logger = logging.getLogger(self.__class__.__name__ + "-" + belongs)

        if send_interface == None or receive_interface == None:
            raise ValueError("Please input your own send and receive interface")

        # replace any capital
        belongs = belongs.lower()
        if belongs not in ["master", "slave"]:
            raise ValueError("Please input the right belongs")

        self.__send_callable = send_interface
        self.__receive_callable = receive_interface
        self.__belongs = belongs
        self.__header = header
        self.__package_length = package_length
        self.__function = function
        self.__authentication_info = authentication_info

        # Flags
        self.__authentication_status = False
        # Master record the slave link id
        self.__master_link_id = []
        # Each has its own slave link id
        self.__slave_link_id = None
        self.init_link_id()

        # Common
        self.__package_split_num = self.__package_length - ProtocolStatus.ProtocolsLength.total_length
        self.__send_seq_sys_cmd = ProtocolStatus.SeqSysCMD.SPP.SEND_CMD_NONE.value

        # Sender
        # This stack is used for store encoded send data
        self.__max_encode_data_stack_length = 0xFFFF
        self.__encode_data_stack = DictManager(Dict[int, List[int]], self.__max_encode_data_stack_length)
        # This stack is used for store the send data with uuid those data need a reply
        # When a reply come please del the uuid
        self.__max_reply_data_stack_length = 0xFFFF
        self.__reply_data_stack = DictManager(Dict[int, Dict[str, List[int]]], self.__max_reply_data_stack_length)
        self.__package_uuid = 0x0000
        # This is a thread for send data
        self.__thread_sending = False
        self.__init_sending_thread()

        # Wait for the thread to start
        time.sleep(0.5)

        # Receiver
        self.__last_package_num = 0x00
        self.__max_decode_data_stack_length = 0xFFFF
        self.__decode_data_stack = DictManager(Dict[int, Dict[str, List[int]]], self.__max_decode_data_stack_length)
        self.__thread_receiving = False
        self.__init_receiving_thread()

    @property
    def package_length(self):
        return self.__package_length

    @package_length.setter
    def package_length(self, value):
        self.__package_length = value

    @property
    def function(self):
        return self.__function

    @staticmethod
    def calculate_crc16(data: List[int]):
        return TypeSwitch.int_to_int_list(Crc16.calc(data))
    
    
    ##########################################################################################################################
    ##########################################################################################################################
    ##########################################################################################################################
    # Connection Management
    def init_link_id(self) -> None:
        # Generate the slave link id in two bytes randomly
        if self.__belongs == "slave":
            self.__slave_link_id = TypeSwitch.int_to_int_list(math.floor(time.time() * 1000) % 0xFFFF, 2)
        if self.__belongs == "master":
            pass

    # User use this to check the connection
    def connection_verification(self) -> bool:
        print("Connection Verification")
        # If the user is master, it will wait for the slave to connect
        if self.__belongs == "master":
            time.sleep(0.5)
            return self.__authentication_status
        
        # If the user is slave, it try to connect to the master this function would make the program stack here until the master is connected
        elif self.__belongs == "slave":
            if self.__authentication_status:
                return self.__authentication_status
            else:
                while not self.__authentication_status:
                    self.__init_authentication_send()
                    time.sleep(0.5)
                return self.__authentication_status

    ##########################################################################################################################
    ##########################################################################################################################
    ##########################################################################################################################
    # Sender
    # Thread instruction: 
    # 1. __thread_encode_sending: This thread is used for sending data, it will encode the data and send it. Take data from the encode_data_stack and use the send_callable to send it. Whenever the thread is running, it will keep sending data.

    # Send data instruction:
    # 1. send_data: This function is used for sending data, it will encode the data and put it into the encode_data_stack. The data will be sent by the __thread_encode_sending thread.
    # 2. __send_internal_reply: This function is used for sending the internal CMD reply data, it will encode the data and put it into the encode_data_stack. The data will be sent by the __thread_encode_sending thread.
    # 3，send_reply: This function is used for sending the reply data, it will encode the data and put it into the encode_data_stack. The data will be sent by the __thread_encode_sending thread.
    #########################################
    # Sender Thread
    def __thread_encode_sending(self, stop_event):
        try:
            while not stop_event.is_set():
                if self.__thread_sending:
                    if self.__encode_data_stack.get_stack_length() > 0:
                        data = self.__encode_data_stack.pop_min()
                        self.__send_callable(data, len(data))
                else:
                    time.sleep(0.1)
        except Exception as e:
            self.logger.exception("An exception occurred" + str(e))

    # This is used in the init function
    def __init_sending_thread(self) -> None:
        """
        Init the sending thread
        :return: None
        """
        match self.__function.value:
            case ProtocolStatus.Functions.SPP.value:
                self.__thread_sending = True
                self.__u_thread_sending_stop_event = threading.Event()
                self.__u_thread_sending = threading.Thread(target=self.__thread_encode_sending,
                                                   args=(self.__u_thread_sending_stop_event,))
                self.__u_thread_sending.start()
                self.logger.info("You start the sending thread")
                return None
            case ProtocolStatus.Functions.STEAM.value:
                return None
            case _:
                return None

    # User can use this function to stop the sending thread
    def set_sending_thread(self, status: bool) -> None:
        """
        Stop the sending thread
        :return: None
        """
        match self.__function.value:
            case ProtocolStatus.Functions.SPP.value:
                self.__thread_sending = status
                if status:
                    self.__u_thread_sending_stop_event.clear()
                else:
                    self.__u_thread_sending_stop_event.set()
                self.__u_thread_sending.join()
                self.logger.info("you set the sending thread status to " + str(status))
                return None
            case ProtocolStatus.Functions.STEAM.value:
                return None
            case _:
                return None

    ############################################
    # Send data
    # Encode
    def __encode_basic(self, seq: List[int], cmd: List[int], data: List[int], uuid: int = None) -> List[List[int]]:
        full_data_list = []
        package_count = 0
        # UUID insert in the reply stack
        if uuid != None:
            uuid_temp = uuid
        else:
            if self.__package_uuid >= self.__max_reply_data_stack_length:
                self.__package_uuid = 0x00
            self.__package_uuid = self.__package_uuid + 1
            uuid_temp = self.__package_uuid
        if (seq[0] & 0xF0) in [ProtocolStatus.Direction.send_need_sync_feedback]:
            # If the data need a reply, put the data into the reply stack
            self.__reply_data_stack.get_stack()[self.__package_uuid] = {"seq": seq, "cmd": cmd, "data": data}
        for i in range(0, len(data), self.__package_split_num):
            uuid = TypeSwitch.int_to_int_list(uuid_temp, 2)
            crc = self.calculate_crc16(cmd + data[i:i + self.__package_split_num])
            package_count = package_count + 1
            package_count_list = TypeSwitch.int_to_int_list(package_count, 4)
            data_length_per_package_list = TypeSwitch.int_to_int_list(ProtocolStatus.ProtocolsLength.cmd_length +
                                                                      len(data[i:i + self.__package_split_num]), 2)
            full_data_list.append(
                list(self.__header) + seq + uuid + package_count_list + data_length_per_package_list + crc +
                cmd + data[i:i + self.__package_split_num])
        return full_data_list

    # insert data to the stack which will be sent by the sending thread
    def __insert_send(self, data: List[int], boost: bool = False):
        # waste the oldest data if the stack is full
        if boost:
            # Insert the data to the first to boost the sending speed
            self.__encode_data_stack.insert(0, data)
        else:
            # Insert the data to the last to keep the order
            self.__encode_data_stack.append_next(data)
    
    def send_data(self, cmd: list[int], data: List[int],
                  feedback_status: int = ProtocolStatus.Direction.send_need_none_feedback,
                  send_seq_user_cmd: int = 0x00) -> None:
        """
        :param cmd:
        :param data:
        :param feedback_status:  send_need_none_feedback / send_need_async_feedback / send_need_sync_feedback
        :param send_seq_user_cmd: send_ways and seq
        :return: -1 / 0 / 1
        """
        if self.__authentication_status:
            if feedback_status not in [ProtocolStatus.Direction.send_need_none_feedback,
                                       ProtocolStatus.Direction.send_need_sync_feedback]:
                raise ValueError("Not input the right feedback_status, please read the instruction")
            datas = self.__encode_basic(seq=[feedback_status | ProtocolStatus.SeqSysCMD.SPP.SEND_CMD_NONE.value,
                                             send_seq_user_cmd | self.__function.value],
                                        cmd=cmd,
                                        data=data)
            for data in datas:
                self.__insert_send(data)
        else:
            self.__init_authentication_send()

    def __send_internal_reply(self, uuid: int, cmd: List[int], seq: List[int], data: List[int]):
        # uuid to get the data from the receiver stack
        feedback_status = seq[0] & 0xF0
        if feedback_status < 0x80:
            feedback_status = feedback_status | 0x80
        datas = self.__encode_basic(seq=[feedback_status | (seq[0] & 0x0F),
                                         seq[1]],
                                    cmd=cmd,
                                    data=data,
                                    uuid=uuid)
        for data in datas:
            self.__insert_send(data)

    def send_reply(self, uuid: int, reply_data: List[int]) -> None:
        # uuid to get the data from the receiver stack
        seq = self.__decode_data_stack.get_stack()[uuid]["seq"]
        feedback_status = seq[0] & 0xF0
        if feedback_status < 0x80:
            feedback_status = feedback_status | 0x80
        datas = self.__encode_basic(seq=[feedback_status | (seq[0] & 0x0F),
                                         seq[1]],
                                    cmd=self.__decode_data_stack.get_stack()[uuid]["cmd"],
                                    data=reply_data,
                                    uuid=uuid)
        # pop the data from the decode stack, this means this data wouble be deleted
        self.__decode_data_stack.pop(uuid)
        for data in datas:
            self.__insert_send(data)

    ##########################################################################################################################
    ##########################################################################################################################
    ##########################################################################################################################
    # Receiver
    # Thread instruction: 
    # 1. __thread_decode_receiving: This thread is used for receiving data, it will decode the data and put it into the decode_data_stack. Take data from the receive_callable and use the decode_basic to decode it. Whenever the thread is running, it will keep receiving data.
    # 2. __init_receiving_thread: This function is used to init the receiving thread
    # 3. set_receiving_thread: This function is used to stop the receiving thread

    #########################################
    # Receiver Thread
    def __thread_decode_receiving(self, stop_event):
        try:
            while not stop_event.is_set():
                if self.__thread_receiving:
                    data = self.__receive_callable()
                    # waste the oldest data if the stack is full
                    self.__decode_data_stack.pop_over_stack()
                    if data != None and data != []:
                        # self.logger.debug(data)
                        match self.__decode_basic(data):
                            case ProtocolStatus.DecodeErrorType.NO_ERROR:
                                pass
                            case ProtocolStatus.DecodeErrorType.HEADER_ERROR:
                                self.logger.warning("HEADER_ERROR")
                            case ProtocolStatus.DecodeErrorType.SEQ_ERROR:
                                self.logger.warning("SEQ_ERROR")
                            case ProtocolStatus.DecodeErrorType.UUID_ERROR:
                                self.logger.warning("UUID_ERROR")
                            case ProtocolStatus.DecodeErrorType.PACKAGE_NUM_ERROR:
                                self.logger.warning("PACKAGE_NUM_ERROR")
                            case ProtocolStatus.DecodeErrorType.DATA_NUM_PER_ERROR:
                                self.logger.warning("DATA_NUM_PER_ERROR")
                            case ProtocolStatus.DecodeErrorType.VPP_ERROR:
                                self.logger.warning("VPP_ERROR")
                            case ProtocolStatus.DecodeErrorType.CMD_ERROR:
                                self.logger.warning("CMD_ERROR")
                            case _:
                                pass
                    else:
                        pass
                else:
                    time.sleep(0.1)
        except Exception as e:
            self.logger.exception("An exception occurred" + str(e))

    # This is used in the init function
    def __init_receiving_thread(self) -> None:
        """
        Init the receiving thread
        :return: None
        """
        match self.__function.value:
            case ProtocolStatus.Functions.SPP.value:
                self.__thread_receiving = True
                self.__u_thread_receiving_stop_event = threading.Event()
                self.__u_thread_receiving = threading.Thread(target=self.__thread_decode_receiving,
                                                     args=(self.__u_thread_receiving_stop_event,))
                self.__u_thread_receiving.start()
                self.logger.info("You start the receiving thread")
                return None
            case ProtocolStatus.Functions.STEAM.value:
                return None
            case _:
                return None

    # User can use this function to stop the receiving thread
    def set_receiving_thread(self, status: bool) -> None:
        """
        Stop the receiving thread
        :return: None
        """
        match self.__function.value:
            case ProtocolStatus.Functions.SPP.value:
                self.__thread_receiving = status
                if status:
                    self.__u_thread_receiving_stop_event.clear()
                else:
                    self.__u_thread_receiving_stop_event.set()
                self.__u_thread_receiving.join()
                self.logger.info("you set the receiving thread status to " + str(status))
                return None
            case ProtocolStatus.Functions.STEAM.value:
                return None
            case _:
                return None

    #########################################
    # Receive Data
    # Decode
    def __seq_handler(self, uuid: int, seq: List[int], data: List[int]) -> bool:
        # Todo need to finish this function for more things
        seq_data_direction = seq[0] & 0xF0
        seq_sys_cmd = seq[0] & 0x0F
        match self.__function.value:
            # SPP
            case ProtocolStatus.Functions.SPP.value:
                # Receive the send data
                if seq_data_direction <= ProtocolStatus.Direction.send_end:
                    match seq_sys_cmd:
                        case ProtocolStatus.SeqSysCMD.SPP.SEND_CMD_NONE.value:
                            return False
                        case ProtocolStatus.SeqSysCMD.SPP.SEND_AUTHENTICATION.value:
                            # reply inside the function
                            # Master would receive the authentication data from the slave
                            if self.__belongs == "master":
                                # If the verfication is correct, the authentication status would be True and reply the data "1" to the slave
                                # Else, the authentication status would be False and reply the data "0" to the slave
                                self.__init_authentication_receive(uuid, seq, data)
                            return True
                        case ProtocolStatus.SeqSysCMD.SPP.send_total_info.value:
                            self.__init_receive_total_info(uuid, data)
                            # no need to reply
                            return True
                        case ProtocolStatus.SeqSysCMD.SPP.SEND_WRONG_DATA.value:
                            # Todo: need to resend from the wrong data package
                            return True
                        case ProtocolStatus.SeqSysCMD.SPP.SEND_LOST_PACKAGE.value:
                            # Todo: need to resend from the lost data package
                            return True
                        case _:
                            return False
                ####################
                # Receive the reply data
                if seq_data_direction >= ProtocolStatus.Direction.reply_start:
                    # NOTE: This part is Must do, to pop the sender stack
                    if seq_data_direction in [(ProtocolStatus.Direction.send_need_sync_feedback |
                                               ProtocolStatus.Direction.reply_start)]:
                        if self.__reply_data_stack.get_stack()[uuid] != None:
                            # handle the related reply data in the sender stack
                            del self.__reply_data_stack.get_stack()[uuid]
                            # The reply data would be not handle here those data would store in the decode_data_stack and user can get it by get_decode_data
                    match seq_sys_cmd:
                        case ProtocolStatus.SeqSysCMD.SPP.SEND_CMD_NONE.value:
                            # No feedback
                            return False
                        case ProtocolStatus.SeqSysCMD.SPP.SEND_AUTHENTICATION.value:
                            if self.__belongs == "slave":
                                self.__authentication_status = bool(TypeSwitch.int_list_to_int(data))
                                self.logger.info("Success authentication")
                            return True
                        case ProtocolStatus.SeqSysCMD.SPP.send_total_info.value:
                            # No feedback
                            return True
                        case ProtocolStatus.SeqSysCMD.SPP.SEND_WRONG_DATA.value:
                            # No feedback
                            return False
                        case ProtocolStatus.SeqSysCMD.SPP.SEND_LOST_PACKAGE.value:
                            # No feedback
                            return False
                        case _:
                            return False
        return False

    def __package_handler(self, package_num: int):
        if package_num == (self.__last_package_num + 1):
            return True
        else:
            # The package is not continuously
            return False

    def __crc_handler(self, cmd: List[int], data: List[int], crc: List[int]) -> bool:
        match self.__function.value:
            # SPP
            case ProtocolStatus.Functions.SPP.value:
                if crc == self.calculate_crc16(cmd + data):
                    return True
                else:
                    return False
            case _:
                return False

    def __decode_basic(self, data: List[int]) -> int:
        match self.__function.value:
            case ProtocolStatus.Functions.SPP.value:
                header_len = ProtocolStatus.ProtocolsLength.header_length
                seq_len = ProtocolStatus.ProtocolsLength.seq_length
                uuid_len = ProtocolStatus.ProtocolsLength.uuid_length
                package_num_len = ProtocolStatus.ProtocolsLength.package_num_length
                data_num_per_package_len = ProtocolStatus.ProtocolsLength.data_num_per_package_length
                vpp_len = ProtocolStatus.ProtocolsLength.vpp_length
                cmd_len = ProtocolStatus.ProtocolsLength.cmd_length

                data_step = 0
                if (data[data_step + header_len - 1] != self.__header[3] or
                        data[data_step + header_len - 2] != self.__header[2] or
                        data[data_step + header_len - 3] != self.__header[1] or
                        data[data_step + header_len - 4] != self.__header[0]):
                    return ProtocolStatus.DecodeErrorType.HEADER_ERROR
                data_step = header_len
                seq = data[data_step: data_step + seq_len]
                data_step = data_step + seq_len
                uuid = TypeSwitch.int_list_to_int(data[data_step: data_step + uuid_len])
                data_step = data_step + uuid_len
                package_num = data[data_step: data_step + package_num_len]
                data_step = data_step + package_num_len
                data_num_per_package = data[data_step: data_step + data_num_per_package_len]
                data_step = data_step + data_num_per_package_len
                vpp = data[data_step: data_step + vpp_len]
                data_step = data_step + vpp_len
                cmd = data[data_step: data_step + cmd_len]
                data_step = data_step + cmd_len
                main_data = data[data_step::]

                # Seq handler, focus on the seq sys cmd
                if self.__seq_handler(uuid, seq, main_data):
                    return ProtocolStatus.DecodeErrorType.NO_ERROR

                # Package num test
                if not self.__package_handler(TypeSwitch.int_list_to_int(package_num)):
                    # Todo: Lost Package Data need sth to do send a feedback to sender lost package
                    return ProtocolStatus.DecodeErrorType.PACKAGE_NUM_ERROR

                # not lost data test CRC test
                if not self.__crc_handler(cmd, main_data, vpp):
                    # Todo: Wrong Data need sth to do send a feedback to sender lost data
                    return ProtocolStatus.DecodeErrorType.VPP_ERROR

                # Add data
                if uuid not in self.__decode_data_stack.get_stack():
                    self.__decode_data_stack.get_stack()[uuid] = {}
                if self.__decode_data_stack.get_stack()[uuid] == None or len(self.__decode_data_stack.get_stack()[uuid]) <= 2:
                    self.__decode_data_stack.get_stack()[uuid]["seq"] = seq
                    self.__decode_data_stack.get_stack()[uuid]["package_num"] = package_num
                    self.__decode_data_stack.get_stack()[uuid]["data_num_per_package"] = data_num_per_package
                    self.__decode_data_stack.get_stack()[uuid]["cmd"] = cmd
                    self.__decode_data_stack.get_stack()[uuid]["data"] = main_data
                    self.__decode_data_stack.update_min_max_keys(uuid)
                else:
                    if isinstance(self.__decode_data_stack.get_stack()[uuid]["data"], list):
                        self.__decode_data_stack.get_stack()[uuid]["data"].extend(main_data)
            case _:
                pass

    def get_decode_data(self) -> Tuple:
        uuid = self.__decode_data_stack.get_min_key()
        if uuid == None:
            return None, None
        # If the data need a reply, not delete the data from the stack it would be deleted after the send_reply function
        if self.__decode_data_stack.get_stack()[uuid]["seq"][0] & 0xF0 in [ProtocolStatus.Direction.send_need_sync_feedback]:
            # If the data need a reply, put the data into the reply stack
            temp = self.__decode_data_stack.get_stack()[uuid]
        else:
            # If the data do not need a reply, delete the data from the stack
            temp = self.__decode_data_stack.pop(uuid)
        return uuid, temp

    ##########################################################################################################################
    ##########################################################################################################################
    ##########################################################################################################################
    # Internal CMD Send Function
    # Authentication Send
    def __init_authentication_send(self):
        # Send data
        if self.__belongs == "slave" and not self.__authentication_status:
            self.__send_seq_sys_cmd = ProtocolStatus.SeqSysCMD.SPP.SEND_AUTHENTICATION.value
            seq_data = [0x00, 0x00]
            seq_data[0] = ProtocolStatus.Direction.send_need_sync_feedback | self.__send_seq_sys_cmd
            seq_data[1] = 0x00 | self.__function.value
            authentication_data = Hash.hash_data(self.__authentication_info, "sha256")
            datas = self.__encode_basic(seq=seq_data,
                                        cmd=[0xFF, 0xFF],
                                        data=TypeSwitch.hex_string_to_int_list(authentication_data))
            for data in datas:
                self.__send_callable(data, len(data))

    # Slave Link ID Send to Master
    def __init_slave_link_id_send(self):
        # If this is a slave, it will send the link id to the master
        if self.__belongs == "slave" and self.__authentication_status:
            self.__send_seq_sys_cmd = ProtocolStatus.SeqSysCMD.SPP.SEND_TOTAL_INFO.value
            seq_data = [0x00, 0x00]
            seq_data[0] = ProtocolStatus.Direction.send_need_sync_feedback | self.__send_seq_sys_cmd
            seq_data[1] = 0x00 | self.__function.value
            datas = self.__encode_basic(seq=seq_data,
                                        cmd=[0xFF, 0xFF],
                                        data=self.__slave_link_id)
            for data in datas:
                self.__send_callable(data, len(data))

    def __init_send_total_info(self, data: List[int]):
        if self.__authentication_status:
            self.__send_seq_sys_cmd = ProtocolStatus.SeqSysCMD.SPP.send_total_info.value
            self.__total_packages = math.ceil((len(data) - ProtocolStatus.ProtocolsLength.total_length) /
                                            self.__package_split_num)
            self.__total_data = len(data)
            datas = self.__encode_basic(seq=[ProtocolStatus.Direction.send_need_none_feedback | self.__send_seq_sys_cmd,
                                            0x00 | self.__function.value],
                                        cmd=[0xFF, 0xFF],
                                        data=(TypeSwitch.int_to_int_list(self.__total_packages, 16) +
                                            TypeSwitch.int_to_int_list(self.__total_data, 16)))
            for data in datas:
                self.__send_callable(data, len(data))
            # Todo wait the receiver to confirm they receive the total info
    
    ##########################################################################################################################
    ##########################################################################################################################
    ##########################################################################################################################
    # Internal CMD Receive Function

    def __init_authentication_receive(self, uuid: int, seq: List[int], data: List[int]) -> None:
        authentication_data = Hash.hash_data(self.__authentication_info, "sha256")
        if self.__belongs == "master" and data == TypeSwitch.hex_string_to_int_list(authentication_data):
            self.__authentication_status = True
        else:
            self.logger.warning("Wrong authentication data")
        self.__send_internal_reply(uuid=uuid,
                                   cmd=[0xFF, 0xFF],
                                   seq=seq,
                                   data=[int(self.__authentication_status)])

if __name__ == "__main__":

    # Test the AtomProtocols
    # Create a virtual wire to connect the master and slave
    # Send data from master to slave

    slave_receive = []
    master_receive = []

    def master_send_data(data: List[int], data_len: int) -> bool:
        global slave_receive
        slave_receive = data
        # print("Master send")
        # print("Master send data!!!: ", data)
        return True
    
    def slave_send_data(data: List[int], data_len: int) -> bool:
        global master_receive
        master_receive = data
        # print("Slave send")
        # print("Slave send data!!!: ", data)
        return True
    
    def master_receive_data() -> List[int]:
        global master_receive
        if master_receive:
            temp = master_receive
            master_receive = []
            # print("Master receive data!!!")
            return temp
        return None
    
    def slave_receive_data() -> List[int]:
        global slave_receive
        if slave_receive:
            temp = slave_receive
            slave_receive = []
            # print("Slave receive data!!!")
            return temp
        return None
    
    master = AtomProtocols(send_interface=master_send_data,
                            receive_interface=master_receive_data,
                            belongs="master")
    time.sleep(1)

    slave = AtomProtocols(send_interface=slave_send_data,
                            receive_interface=slave_receive_data,
                            belongs="slave")
    
    time.sleep(1)
    slave.connection_verification()

    slave.send_data([0x01, 0x02], [0x01, 0x02, 0x03, 0x04])
    time.sleep(1)
    uuid, data = master.get_decode_data()
    print("Master receive data: ", data)
    print("Master receive data uuid: ", uuid)

    master.connection_verification()
    master.send_data([0x01, 0x02], [0x01, 0x02, 0x03, 0x04])
    time.sleep(1)
    uuid, data = slave.get_decode_data()
    print("Slave receive data: ", data)
    print("Slave receive data uuid: ", uuid)
