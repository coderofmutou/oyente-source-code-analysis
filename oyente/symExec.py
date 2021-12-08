# 这个文件是这个框架最重要也是最难以理解的文件，它的基本步骤可以描述成：
#   1. 初始化和收集各种变量。
#   2. 生成 control flow graph(CFG)，这是一种在每个区块中只含有逻辑指令，不含有分支指令的图。
#   3. 深度优先遍历 CFG，获取整一个逻辑框架所有的可能性。
#   4. 对所有的可能性方案用 z3 求解器进行验算，对于位置的形参，使用 symbolic execution 的方式。

import tokenize
import zlib, base64
from tokenize import NUMBER, NAME, NEWLINE
import re
import math
import sys
import pickle
import json
import traceback
import signal
import time
import logging
import six
from collections import namedtuple
from z3 import *

from vargenerator import *
from ethereum_data import *
from basicblock import BasicBlock
from analysis import *
from test_evm.global_test_params import (TIME_OUT, UNKNOWN_INSTRUCTION,
                                         EXCEPTION, PICKLE_PATH)
from vulnerability import CallStack, TimeDependency, MoneyConcurrency, Reentrancy, AssertionFailure, ParityMultisigBug2, IntegerUnderflow, IntegerOverflow
import global_params

log = logging.getLogger(__name__)

UNSIGNED_BOUND_NUMBER = 2**256 - 1
CONSTANT_ONES_159 = BitVecVal((1 << 160) - 1, 256)

Assertion = namedtuple('Assertion', ['pc', 'model'])
Underflow = namedtuple('Underflow', ['pc', 'model'])
Overflow = namedtuple('Overflow', ['pc', 'model'])

class Parameter:
    def __init__(self, **kwargs):
        attr_defaults = {
            "stack": [],
            "calls": [],
            "memory": [],
            "visited": [],
            "overflow_pcs": [],
            "mem": {},
            "analysis": {},
            "sha3_list": {},
            "global_state": {},
            "path_conditions_and_vars": {}
        }
        for (attr, default) in six.iteritems(attr_defaults):
            setattr(self, attr, kwargs.get(attr, default))

    def copy(self):
        _kwargs = custom_deepcopy(self.__dict__)
        return Parameter(**_kwargs)

# 初始化全局变量
def initGlobalVars():
    global g_src_map
    global solver
    # Z3 solver
    # Run Oyente in parallel
    if global_params.PARALLEL:
        t2 = Then('simplify', 'solve-eqs', 'smt')
        _t = Then('tseitin-cnf-core', 'split-clause')
        t1 = ParThen(_t, t2)
        solver = OrElse(t1, t2).solver()
    else:
        solver = Solver()

    solver.set("timeout", global_params.TIMEOUT)

    global MSIZE
    MSIZE = False

    global revertible_overflow_pcs
    revertible_overflow_pcs = set()

    global g_disasm_file
    with open(g_disasm_file, 'r') as f:
        disasm = f.read()
    if 'MSIZE' in disasm:
        MSIZE = True

    global g_timeout
    g_timeout = False

    global visited_pcs
    visited_pcs = set()

    global results
    if g_src_map:
        global start_block_to_func_sig
        start_block_to_func_sig = {}

        results = {
            'evm_code_coverage': '',
            'vulnerabilities': {
                'integer_underflow': [],
                'integer_overflow': [],
                'callstack': [],
                'money_concurrency': [],
                'time_dependency': [],
                'reentrancy': [],
                'assertion_failure': [],
                'parity_multisig_bug_2': [],
            }
        }
    else:
        results = {
            'evm_code_coverage': '',
            'vulnerabilities': {
                'integer_underflow': [],
                'integer_overflow': [],
                'callstack': False,
                'money_concurrency': False,
                'time_dependency': False,
                'reentrancy': False,
            }
        }

    global calls_affect_state
    calls_affect_state = {}

    # capturing the last statement of each basic block
    # 捕获每个基本块的最后一条语句
    global end_ins_dict
    end_ins_dict = {}

    # capturing all the instructions, keys are corresponding addresses
    # 捕获所有指令，key 是对应的地址
    global instructions
    instructions = {}

    # capturing the "jump type" of each basic block
    # 捕获每个基本块的“跳转类型”
    global jump_type
    jump_type = {}

    global vertices
    vertices = {}

    global edges
    edges = {}

    global visited_edges
    visited_edges = {}

    global money_flow_all_paths
    money_flow_all_paths = []

    global reentrancy_all_paths
    reentrancy_all_paths = []

    # store the path condition corresponding to each path in money_flow_all_paths
    # 将每条路径对应的路径条件存储在 money_flow_all_paths 中
    global path_conditions
    path_conditions = []

    global global_problematic_pcs
    global_problematic_pcs = {"money_concurrency_bug": [], "reentrancy_bug": [], "time_dependency_bug": [], "assertion_failure": [], "integer_underflow": [], "integer_overflow": []}

    # store global variables, e.g. storage, balance of all paths
    # 存储全局变量，例如 存储，所有路径的余额
    global all_gs
    all_gs = []

    global total_no_of_paths
    total_no_of_paths = 0

    global no_of_test_cases
    no_of_test_cases = 0

    # to generate names for symbolic variables
    # 为符号变量生成名称
    global gen
    gen = Generator()

    global data_source
    if global_params.USE_GLOBAL_BLOCKCHAIN:
        data_source = EthereumData()

    global rfile
    if global_params.REPORT_MODE:
        rfile = open(g_disasm_file + '.report', 'w')

def is_testing_evm():
    return global_params.UNIT_TEST != 0

def compare_storage_and_gas_unit_test(global_state, analysis):
    unit_test = pickle.load(open(PICKLE_PATH, 'rb'))
    test_status = unit_test.compare_with_symExec_result(global_state, analysis)
    exit(test_status)

def change_format():
    with open(g_disasm_file) as disasm_file:
        file_contents = disasm_file.readlines()
        i = 0
        # 移除第一行字符串前后的换行符
        firstLine = file_contents[0].strip('\n')
        for line in file_contents:
            line = line.replace('SELFDESTRUCT', 'SUICIDE')
            line = line.replace('Missing opcode 0xfd', 'REVERT')
            line = line.replace('Missing opcode 0xfe', 'ASSERTFAIL')
            line = line.replace('Missing opcode', 'INVALID')
            line = line.replace(':', '')
            lineParts = line.split(' ')
            try: # removing initial zeroes
                lineParts[0] = str(int(lineParts[0]))

            except:
                lineParts[0] = lineParts[0]
            lineParts[-1] = lineParts[-1].strip('\n')
            try: # adding arrow if last is a number
                lastInt = lineParts[-1]
                if(int(lastInt, 16) or int(lastInt, 16) == 0) and len(lineParts) > 2:
                    lineParts[-1] = "=>"
                    lineParts.append(lastInt)
            except Exception:
                pass
            file_contents[i] = ' '.join(lineParts)
            i = i + 1
        file_contents[0] = firstLine
        file_contents[-1] += '\n'

    with open(g_disasm_file, 'w') as disasm_file:
        disasm_file.write("\n".join(file_contents))

# tokenize 是一个词汇扫描器，你可以看到每个词或者字符是什么类型的
#   其中所有的运算符，分隔符和 ellipsis 都会被标记成 OP 类型。
#   下面的 generate_tokens() 接受的参数必须是一个 readline，生成器会生成 5 个元素的具名元祖，内容分别是：
#       type：令牌类型
#       string：被令牌的字符串
#       指定令牌在源中开始的行和列的 2 元组 (srow, scol) 
#       指定令牌在源中结束的行和列的 2 元组 (erow, ecol) ；
#       line：所传递的行（最后一个元组项）是 实际的 行
#   其中还有一个属性 exact_type 标记了类型为 OP 词的确切操作类型。
#   可以在 collect_vertices 函数中看到对这个对象的调用。
def build_cfg_and_analyze():
    change_format()
    with open(g_disasm_file, 'r') as disasm_file:
        disasm_file.readline()  # Remove first line
        tokens = tokenize.generate_tokens(disasm_file.readline)
        collect_vertices(tokens)
        construct_bb()
        construct_static_edges()
        # 跳跃目标是动态构建的
        full_sym_exec()  # jump targets are constructed on the fly


def print_cfg():
    for block in vertices.values():
        block.display()
    log.debug(str(edges))


# positions 格式:{{'begin': 27, 'end': 141, 'name': 'DUP2'}, {'begin': 27, 'end': 141, 'name': 'SWAP1'}}
# name 为 “PUSH”时 还有个 value {'begin': 27, 'end': 141, 'name': 'PUSH', 'value': '20'}
def mapping_push_instruction(current_line_content, current_ins_address, idx, positions, length):
    global g_src_map

    while (idx < length):
        if not positions[idx]:
            return idx + 1
        name = positions[idx]['name']
        if name.startswith("tag"):
            idx += 1
        else:
            if name.startswith("PUSH"):
                if name == "PUSH":
                    value = positions[idx]['value']
                    instr_value = current_line_content.split(" ")[1]
                    if int(value, 16) == int(instr_value, 16):
                        g_src_map.instr_positions[current_ins_address] = g_src_map.positions[idx]
                        idx += 1
                        break;
                    else:
                        raise Exception("Source map error")
                else:
                    g_src_map.instr_positions[current_ins_address] = g_src_map.positions[idx]
                    idx += 1
                    break;
            else:
                raise Exception("Source map error")
    return idx

def mapping_non_push_instruction(current_line_content, current_ins_address, idx, positions, length):
    global g_src_map

    while (idx < length):
        if not positions[idx]:
            return idx + 1
        name = positions[idx]['name']
        if name.startswith("tag"):
            idx += 1
        else:
            instr_name = current_line_content.split(" ")[0]
            if name == instr_name or name == "INVALID" and instr_name == "ASSERTFAIL" or name == "KECCAK256" and instr_name == "SHA3" or name == "SELFDESTRUCT" and instr_name == "SUICIDE":
                g_src_map.instr_positions[current_ins_address] = g_src_map.positions[idx]
                idx += 1
                break;
            else:
                raise RuntimeError(F"Source map error, unknown name({name}) or instr_name({instr_name})")
    return idx

# 1. Parse the disassembled file
# 2. Then identify each basic block (i.e. one-in, one-out)
# 3. Store them in vertices
# 这个函数主要做的有：
#   1. 解析汇编文件
#   2. 判断区分不同的基础区块
#   3. 把他们存在顶点中
# 这个循环的主要作用就是将 block 添加到顶点中[重要]:
#   1. 通过解析出来的 token 类型，这个循环进行不同的操作；例如 tok_type 为 NAME 时，就把对 tok_string 做判断。解析出来是 PUSH 之后，则会让 wait_for_push 设置为 True。
#   2. 当读取该行结束之后，会调用一个 mapping_push_instruction，把 g_src_map.position 内的指令放入 g_src_map.instr_positions。
#   3. 同时全局变量 end_ins_dict 记录的是每个基本块的最后一条语句
#   4. 全局变量 instructions 负责记录指令。
#   5. 全局变量 jump_type 负责记录分支的类型和位置。
def collect_vertices(tokens):
    global g_src_map
    if g_src_map:
        idx = 0
        positions = g_src_map.positions
        length = len(positions)
    global end_ins_dict
    global instructions
    global jump_type

    current_ins_address = 0 # pc
    last_ins_address = 0
    is_new_line = True  # 新行标识
    current_block = 0
    current_line_content = ""
    wait_for_push = False   # PUSH 后为 True
    is_new_block = False

    # tok_type:'number' tok_string:'0000' 不是'0000c'，需在 change_format() 中更改
    # NUMBER==2,NAME==1,NEWLINE==4
    # 0 PUSH1 => 0x60
    # 2 0 (1, 0) 0 PUSH1 => 0x60
    # tok_type, tok_string, (srow, scol), _, line_number
    for tok_type, tok_string, (srow, scol), _, line_number in tokens:
        # 对 PUSH 后的值进行处理，向 instructions 中插入当前指令
        if wait_for_push is True:
            push_val = ""
            for ptok_type, ptok_string, _, _, _ in tokens:
                if ptok_type == NEWLINE:
                    is_new_line = True
                    current_line_content += push_val + ' '
                    instructions[current_ins_address] = current_line_content
                    idx = mapping_push_instruction(current_line_content, current_ins_address, idx, positions, length) if g_src_map else None
                    log.debug(current_line_content)
                    current_line_content = ""
                    wait_for_push = False
                    break
                try:
                    int(ptok_string, 16)
                    push_val += ptok_string
                except ValueError:
                    pass

            continue
        # 寻找行号
        elif is_new_line is True and tok_type == NUMBER:  # looking for a line number
            last_ins_address = current_ins_address
            try:
                current_ins_address = int(tok_string)
            except ValueError:
                log.critical("ERROR when parsing row %d col %d", srow, scol)
                quit()
            is_new_line = False
            if is_new_block:
                current_block = current_ins_address # 新块的起始 pc
                is_new_block = False
            continue
        elif tok_type == NEWLINE:   # /n
            is_new_line = True
            log.debug(current_line_content)
            instructions[current_ins_address] = current_line_content
            # if len(current_line_content.split(' ')) == 2:
            #     current_line_content = current_line_content.split(' ')[1]
            idx = mapping_non_push_instruction(current_line_content, current_ins_address, idx, positions, length) if g_src_map else None
            current_line_content = ""
            continue
        elif tok_type == NAME:
            if tok_string == "JUMPDEST":
                if last_ins_address not in end_ins_dict:
                    end_ins_dict[current_block] = last_ins_address
                current_block = current_ins_address
                is_new_block = False
            elif tok_string == "STOP" or tok_string == "RETURN" or tok_string == "SUICIDE" or tok_string == "REVERT" or tok_string == "ASSERTFAIL":
                jump_type[current_block] = "terminal"
                end_ins_dict[current_block] = current_ins_address
            elif tok_string == "JUMP":
                jump_type[current_block] = "unconditional"
                end_ins_dict[current_block] = current_ins_address
                is_new_block = True
            elif tok_string == "JUMPI":
                jump_type[current_block] = "conditional"
                end_ins_dict[current_block] = current_ins_address
                is_new_block = True
            elif tok_string.startswith('PUSH', 0):
                wait_for_push = True
            is_new_line = False
        if tok_string != "=" and tok_string != ">":
        # if tok_string != "=" and tok_string != ">" and not(tok_string >= "a" and tok_string <= "f"):
            current_line_content += tok_string + " "

    # 结束时给最后一个赋值
    if current_block not in end_ins_dict:
        log.debug("current block: %d", current_block)
        log.debug("last line: %d", current_ins_address)
        end_ins_dict[current_block] = current_ins_address

    # 结束时给最后一个赋值
    if current_block not in jump_type:
        jump_type[current_block] = "terminal"

    # 结束时给其他块的跳转类型赋值
    for key in end_ins_dict:
        if key not in jump_type:
            jump_type[key] = "falls_to" # ?

# BasicBlock
# 这个函数的主要作用是构建一个没有链接的 vertices 和 edges。
# vertices 内存储着 BasicBlock，其内部存有该块的指令。
# edge 则存有节点 key-value值，例如 {[0,[]],[13,[]],...}。
# 节点内的值会在之后的 construct_static_edges() 补全。

# 基本块是一个最大化的指令序列，程序执行只能从这个序列的第一条指令，从这个序列的最后一条指令退出。
# 构建基本块的三个原则：
#   1. 遇到程序、子程序的第一条指令或语句，结束当前基本块，并将该语句作为一个新块的第一条语句。
#   2. 遇到跳转语句、分支语句、循环语句、将该语句作为当前块的最后一条语句，并结束当前块。
#   3. 遇到其他语句直接将其加入当前基本块。
def construct_bb():
    global vertices
    global edges
    sorted_addresses = sorted(instructions.keys())
    size = len(sorted_addresses)
    for key in end_ins_dict:
        end_address = end_ins_dict[key]
        block = BasicBlock(key, end_address)
        if key not in instructions:
            continue
        block.add_instruction(instructions[key])
        i = sorted_addresses.index(key) + 1
        while i < size and sorted_addresses[i] <= end_address:
            block.add_instruction(instructions[sorted_addresses[i]])
            i += 1
        block.set_block_type(jump_type[key])
        vertices[key] = block
        edges[key] = []

def construct_static_edges():
    add_falls_to()  # these edges are static


# 这个函数的作用就是在 jump_type 不是 terminal 或者 unconditional 的时候，把节点的 target 赋给 edges 和 vertices。
def add_falls_to():
    global vertices
    global edges
    key_list = sorted(jump_type.keys()) # falls_to 都在后面，会影响边的构建，需要进行 pc 排序
    length = len(key_list)
    for i, key in enumerate(key_list):
        if jump_type[key] != "terminal" and jump_type[key] != "unconditional" and i+1 < length: # 即为"falls_to"/"conditional"
            target = key_list[i+1]
            edges[key].append(target)   # 简单的设置为下一个块的起始 pc
            vertices[key].set_falls_to(target)  # 简单的设置为下一个块的起始 pc

# path_conditions_and_vars 指的是在 block 跳转的时候可能会调用的变量和需要处理的约束。
# global_state 是在正常 block 执行的时候就有可能会调用的变量。
def get_init_global_state(path_conditions_and_vars):
    global_state = {"balance" : {}, "pc": 0}
    init_is = init_ia = deposited_value = sender_address = receiver_address = gas_price = origin = currentCoinbase = currentNumber = currentDifficulty = currentGasLimit = callData = None

    # INPUT_STATE 指的是假设链的状态，这里的默认值是 False
    if global_params.INPUT_STATE:
        with open('state.json') as f:
            state = json.loads(f.read())
            if state["Is"]["balance"]:
                init_is = int(state["Is"]["balance"], 16)
            if state["Ia"]["balance"]:
                init_ia = int(state["Ia"]["balance"], 16)
            if state["exec"]["value"]:
                deposited_value = 0
            if state["Is"]["address"]:
                sender_address = int(state["Is"]["address"], 16)
            if state["Ia"]["address"]:
                receiver_address = int(state["Ia"]["address"], 16)
            if state["exec"]["gasPrice"]:
                gas_price = int(state["exec"]["gasPrice"], 16)
            if state["exec"]["origin"]:
                origin = int(state["exec"]["origin"], 16)
            if state["env"]["currentCoinbase"]:
                currentCoinbase = int(state["env"]["currentCoinbase"], 16)
            if state["env"]["currentNumber"]:
                currentNumber = int(state["env"]["currentNumber"], 16)
            if state["env"]["currentDifficulty"]:
                currentDifficulty = int(state["env"]["currentDifficulty"], 16)
            if state["env"]["currentGasLimit"]:
                currentGasLimit = int(state["env"]["currentGasLimit"], 16)

    # for some weird reason these 3 vars are stored in path_conditions insteaad of global_state
    # 出于某种奇怪的原因，这 3 个变量存储在 path_conditions 而不是 global_state 中
    else:
        # 定义 BitVec 型的变量，作为 CALLDATASIZE 中可能传入的变量
        sender_address = BitVec("Is", 256)
        receiver_address = BitVec("Ia", 256)
        deposited_value = BitVec("Iv", 256)
        init_is = BitVec("init_Is", 256)
        init_ia = BitVec("init_Ia", 256)

    # 对 path_conditions_and_vars 进行赋值
    path_conditions_and_vars["Is"] = sender_address
    path_conditions_and_vars["Ia"] = receiver_address
    path_conditions_and_vars["Iv"] = deposited_value

    # 先设定约束，deposited_value 需要大于 0
    constraint = (deposited_value >= BitVecVal(0, 256))
    path_conditions_and_vars["path_condition"].append(constraint)
    # 发送者的余额要大于 deposited_value 才能发
    constraint = (init_is >= deposited_value)
    path_conditions_and_vars["path_condition"].append(constraint)
    # 接收者的值需要大于 0
    constraint = (init_ia >= BitVecVal(0, 256))
    path_conditions_and_vars["path_condition"].append(constraint)

    # update the balances of the "caller" and "callee"
    # 更新发送者和接受者的余额
    global_state["balance"]["Is"] = (init_is - deposited_value)
    global_state["balance"]["Ia"] = (init_ia + deposited_value)

    # 下面的值原先都为 None，由 gen_xxx 指定一个变量名
    # 如 gas_price 就被制定了变量名 Ip
    if not gas_price:
        new_var_name = gen.gen_gas_price_var()  # Ip
        gas_price = BitVec(new_var_name, 256)
        path_conditions_and_vars[new_var_name] = gas_price

    if not origin:
        new_var_name = gen.gen_origin_var() # Io
        origin = BitVec(new_var_name, 256)
        path_conditions_and_vars[new_var_name] = origin

    if not currentCoinbase:
        new_var_name = "IH_c"
        currentCoinbase = BitVec(new_var_name, 256)
        path_conditions_and_vars[new_var_name] = currentCoinbase

    if not currentNumber:
        new_var_name = "IH_i"
        currentNumber = BitVec(new_var_name, 256)
        path_conditions_and_vars[new_var_name] = currentNumber

    if not currentDifficulty:
        new_var_name = "IH_d"
        currentDifficulty = BitVec(new_var_name, 256)
        path_conditions_and_vars[new_var_name] = currentDifficulty

    if not currentGasLimit:
        new_var_name = "IH_l"
        currentGasLimit = BitVec(new_var_name, 256)
        path_conditions_and_vars[new_var_name] = currentGasLimit

    new_var_name = "IH_s"
    currentTimestamp = BitVec(new_var_name, 256)
    path_conditions_and_vars[new_var_name] = currentTimestamp

    # the state of the current current contract
    if "Ia" not in global_state:
        global_state["Ia"] = {}
    global_state["miu_i"] = 0
    global_state["value"] = deposited_value
    global_state["sender_address"] = sender_address
    global_state["receiver_address"] = receiver_address
    global_state["gas_price"] = gas_price
    global_state["origin"] = origin
    global_state["currentCoinbase"] = currentCoinbase
    global_state["currentTimestamp"] = currentTimestamp
    global_state["currentNumber"] = currentNumber
    global_state["currentDifficulty"] = currentDifficulty
    global_state["currentGasLimit"] = currentGasLimit

    return global_state

# 获取函数的 pc 和签名
# 遍历整个指令集，找到起始为 PUSH4，且后一位是 EQ 且再后一位是 PUSH的，
# 然后 start_block_to_func_sig 就记录下 func_sig。
# 这个是在收集函数的 id，因为 PUSH4 后面的那个 x 其实就是函数的 id，收集函数其实就可以认为在收集 block 的逻辑。
def get_start_block_to_func_sig():
    state = 0
    func_sig = None
    for pc, instr in six.iteritems(instructions):
        if state == 0 and instr.startswith('PUSH4'):
            state += 1
            func_sig = instr.split(' ')[1][2:]
        elif state == 1 and instr.startswith('EQ'):
            state += 1
        elif state == 2 and instr.startswith('PUSH'):
            state = 0
            pc = instr.split(' ')[1]
            pc = int(pc, 16)
            start_block_to_func_sig[pc] = func_sig
        else:
            state = 0
    return start_block_to_func_sig

# 这一个函数涉及到的是 oyente 框架最关键的内容，就是对于合约安全的各种检测
# 主要的步骤就是
#   1. 获取全部参数，存入 param 变量。
#   2. 使用 sym_exec_block 对所有的块进行深度优先遍历。
#   3. 进行 symbolic execution，对 EVM 的栈的内容进行模仿，并且使用求解器约束参数的范围。
#   4. 对不同的可能出现的问题进行逻辑判断，返回不同的异常信息——例如求解器的约束对没有限制的整数进行范围的判定等。
def full_sym_exec():
    # executing, starting from beginning 执行，从头开始
    path_conditions_and_vars = {"path_condition" : []}
    global_state = get_init_global_state(path_conditions_and_vars)
    analysis = init_analysis()
    params = Parameter(path_conditions_and_vars=path_conditions_and_vars, global_state=global_state, analysis=analysis)
    # 如果输入的是字节码就没有这个步骤，因为没有 g_src_map
    if g_src_map:
        start_block_to_func_sig = get_start_block_to_func_sig() # 获取函数的 pc 和签名
    return sym_exec_block(params, 0, 0, 0, -1, 'fallback')  # 从起始地址符号执行一个块，内含递归符号执行


# Symbolically executing a block from the start address
# 现在实际上已经获得了 block 和边了，但是对于 block 之间连续的逻辑，我们需要做一个深度优先遍历
# 所以 sys_exec_block 会是一个递归函数
def sym_exec_block(params, block, pre_block, depth, func_call, current_func_name):
    global solver
    global visited_edges
    global money_flow_all_paths
    global path_conditions
    global global_problematic_pcs
    global all_gs
    global results
    global g_src_map

    # 对已经访问过的进行标记
    visited = params.visited
    # 作为符号化执行的虚拟出来的栈
    stack = params.stack
    # gas_memory
    mem = params.mem
    # 符号化执行虚拟出来的内存
    memory = params.memory
    # 这是在上面定义的一些链的常量(主要是 z3)
    global_state = params.global_state
    # ？？？
    sha3_list = params.sha3_list
    # 用于填充 block 与 block 之间的中间条件以及变量
    path_conditions_and_vars = params.path_conditions_and_vars
    # 代表着分析结果
    analysis = params.analysis
    calls = params.calls
    overflow_pcs = params.overflow_pcs

    Edge = namedtuple("Edge", ["v1", "v2"]) # 具名元组 Factory Function for tuples is used as dictionary key
    if block < 0:
        log.debug("UNKNOWN JUMP ADDRESS. TERMINATING THIS PATH")
        return ["ERROR"]

    log.debug("Reach block address %d \n", block)

    if g_src_map:
        # 如果 block 在起始 block，或者在函数清单内
        # 如果是函数块，则得到 current_func_name
        if block in start_block_to_func_sig:
            func_sig = start_block_to_func_sig[block]
            current_func_name = g_src_map.sig_to_func[func_sig]
            pattern = r'(\w[\w\d_]*)\((.*)\)$'
            match = re.match(pattern, current_func_name)
            if match:
                current_func_name =  list(match.groups())[0]

    # 构建当前边(前 block 起始 pc, 当前 block 起始 pc)
    current_edge = Edge(pre_block, block)
    # 更新当前边的访问次数
    if current_edge in visited_edges:   
        updated_count_number = visited_edges[current_edge] + 1
        visited_edges.update({current_edge: updated_count_number})
    # 如果当前的 edges 没有被 visited 过，则更新为 1
    else:
        visited_edges.update({current_edge: 1})

    # 如果这一个 edges 大于了循环的最高限制
    if visited_edges[current_edge] > global_params.LOOP_LIMIT:
        log.debug("Overcome a number of loop limit. Terminating this path ...")
        return stack

    # 计算当前的 gas，如果大于了限制，则返回 stack
    current_gas_used = analysis["gas"]  # 获取当前已消耗的 gas
    if current_gas_used > global_params.GAS_LIMIT:  # 处理 gas 超过上限的情况
        log.debug("Run out of gas. Terminating this path ... ")
        return stack

    # Execute every instruction, one at a time
    # 执行每个指令，一次一个
    try:
        # 获取当前 block 所有的指令
        block_ins = vertices[block].get_instructions()
    except KeyError:
        log.debug("This path results in an exception, possibly an invalid jump address")
        return ["ERROR"]

    # 循环执行当前 block 的指令，所有的符号化执行的内容全部都在 sym_exec_ins 函数中
    for instr in block_ins: # 符号执行块中的每一个指令
        sym_exec_ins(params, block, instr, func_call, current_func_name)

    # Mark that this basic block in the visited blocks
    # 在已访问的块中标记此基本块
    visited.append(block)
    depth += 1

    # 块指令执行完后(有块的指令分析结果)，添加 money 分析和时间戳依赖分析结果
    # 把之前添加的一些 bug 结果进行汇总
    reentrancy_all_paths.append(analysis["reentrancy_bug"])
    if analysis["money_flow"] not in money_flow_all_paths:
        global_problematic_pcs["money_concurrency_bug"].append(analysis["money_concurrency_bug"])
        money_flow_all_paths.append(analysis["money_flow"])
        path_conditions.append(path_conditions_and_vars["path_condition"])
        global_problematic_pcs["time_dependency_bug"].append(analysis["time_dependency_bug"])
        all_gs.append(copy_global_values(global_state))

    # Go to next Basic Block(s)
    # 然后前往下一个 block
    # 如果这个 block 的类型是 terminal 或者 递归的深度大于最大深度限制了
    if jump_type[block] == "terminal" or depth > global_params.DEPTH_LIMIT:
        global total_no_of_paths
        global no_of_test_cases

        total_no_of_paths += 1

        # 如果要求生成测试用例，则..
        if global_params.GENERATE_TEST_CASES:
            try:
                model = solver.model()
                no_of_test_cases += 1
                filename = "test%s.otest" % no_of_test_cases
                with open(filename, 'w') as f:
                    for variable in model.decls():
                        f.write(str(variable) + " = " + str(model[variable]) + "\n")
                if os.stat(filename).st_size == 0:
                    os.remove(filename)
                    no_of_test_cases -= 1
            except Exception as e:
                pass

        log.debug("TERMINATING A PATH ...")
        # 显示结果
        display_analysis(analysis)
        if is_testing_evm():
            compare_storage_and_gas_unit_test(global_state, analysis)

    # 如果是没有条件语句的跳转
    elif jump_type[block] == "unconditional":  # executing "JUMP"
        # 继任者 = 当前 block 跳转的目标
        successor = vertices[block].get_jump_target()
        # 新的参数
        new_params = params.copy()
        # 获取新的 program counter
        new_params.global_state["pc"] = successor
        if g_src_map:
            # 通过 program counter 和之前的 source map 获取源码
            source_code = g_src_map.get_source_code(global_state['pc'])
            if source_code in g_src_map.func_call_names:
                func_call = global_state['pc']
        sym_exec_block(new_params, successor, block, depth, func_call, current_func_name)
    # 如果跳转类型是 fall to，即什么都不做
    elif jump_type[block] == "falls_to":  # just follow to the next basic block
        successor = vertices[block].get_falls_to()
        new_params = params.copy()
        new_params.global_state["pc"] = successor
        sym_exec_block(new_params, successor, block, depth, func_call, current_func_name)
    # 如果跳转类型是条件跳转
    elif jump_type[block] == "conditional":  # executing "JUMPI"

        # A choice point, we proceed with depth first search
        # 则先获取分支的表达式
        branch_expression = vertices[block].get_branch_expression()

        log.debug("Branch expression: " + str(branch_expression))
        # 设置 solver 的一个边界
        solver.push()  # SET A BOUNDARY FOR SOLVER
        # 给 solver 增加一个边界表达式
        solver.add(branch_expression)
        # 下面的这一部分是对 JUMPI 的条件为 true 检查
        try:
            # 如果 solver 检测处有不满足的地方
            if solver.check() == unsat:
                # 则返回有不可解的路径
                log.debug("INFEASIBLE PATH DETECTED")
            else:
                # 则跳转到下一个目标
                left_branch = vertices[block].get_jump_target()
                new_params = params.copy()
                new_params.global_state["pc"] = left_branch
                # 在 path_... 的变量中加入这一个分支的 expression
                new_params.path_conditions_and_vars["path_condition"].append(branch_expression)
                last_idx = len(new_params.path_conditions_and_vars["path_condition"]) - 1
                # 定位上一个 inx 发生的 bug 并保存
                new_params.analysis["time_dependency_bug"][last_idx] = global_state["pc"]
                # 继续进入下一个 block
                sym_exec_block(new_params, left_branch, block, depth, func_call, current_func_name)
        except TimeoutError:
            raise
        except Exception as e:
            if global_params.DEBUG_MODE:
                traceback.print_exc()

        # 下面的条件是对 JUMPI 为 false 条件的检查
        solver.pop()  # POP SOLVER CONTEXT

        solver.push()  # SET A BOUNDARY FOR SOLVER
        negated_branch_expression = Not(branch_expression)
        solver.add(negated_branch_expression)

        log.debug("Negated branch expression: " + str(negated_branch_expression))   # 否定

        try:
            if solver.check() == unsat:
                # Note that this check can be optimized. I.e. if the previous check succeeds,
                # no need to check for the negated condition, but we can immediately go into
                # the else branch
                log.debug("INFEASIBLE PATH DETECTED")
            else:
                right_branch = vertices[block].get_falls_to()
                new_params = params.copy()
                new_params.global_state["pc"] = right_branch
                new_params.path_conditions_and_vars["path_condition"].append(negated_branch_expression)
                last_idx = len(new_params.path_conditions_and_vars["path_condition"]) - 1
                new_params.analysis["time_dependency_bug"][last_idx] = global_state["pc"]
                sym_exec_block(new_params, right_branch, block, depth, func_call, current_func_name)
        except TimeoutError:
            raise
        except Exception as e:
            if global_params.DEBUG_MODE:
                traceback.print_exc()
        solver.pop()  # POP SOLVER CONTEXT
        updated_count_number = visited_edges[current_edge] - 1
        visited_edges.update({current_edge: updated_count_number})
    else:
        updated_count_number = visited_edges[current_edge] - 1
        visited_edges.update({current_edge: updated_count_number})
        raise Exception('Unknown Jump-Type')


# Symbolically executing an instruction
# 象征性地执行一条指令
def sym_exec_ins(params, block, instr, func_call, current_func_name):
    global MSIZE
    global visited_pcs
    global solver
    global vertices
    global edges
    global g_src_map
    global calls_affect_state
    global data_source

    stack = params.stack
    mem = params.mem
    memory = params.memory
    global_state = params.global_state
    sha3_list = params.sha3_list
    path_conditions_and_vars = params.path_conditions_and_vars
    analysis = params.analysis
    calls = params.calls
    overflow_pcs = params.overflow_pcs

    visited_pcs.add(global_state["pc"])

    instr_parts = str.split(instr, ' ')
    opcode = instr_parts[0]

    if opcode == "INVALID":
        return
    elif opcode == "ASSERTFAIL":
        if g_src_map:
            source_code = g_src_map.get_source_code(global_state['pc'])
            source_code = source_code.split("(")[0]
            func_name = source_code.strip()
            if check_sat(solver, False) != unsat:
                model = solver.model()
            if func_name == "assert":
                global_problematic_pcs["assertion_failure"].append(Assertion(global_state["pc"], model))
            elif func_call != -1:
                global_problematic_pcs["assertion_failure"].append(Assertion(func_call, model))
        return

    # collecting the analysis result by calling this skeletal function
    # 通过调用这个骨架函数来收集分析结果
    # this should be done before symbolically executing the instruction,
    # 这应该在符号执行指令之前完成
    # since SE will modify the stack and mem
    # 因为符号执行将修改 stack 和 mem
    update_analysis(analysis, opcode, stack, mem, global_state, path_conditions_and_vars, solver)

    # 如果确认存在重入则将 pc 添加到 global_problematic_pcs["reentrancy_bug"]
    if opcode == "CALL" and analysis["reentrancy_bug"] and analysis["reentrancy_bug"][-1]:
        global_problematic_pcs["reentrancy_bug"].append(global_state["pc"])

    log.debug("==============================")
    log.debug("EXECUTING: " + instr)

    #
    # 以下是指令执行
    #
    #  0s: Stop and Arithmetic Operations
    #
    if opcode == "STOP":
        global_state["pc"] = global_state["pc"] + 1
        return
    elif opcode == "ADD":
        if len(stack) > 1:
            global_state["pc"] = global_state["pc"] + 1
            first = stack.pop(0)
            second = stack.pop(0)
            # Type conversion is needed when they are mismatched
            if isReal(first) and isSymbolic(second):
                first = BitVecVal(first, 256)
                computed = first + second
            elif isSymbolic(first) and isReal(second):
                second = BitVecVal(second, 256)
                computed = first + second
            else:
                # both are real and we need to manually modulus with 2 ** 256
                # if both are symbolic z3 takes care of modulus automatically
                computed = (first + second) % (2 ** 256)
            computed = simplify(computed) if is_expr(computed) else computed

            check_revert = False
            if jump_type[block] == 'conditional':
                jump_target = vertices[block].get_jump_target()
                falls_to = vertices[block].get_falls_to()
                # 检测 jump_target 块的指令和 falls_to 块的指令中是否有 REVERT 指令
                check_revert = any([True for instruction in vertices[jump_target].get_instructions() if instruction.startswith('REVERT')])
                if not check_revert:
                    check_revert = any([True for instruction in vertices[falls_to].get_instructions() if instruction.startswith('REVERT')])

            # integer_overflow 检测，有 REVERT 指令则不需要检测，会撤销，不会导致 integer_overflow
            if jump_type[block] != 'conditional' or not check_revert:
                if not isAllReal(computed, first):
                    solver.push()
                    solver.add(UGT(first, computed))
                    # 如果 first > computed 可满足，即两数相加后反而小于第一个数，则出现了 integer_overflow
                    if check_sat(solver) == sat:
                        global_problematic_pcs['integer_overflow'].append(Overflow(global_state['pc'] - 1, solver.model()))
                        overflow_pcs.append(global_state['pc'] - 1)
                    solver.pop()

            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    # 难道相乘就不会出现 integer_overflow 么？不严谨吧。。。
    elif opcode == "MUL":
        if len(stack) > 1:
            global_state["pc"] = global_state["pc"] + 1
            first = stack.pop(0)
            second = stack.pop(0)
            if isReal(first) and isSymbolic(second):
                first = BitVecVal(first, 256)
            elif isSymbolic(first) and isReal(second):
                second = BitVecVal(second, 256)
            computed = first * second & UNSIGNED_BOUND_NUMBER
            computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')

    # integer_underflow 检测
    elif opcode == "SUB":
        if len(stack) > 1:
            global_state["pc"] = global_state["pc"] + 1
            first = stack.pop(0)
            second = stack.pop(0)
            if isReal(first) and isSymbolic(second):
                first = BitVecVal(first, 256)
                computed = first - second
            elif isSymbolic(first) and isReal(second):
                second = BitVecVal(second, 256)
                computed = first - second
            else:
                computed = (first - second) % (2 ** 256)
            computed = simplify(computed) if is_expr(computed) else computed

            check_revert = False
            if jump_type[block] == 'conditional':
                jump_target = vertices[block].get_jump_target()
                falls_to = vertices[block].get_falls_to()
                check_revert = any([True for instruction in vertices[jump_target].get_instructions() if instruction.startswith('REVERT')])
                if not check_revert:
                    check_revert = any([True for instruction in vertices[falls_to].get_instructions() if instruction.startswith('REVERT')])

            if jump_type[block] != 'conditional' or not check_revert:
                if not isAllReal(first, second):
                    solver.push()
                    solver.add(UGT(second, first))
                    if check_sat(solver) == sat:
                        global_problematic_pcs['integer_underflow'].append(Underflow(global_state['pc'] - 1, solver.model()))
                    solver.pop()

            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    
    # 除 0 处理
    elif opcode == "DIV":
        if len(stack) > 1:
            global_state["pc"] = global_state["pc"] + 1
            first = stack.pop(0)
            second = stack.pop(0)
            if isAllReal(first, second):
                if second == 0:
                    computed = 0
                else:
                    first = to_unsigned(first)
                    second = to_unsigned(second)
                    computed = first / second
            else:
                first = to_symbolic(first)
                second = to_symbolic(second)
                solver.push()
                solver.add( Not (second == 0) )
                if check_sat(solver) == unsat:
                    computed = 0
                else:
                    computed = UDiv(first, second)
                solver.pop()
            computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "SDIV":
        if len(stack) > 1:
            global_state["pc"] = global_state["pc"] + 1
            first = stack.pop(0)
            second = stack.pop(0)
            if isAllReal(first, second):
                first = to_signed(first)
                second = to_signed(second)
                if second == 0:
                    computed = 0
                elif first == -2**255 and second == -1:
                    computed = -2**255
                else:
                    sign = -1 if (first / second) < 0 else 1
                    computed = sign * ( abs(first) / abs(second) )
            else:
                first = to_symbolic(first)
                second = to_symbolic(second)
                solver.push()
                solver.add(Not(second == 0))
                if check_sat(solver) == unsat:
                    computed = 0
                else:
                    solver.push()
                    solver.add( Not( And(first == -2**255, second == -1 ) ))
                    if check_sat(solver) == unsat:
                        computed = -2**255
                    else:
                        solver.push()
                        solver.add(first / second < 0)
                        sign = -1 if check_sat(solver) == sat else 1
                        z3_abs = lambda x: If(x >= 0, x, -x)
                        first = z3_abs(first)
                        second = z3_abs(second)
                        computed = sign * (first / second)
                        solver.pop()
                    solver.pop()
                solver.pop()
            computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "MOD":
        if len(stack) > 1:
            global_state["pc"] = global_state["pc"] + 1
            first = stack.pop(0)
            second = stack.pop(0)
            if isAllReal(first, second):
                if second == 0:
                    computed = 0
                else:
                    first = to_unsigned(first)
                    second = to_unsigned(second)
                    computed = first % second & UNSIGNED_BOUND_NUMBER

            else:
                first = to_symbolic(first)
                second = to_symbolic(second)

                solver.push()
                solver.add(Not(second == 0))
                if check_sat(solver) == unsat:
                    # it is provable that second is indeed equal to zero
                    computed = 0
                else:
                    computed = URem(first, second)
                solver.pop()

            computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "SMOD":
        if len(stack) > 1:
            global_state["pc"] = global_state["pc"] + 1
            first = stack.pop(0)
            second = stack.pop(0)
            if isAllReal(first, second):
                if second == 0:
                    computed = 0
                else:
                    first = to_signed(first)
                    second = to_signed(second)
                    sign = -1 if first < 0 else 1
                    computed = sign * (abs(first) % abs(second))
            else:
                first = to_symbolic(first)
                second = to_symbolic(second)

                solver.push()
                solver.add(Not(second == 0))
                if check_sat(solver) == unsat:
                    # it is provable that second is indeed equal to zero
                    computed = 0
                else:

                    solver.push()
                    solver.add(first < 0) # check sign of first element
                    sign = BitVecVal(-1, 256) if check_sat(solver) == sat \
                        else BitVecVal(1, 256)
                    solver.pop()

                    z3_abs = lambda x: If(x >= 0, x, -x)
                    first = z3_abs(first)
                    second = z3_abs(second)

                    computed = sign * (first % second)
                solver.pop()

            computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    # ADDMOD 也有可能出现 ADDMOD 吧？？？
    elif opcode == "ADDMOD":    # (a + b) % c
        if len(stack) > 2:
            global_state["pc"] = global_state["pc"] + 1
            first = stack.pop(0)
            second = stack.pop(0)
            third = stack.pop(0)

            if isAllReal(first, second, third):
                if third == 0:
                    computed = 0
                else:
                    computed = (first + second) % third
            else:
                first = to_symbolic(first)
                second = to_symbolic(second)
                solver.push()
                solver.add( Not(third == 0) )
                if check_sat(solver) == unsat:
                    computed = 0
                else:
                    first = ZeroExt(256, first)
                    second = ZeroExt(256, second)
                    third = ZeroExt(256, third)
                    computed = (first + second) % third
                    computed = Extract(255, 0, computed)
                solver.pop()
            computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "MULMOD":
        if len(stack) > 2:
            global_state["pc"] = global_state["pc"] + 1
            first = stack.pop(0)
            second = stack.pop(0)
            third = stack.pop(0)

            if isAllReal(first, second, third):
                if third == 0:
                    computed = 0
                else:
                    computed = (first * second) % third
            else:
                first = to_symbolic(first)
                second = to_symbolic(second)
                solver.push()
                solver.add( Not(third == 0) )
                if check_sat(solver) == unsat:
                    computed = 0
                else:
                    first = ZeroExt(256, first)
                    second = ZeroExt(256, second)
                    third = ZeroExt(256, third)
                    computed = URem(first * second, third)
                    computed = Extract(255, 0, computed)
                solver.pop()
            computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "EXP":
        if len(stack) > 1:
            global_state["pc"] = global_state["pc"] + 1
            base = stack.pop(0)
            exponent = stack.pop(0)
            # Type conversion is needed when they are mismatched
            if isAllReal(base, exponent):
                computed = pow(base, exponent, 2**256)
            else:
                # The computed value is unknown, this is because power is
                # not supported in bit-vector theory
                # 不支持幂操作，设为未知数
                new_var_name = gen.gen_arbitrary_var()  # some_var_*
                computed = BitVec(new_var_name, 256)
            computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "SIGNEXTEND":
        if len(stack) > 1:
            global_state["pc"] = global_state["pc"] + 1
            first = stack.pop(0)
            second = stack.pop(0)
            if isAllReal(first, second):
                if first >= 32 or first < 0:
                    computed = second
                else:
                    signbit_index_from_right = 8 * first + 7
                    if second & (1 << signbit_index_from_right):
                        computed = second | (2 ** 256 - (1 << signbit_index_from_right))
                    else:
                        computed = second & ((1 << signbit_index_from_right) - 1 )
            else:
                first = to_symbolic(first)
                second = to_symbolic(second)
                solver.push()
                solver.add( Not( Or(first >= 32, first < 0 ) ) )
                if check_sat(solver) == unsat:
                    computed = second
                else:
                    signbit_index_from_right = 8 * first + 7
                    solver.push()
                    solver.add(second & (1 << signbit_index_from_right) == 0)
                    if check_sat(solver) == unsat:
                        computed = second | (2 ** 256 - (1 << signbit_index_from_right))
                    else:
                        computed = second & ((1 << signbit_index_from_right) - 1)
                    solver.pop()
                solver.pop()
            computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    #
    #  10s: Comparison and Bitwise Logic Operations
    #
    elif opcode == "LT":
        if len(stack) > 1:
            global_state["pc"] = global_state["pc"] + 1
            first = stack.pop(0)
            second = stack.pop(0)
            if isAllReal(first, second):
                first = to_unsigned(first)
                second = to_unsigned(second)
                if first < second:
                    computed = 1
                else:
                    computed = 0
            else:
                computed = If(ULT(first, second), BitVecVal(1, 256), BitVecVal(0, 256))
            computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "GT":
        if len(stack) > 1:
            global_state["pc"] = global_state["pc"] + 1
            first = stack.pop(0)
            second = stack.pop(0)
            if isAllReal(first, second):
                first = to_unsigned(first)
                second = to_unsigned(second)
                if first > second:
                    computed = 1
                else:
                    computed = 0
            else:
                computed = If(UGT(first, second), BitVecVal(1, 256), BitVecVal(0, 256))
            computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "SLT":  # Not fully faithful to signed comparison
        if len(stack) > 1:
            global_state["pc"] = global_state["pc"] + 1
            first = stack.pop(0)
            second = stack.pop(0)
            if isAllReal(first, second):
                first = to_signed(first)
                second = to_signed(second)
                if first < second:
                    computed = 1
                else:
                    computed = 0
            else:
                computed = If(first < second, BitVecVal(1, 256), BitVecVal(0, 256))
            computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "SGT":  # Not fully faithful to signed comparison
        if len(stack) > 1:
            global_state["pc"] = global_state["pc"] + 1
            first = stack.pop(0)
            second = stack.pop(0)
            if isAllReal(first, second):
                first = to_signed(first)
                second = to_signed(second)
                if first > second:
                    computed = 1
                else:
                    computed = 0
            else:
                computed = If(first > second, BitVecVal(1, 256), BitVecVal(0, 256))
            computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "EQ":
        if len(stack) > 1:
            global_state["pc"] = global_state["pc"] + 1
            first = stack.pop(0)
            second = stack.pop(0)
            if isAllReal(first, second):
                if first == second:
                    computed = 1
                else:
                    computed = 0
            else:
                computed = If(first == second, BitVecVal(1, 256), BitVecVal(0, 256))
            computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "ISZERO":
        # Tricky: this instruction works on both boolean and integer,
        # when we have a symbolic expression, type error might occur
        # Currently handled by try and catch
        # 棘手：这条指令适用于布尔型和整数型，当我们有一个符号表达式时，可能会发生类型错误目前由 try 和 catch 处理
        if len(stack) > 0:
            global_state["pc"] = global_state["pc"] + 1
            first = stack.pop(0)
            if isReal(first):
                if first == 0:
                    computed = 1
                else:
                    computed = 0
            else:
                computed = If(first == 0, BitVecVal(1, 256), BitVecVal(0, 256))
            computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "AND":
        if len(stack) > 1:
            global_state["pc"] = global_state["pc"] + 1
            first = stack.pop(0)
            second = stack.pop(0)
            computed = first & second
            computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "OR":
        if len(stack) > 1:
            global_state["pc"] = global_state["pc"] + 1
            first = stack.pop(0)
            second = stack.pop(0)

            computed = first | second
            computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)

        else:
            raise ValueError('STACK underflow')
    elif opcode == "XOR":
        if len(stack) > 1:
            global_state["pc"] = global_state["pc"] + 1
            first = stack.pop(0)
            second = stack.pop(0)

            computed = first ^ second
            computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)

        else:
            raise ValueError('STACK underflow')
    elif opcode == "NOT":
        if len(stack) > 0:
            global_state["pc"] = global_state["pc"] + 1
            first = stack.pop(0)
            computed = (~first) & UNSIGNED_BOUND_NUMBER
            computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "BYTE":
        if len(stack) > 1:
            global_state["pc"] = global_state["pc"] + 1
            first = stack.pop(0)
            byte_index = 32 - first - 1
            second = stack.pop(0)

            if isAllReal(first, second):
                if first >= 32 or first < 0:
                    computed = 0
                else:
                    computed = second & (255 << (8 * byte_index))
                    computed = computed >> (8 * byte_index)
            else:
                first = to_symbolic(first)
                second = to_symbolic(second)
                solver.push()
                solver.add( Not (Or( first >= 32, first < 0 ) ) )
                if check_sat(solver) == unsat:
                    computed = 0
                else:
                    computed = second & (255 << (8 * byte_index))
                    computed = computed >> (8 * byte_index)
                solver.pop()
            computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    #
    # 20s: SHA3
    #
    elif opcode == "SHA3":
        if len(stack) > 1:
            global_state["pc"] = global_state["pc"] + 1
            s0 = stack.pop(0)
            s1 = stack.pop(0)
            if isAllReal(s0, s1):
                # simulate the hashing of sha3
                data = [str(x) for x in memory[s0: s0 + s1]]
                position = ''.join(data)
                position = re.sub('[\s+]', '', position)
                position = zlib.compress(six.b(position), 9)
                position = base64.b64encode(position)
                position = position.decode('utf-8', 'strict')
                if position in sha3_list:
                    stack.insert(0, sha3_list[position])
                else:
                    new_var_name = gen.gen_arbitrary_var()  # some_var_*
                    new_var = BitVec(new_var_name, 256)
                    sha3_list[position] = new_var
                    stack.insert(0, new_var)
            else:
                # push into the execution a fresh symbolic variable
                new_var_name = gen.gen_arbitrary_var()  # some_var_*
                new_var = BitVec(new_var_name, 256)
                path_conditions_and_vars[new_var_name] = new_var
                stack.insert(0, new_var)
        else:
            raise ValueError('STACK underflow')
    #
    # 30s: Environment Information
    #
    elif opcode == "ADDRESS":  # get address of currently executing account
        global_state["pc"] = global_state["pc"] + 1
        stack.insert(0, path_conditions_and_vars["Ia"])
    elif opcode == "BALANCE":
        if len(stack) > 0:
            global_state["pc"] = global_state["pc"] + 1
            address = stack.pop(0)
            if isReal(address) and global_params.USE_GLOBAL_BLOCKCHAIN:
                new_var = data_source.getBalance(address)
            else:
                new_var_name = gen.gen_balance_var()    # balance_*
                if new_var_name in path_conditions_and_vars:
                    new_var = path_conditions_and_vars[new_var_name]
                else:
                    new_var = BitVec(new_var_name, 256)
                    path_conditions_and_vars[new_var_name] = new_var
            if isReal(address):
                hashed_address = "concrete_address_" + str(address)
            else:
                hashed_address = str(address)
            global_state["balance"][hashed_address] = new_var
            stack.insert(0, new_var)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "CALLER":  # get caller address
        # that is directly responsible for this execution
        global_state["pc"] = global_state["pc"] + 1
        stack.insert(0, global_state["sender_address"])
    elif opcode == "ORIGIN":  # get execution origination address
        global_state["pc"] = global_state["pc"] + 1
        stack.insert(0, global_state["origin"])
    elif opcode == "CALLVALUE":  # get value of this transaction
        global_state["pc"] = global_state["pc"] + 1
        stack.insert(0, global_state["value"])
    elif opcode == "CALLDATALOAD":  # from input data from environment
        if len(stack) > 0:
            global_state["pc"] = global_state["pc"] + 1
            position = stack.pop(0)
            if g_src_map:
                source_code = g_src_map.get_source_code(global_state['pc'] - 1)
                if source_code.startswith("function") and isReal(position) and current_func_name in g_src_map.func_name_to_params:
                    params =  g_src_map.func_name_to_params[current_func_name]
                    param_idx = (position - 4) // 32
                    for param in params:
                        if param_idx == param['position']:
                            new_var_name = param['name']
                            g_src_map.var_names.append(new_var_name)
                else:
                    new_var_name = gen.gen_data_var(position)   # Id_*
            else:
                new_var_name = gen.gen_data_var(position)   # Id_*
            if new_var_name in path_conditions_and_vars:
                new_var = path_conditions_and_vars[new_var_name]
            else:
                new_var = BitVec(new_var_name, 256)
                path_conditions_and_vars[new_var_name] = new_var
            stack.insert(0, new_var)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "CALLDATASIZE":
        global_state["pc"] = global_state["pc"] + 1
        new_var_name = gen.gen_data_size()  # Id_size
        if new_var_name in path_conditions_and_vars:
            new_var = path_conditions_and_vars[new_var_name]
        else:
            new_var = BitVec(new_var_name, 256)
            path_conditions_and_vars[new_var_name] = new_var
        stack.insert(0, new_var)
    elif opcode == "CALLDATACOPY":  # Copy input data to memory
        #  TODO: Don't know how to simulate this yet
        if len(stack) > 2:
            global_state["pc"] = global_state["pc"] + 1
            stack.pop(0)
            stack.pop(0)
            stack.pop(0)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "CODESIZE":
        global_state["pc"] = global_state["pc"] + 1
        if g_disasm_file.endswith('.disasm'):
            evm_file_name = g_disasm_file[:-7]
        else:
            evm_file_name = g_disasm_file
        with open(evm_file_name, 'r') as evm_file:
            evm = evm_file.read()[:-1]
            code_size = len(evm)/2
            stack.insert(0, code_size)
    elif opcode == "CODECOPY":
        if len(stack) > 2:
            global_state["pc"] = global_state["pc"] + 1
            mem_location = stack.pop(0)
            code_from = stack.pop(0)
            no_bytes = stack.pop(0)
            current_miu_i = global_state["miu_i"]

            if isAllReal(mem_location, current_miu_i, code_from, no_bytes):
                if six.PY2:
                    temp = long(math.ceil((mem_location + no_bytes) / float(32)))
                else:
                    temp = int(math.ceil((mem_location + no_bytes) / float(32)))

                if temp > current_miu_i:
                    current_miu_i = temp

                if g_disasm_file.endswith('.disasm'):
                    evm_file_name = g_disasm_file[:-7]
                else:
                    evm_file_name = g_disasm_file
                with open(evm_file_name, 'r') as evm_file:
                    evm = evm_file.read()[:-1]
                    start = code_from * 2
                    end = start + no_bytes * 2
                    code = evm[start: end]
                mem[mem_location] = int(code, 16)
            else:  
                new_var_name = gen.gen_code_var("Ia", code_from, no_bytes)  # code_Ia_*_*
                if new_var_name in path_conditions_and_vars:
                    new_var = path_conditions_and_vars[new_var_name]
                else:
                    new_var = BitVec(new_var_name, 256)
                    path_conditions_and_vars[new_var_name] = new_var

                temp = ((mem_location + no_bytes) / 32) + 1
                current_miu_i = to_symbolic(current_miu_i)
                expression = current_miu_i < temp
                solver.push()
                solver.add(expression)
                if MSIZE:
                    if check_sat(solver) != unsat:
                        current_miu_i = If(expression, temp, current_miu_i)
                solver.pop()
                mem.clear() # very conservative
                mem[str(mem_location)] = new_var
            global_state["miu_i"] = current_miu_i
        else:
            raise ValueError('STACK underflow')
    elif opcode == "RETURNDATACOPY":
        if len(stack) > 2:
            global_state["pc"] += 1
            stack.pop(0)
            stack.pop(0)
            stack.pop(0)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "RETURNDATASIZE":
        global_state["pc"] += 1
        new_var_name = gen.gen_arbitrary_var()  # some_var_*
        new_var = BitVec(new_var_name, 256)
        stack.insert(0, new_var)
    elif opcode == "GASPRICE":
        global_state["pc"] = global_state["pc"] + 1
        stack.insert(0, global_state["gas_price"])
    elif opcode == "EXTCODESIZE":
        if len(stack) > 0:
            global_state["pc"] = global_state["pc"] + 1
            address = stack.pop(0)
            if isReal(address) and global_params.USE_GLOBAL_BLOCKCHAIN:
                code = data_source.getCode(address)
                stack.insert(0, len(code)/2)
            else:
                #not handled yet
                new_var_name = gen.gen_code_size_var(address)   # code_size_* address
                if new_var_name in path_conditions_and_vars:
                    new_var = path_conditions_and_vars[new_var_name]
                else:
                    new_var = BitVec(new_var_name, 256)
                    path_conditions_and_vars[new_var_name] = new_var
                stack.insert(0, new_var)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "EXTCODECOPY":
        if len(stack) > 3:
            global_state["pc"] = global_state["pc"] + 1
            address = stack.pop(0)
            mem_location = stack.pop(0)
            code_from = stack.pop(0)
            no_bytes = stack.pop(0)
            current_miu_i = global_state["miu_i"]

            if isAllReal(address, mem_location, current_miu_i, code_from, no_bytes) and USE_GLOBAL_BLOCKCHAIN:
                if six.PY2:
                    temp = long(math.ceil((mem_location + no_bytes) / float(32)))
                else:
                    temp = int(math.ceil((mem_location + no_bytes) / float(32)))
                if temp > current_miu_i:
                    current_miu_i = temp

                evm = data_source.getCode(address)
                start = code_from * 2
                end = start + no_bytes * 2
                code = evm[start: end]
                mem[mem_location] = int(code, 16)
            else:
                new_var_name = gen.gen_code_var(address, code_from, no_bytes)   # code_*_*_*
                if new_var_name in path_conditions_and_vars:
                    new_var = path_conditions_and_vars[new_var_name]
                else:
                    new_var = BitVec(new_var_name, 256)
                    path_conditions_and_vars[new_var_name] = new_var

                temp = ((mem_location + no_bytes) / 32) + 1
                current_miu_i = to_symbolic(current_miu_i)
                expression = current_miu_i < temp
                solver.push()
                solver.add(expression)
                if MSIZE:
                    if check_sat(solver) != unsat:
                        current_miu_i = If(expression, temp, current_miu_i)
                solver.pop()
                mem.clear() # very conservative
                mem[str(mem_location)] = new_var
            global_state["miu_i"] = current_miu_i
        else:
            raise ValueError('STACK underflow')
    #
    #  40s: Block Information
    #
    elif opcode == "BLOCKHASH":  # information from block header
        if len(stack) > 0:
            global_state["pc"] = global_state["pc"] + 1
            stack.pop(0)
            new_var_name = "IH_blockhash"
            if new_var_name in path_conditions_and_vars:
                new_var = path_conditions_and_vars[new_var_name]
            else:
                new_var = BitVec(new_var_name, 256)
                path_conditions_and_vars[new_var_name] = new_var
            stack.insert(0, new_var)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "COINBASE":  # information from block header
        global_state["pc"] = global_state["pc"] + 1
        stack.insert(0, global_state["currentCoinbase"])
    elif opcode == "TIMESTAMP":  # information from block header
        global_state["pc"] = global_state["pc"] + 1
        stack.insert(0, global_state["currentTimestamp"])
    elif opcode == "NUMBER":  # information from block header
        global_state["pc"] = global_state["pc"] + 1
        stack.insert(0, global_state["currentNumber"])
    elif opcode == "DIFFICULTY":  # information from block header
        global_state["pc"] = global_state["pc"] + 1
        stack.insert(0, global_state["currentDifficulty"])
    elif opcode == "GASLIMIT":  # information from block header
        global_state["pc"] = global_state["pc"] + 1
        stack.insert(0, global_state["currentGasLimit"])
    #
    #  50s: Stack, Memory, Storage, and Flow Information
    #
    elif opcode == "POP":
        if len(stack) > 0:
            global_state["pc"] = global_state["pc"] + 1
            stack.pop(0)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "MLOAD":
        if len(stack) > 0:
            global_state["pc"] = global_state["pc"] + 1
            address = stack.pop(0)
            current_miu_i = global_state["miu_i"]
            if isAllReal(address, current_miu_i) and address in mem:
                if six.PY2:
                    temp = long(math.ceil((address + 32) / float(32)))
                else:
                    temp = int(math.ceil((address + 32) / float(32)))
                if temp > current_miu_i:
                    current_miu_i = temp
                value = mem[address]
                stack.insert(0, value)
            else:
                temp = ((address + 31) / 32) + 1
                current_miu_i = to_symbolic(current_miu_i)
                expression = current_miu_i < temp
                solver.push()
                solver.add(expression)
                if MSIZE:
                    if check_sat(solver) != unsat:
                        # this means that it is possibly that current_miu_i < temp
                        current_miu_i = If(expression,temp,current_miu_i)
                solver.pop()
                new_var_name = gen.gen_mem_var(address) # mem_*
                if new_var_name in path_conditions_and_vars:
                    new_var = path_conditions_and_vars[new_var_name]
                else:
                    new_var = BitVec(new_var_name, 256)
                    path_conditions_and_vars[new_var_name] = new_var
                stack.insert(0, new_var)
                if isReal(address):
                    mem[address] = new_var
                else:
                    mem[str(address)] = new_var
            global_state["miu_i"] = current_miu_i
        else:
            raise ValueError('STACK underflow')
    elif opcode == "MSTORE":
        if len(stack) > 1:
            global_state["pc"] = global_state["pc"] + 1
            stored_address = stack.pop(0)
            stored_value = stack.pop(0)
            current_miu_i = global_state["miu_i"]
            if isReal(stored_address):
                # preparing data for hashing later
                old_size = len(memory) // 32
                new_size = ceil32(stored_address + 32) // 32
                mem_extend = (new_size - old_size) * 32
                memory.extend([0] * mem_extend)
                value = stored_value
                for i in range(31, -1, -1):
                    memory[stored_address + i] = value % 256
                    value /= 256
            if isAllReal(stored_address, current_miu_i):
                if six.PY2:
                    temp = long(math.ceil((stored_address + 32) / float(32)))
                else:
                    temp = int(math.ceil((stored_address + 32) / float(32)))
                if temp > current_miu_i:
                    current_miu_i = temp
                mem[stored_address] = stored_value  # note that the stored_value could be symbolic
            else:
                temp = ((stored_address + 31) / 32) + 1
                expression = current_miu_i < temp
                solver.push()
                solver.add(expression)
                if MSIZE:
                    if check_sat(solver) != unsat:
                        # this means that it is possibly that current_miu_i < temp
                        current_miu_i = If(expression,temp,current_miu_i)
                solver.pop()
                mem.clear()  # very conservative
                mem[str(stored_address)] = stored_value
            global_state["miu_i"] = current_miu_i
        else:
            raise ValueError('STACK underflow')
    elif opcode == "MSTORE8":
        if len(stack) > 1:
            global_state["pc"] = global_state["pc"] + 1
            stored_address = stack.pop(0)
            temp_value = stack.pop(0)
            stored_value = temp_value % 256  # get the least byte
            current_miu_i = global_state["miu_i"]
            if isAllReal(stored_address, current_miu_i):
                if six.PY2:
                    temp = long(math.ceil((stored_address + 1) / float(32)))
                else:
                    temp = int(math.ceil((stored_address + 1) / float(32)))
                if temp > current_miu_i:
                    current_miu_i = temp
                mem[stored_address] = stored_value  # note that the stored_value could be symbolic
            else:
                temp = (stored_address / 32) + 1
                if isReal(current_miu_i):
                    current_miu_i = BitVecVal(current_miu_i, 256)
                expression = current_miu_i < temp
                solver.push()
                solver.add(expression)
                if MSIZE:
                    if check_sat(solver) != unsat:
                        # this means that it is possibly that current_miu_i < temp
                        current_miu_i = If(expression,temp,current_miu_i)
                solver.pop()
                mem.clear()  # very conservative
                mem[str(stored_address)] = stored_value
            global_state["miu_i"] = current_miu_i
        else:
            raise ValueError('STACK underflow')
    elif opcode == "SLOAD":
        if len(stack) > 0:
            global_state["pc"] = global_state["pc"] + 1
            position = stack.pop(0)
            if isReal(position) and position in global_state["Ia"]:
                value = global_state["Ia"][position]
                stack.insert(0, value)
            elif global_params.USE_GLOBAL_STORAGE and isReal(position) and position not in global_state["Ia"]:
                value = data_source.getStorageAt(position)
                global_state["Ia"][position] = value
                stack.insert(0, value)
            else:
                if str(position) in global_state["Ia"]:
                    value = global_state["Ia"][str(position)]
                    stack.insert(0, value)
                else:
                    if is_expr(position):
                        position = simplify(position)
                    if g_src_map:
                        new_var_name = g_src_map.get_source_code(global_state['pc'] - 1)
                        operators = '[-+*/%|&^!><=]'
                        new_var_name = re.compile(operators).split(new_var_name)[0].strip()
                        new_var_name = g_src_map.get_parameter_or_state_var(new_var_name)
                        if new_var_name:
                            new_var_name = gen.gen_owner_store_var(position, new_var_name)  # Ia_store-*-*
                        else:
                            new_var_name = gen.gen_owner_store_var(position)    # Ia_store-*-
                    else:
                        new_var_name = gen.gen_owner_store_var(position)    # Ia_store-*-

                    if new_var_name in path_conditions_and_vars:
                        new_var = path_conditions_and_vars[new_var_name]
                    else:
                        new_var = BitVec(new_var_name, 256)
                        path_conditions_and_vars[new_var_name] = new_var
                    stack.insert(0, new_var)
                    if isReal(position):
                        global_state["Ia"][position] = new_var
                    else:
                        global_state["Ia"][str(position)] = new_var
        else:
            raise ValueError('STACK underflow')

    elif opcode == "SSTORE":
        if len(stack) > 1:
            for call_pc in calls:
                calls_affect_state[call_pc] = True
            global_state["pc"] = global_state["pc"] + 1
            stored_address = stack.pop(0)
            stored_value = stack.pop(0)
            if isReal(stored_address):
                # note that the stored_value could be unknown
                global_state["Ia"][stored_address] = stored_value
            else:
                # note that the stored_value could be unknown
                global_state["Ia"][str(stored_address)] = stored_value
        else:
            raise ValueError('STACK underflow')
    elif opcode == "JUMP":
        if len(stack) > 0:
            target_address = stack.pop(0)
            if isSymbolic(target_address):
                try:
                    target_address = int(str(simplify(target_address)))
                except:
                    raise TypeError("Target address must be an integer")
            vertices[block].set_jump_target(target_address)
            if target_address not in edges[block]:
                edges[block].append(target_address)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "JUMPI":
        # We need to prepare two branches
        if len(stack) > 1:
            target_address = stack.pop(0)
            if isSymbolic(target_address):
                try:
                    target_address = int(str(simplify(target_address)))
                except:
                    raise TypeError("Target address must be an integer")
            vertices[block].set_jump_target(target_address)
            flag = stack.pop(0)
            branch_expression = (BitVecVal(0, 1) == BitVecVal(1, 1))
            if isReal(flag):
                if flag != 0:
                    branch_expression = True
            else:
                branch_expression = (flag != 0)
            vertices[block].set_branch_expression(branch_expression)
            if target_address not in edges[block]:
                edges[block].append(target_address)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "PC":
        stack.insert(0, global_state["pc"])
        global_state["pc"] = global_state["pc"] + 1
    elif opcode == "MSIZE":
        global_state["pc"] = global_state["pc"] + 1
        msize = 32 * global_state["miu_i"]
        stack.insert(0, msize)
    elif opcode == "GAS":
        # In general, we do not have this precisely. It depends on both
        # the initial gas and the amount has been depleted
        # we need to think about this in the future, in case precise gas
        # can be tracked
        # 一般来说，我们并没有准确地做到这一点。 这取决于初始 gas 和消耗的数量，我们需要在未来考虑这一点，以防可以跟踪精确的 gas
        global_state["pc"] = global_state["pc"] + 1
        new_var_name = gen.gen_gas_var()       # gas_*
        new_var = BitVec(new_var_name, 256)
        path_conditions_and_vars[new_var_name] = new_var
        stack.insert(0, new_var)
    elif opcode == "JUMPDEST":
        # Literally do nothing
        global_state["pc"] = global_state["pc"] + 1
    #
    #  60s & 70s: Push Operations
    #
    elif opcode.startswith('PUSH', 0):  # this is a push instruction
        position = int(opcode[4:], 10)
        global_state["pc"] = global_state["pc"] + 1 + position  # pc处理
        pushed_value = int(instr_parts[1], 16)
        stack.insert(0, pushed_value)
        if global_params.UNIT_TEST == 3: # test evm symbolic
            stack[0] = BitVecVal(stack[0], 256)
    #
    #  80s: Duplication Operations
    #
    elif opcode.startswith("DUP", 0):
        global_state["pc"] = global_state["pc"] + 1
        position = int(opcode[3:], 10) - 1
        if len(stack) > position:
            duplicate = stack[position]
            stack.insert(0, duplicate)
        else:
            raise ValueError('STACK underflow')

    #
    #  90s: Swap Operations
    #
    elif opcode.startswith("SWAP", 0):
        global_state["pc"] = global_state["pc"] + 1
        position = int(opcode[4:], 10)
        if len(stack) > position:
            temp = stack[position]
            stack[position] = stack[0]
            stack[0] = temp
        else:
            raise ValueError('STACK underflow')

    #
    #  a0s: Logging Operations
    #
    elif opcode in ("LOG0", "LOG1", "LOG2", "LOG3", "LOG4"):
        global_state["pc"] = global_state["pc"] + 1
        # We do not simulate these log operations
        num_of_pops = 2 + int(opcode[3:])
        while num_of_pops > 0:
            stack.pop(0)
            num_of_pops -= 1

    #
    #  f0s: System Operations
    #
    elif opcode == "CREATE":
        if len(stack) > 2:
            global_state["pc"] += 1
            stack.pop(0)
            stack.pop(0)
            stack.pop(0)
            new_var_name = gen.gen_arbitrary_var()  # some_var_*
            new_var = BitVec(new_var_name, 256)
            stack.insert(0, new_var)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "CALL":
        # TODO: Need to handle miu_i
        if len(stack) > 6:
            calls.append(global_state["pc"])
            for call_pc in calls:
                if call_pc not in calls_affect_state:
                    calls_affect_state[call_pc] = False
            global_state["pc"] = global_state["pc"] + 1
            outgas = stack.pop(0)
            recipient = stack.pop(0)
            transfer_amount = stack.pop(0)
            start_data_input = stack.pop(0)
            size_data_input = stack.pop(0)
            start_data_output = stack.pop(0)
            size_data_ouput = stack.pop(0)
            # in the paper, it is shaky when the size of data output is
            # min of stack[6] and the | o |

            if isReal(transfer_amount):
                if transfer_amount == 0:
                    stack.insert(0, 1)   # x = 0
                    return

            # Let us ignore the call depth
            balance_ia = global_state["balance"]["Ia"]
            is_enough_fund = (transfer_amount <= balance_ia)
            solver.push()
            solver.add(is_enough_fund)

            if check_sat(solver) == unsat:
                # this means not enough fund, thus the execution will result in exception
                solver.pop()
                stack.insert(0, 0)   # x = 0
            else:
                # the execution is possibly okay
                stack.insert(0, 1)   # x = 1
                solver.pop()
                solver.add(is_enough_fund)
                path_conditions_and_vars["path_condition"].append(is_enough_fund)
                last_idx = len(path_conditions_and_vars["path_condition"]) - 1
                analysis["time_dependency_bug"][last_idx] = global_state["pc"] - 1
                new_balance_ia = (balance_ia - transfer_amount)
                global_state["balance"]["Ia"] = new_balance_ia
                address_is = path_conditions_and_vars["Is"]
                address_is = (address_is & CONSTANT_ONES_159)
                boolean_expression = (recipient != address_is)
                solver.push()
                solver.add(boolean_expression)
                if check_sat(solver) == unsat:
                    solver.pop()
                    new_balance_is = (global_state["balance"]["Is"] + transfer_amount)
                    global_state["balance"]["Is"] = new_balance_is
                else:
                    solver.pop()
                    if isReal(recipient):
                        new_address_name = "concrete_address_" + str(recipient)
                    else:
                        new_address_name = gen.gen_arbitrary_address_var()  # some_address_*
                    old_balance_name = gen.gen_arbitrary_var()  # some_var_*
                    old_balance = BitVec(old_balance_name, 256)
                    path_conditions_and_vars[old_balance_name] = old_balance
                    constraint = (old_balance >= 0)
                    solver.add(constraint)
                    path_conditions_and_vars["path_condition"].append(constraint)
                    new_balance = (old_balance + transfer_amount)
                    global_state["balance"][new_address_name] = new_balance
        else:
            raise ValueError('STACK underflow')
    elif opcode == "CALLCODE":
        # TODO: Need to handle miu_i
        if len(stack) > 6:
            calls.append(global_state["pc"])
            for call_pc in calls:
                if call_pc not in calls_affect_state:
                    calls_affect_state[call_pc] = False
            global_state["pc"] = global_state["pc"] + 1
            outgas = stack.pop(0)
            recipient = stack.pop(0) # this is not used as recipient
            if global_params.USE_GLOBAL_STORAGE:
                if isReal(recipient):
                    recipient = hex(recipient)
                    if recipient[-1] == "L":
                        recipient = recipient[:-1]
                    recipients.add(recipient)
                else:
                    recipients.add(None)

            transfer_amount = stack.pop(0)
            start_data_input = stack.pop(0)
            size_data_input = stack.pop(0)
            start_data_output = stack.pop(0)
            size_data_ouput = stack.pop(0)
            # in the paper, it is shaky when the size of data output is
            # min of stack[6] and the | o |

            if isReal(transfer_amount):
                if transfer_amount == 0:
                    stack.insert(0, 1)   # x = 0
                    return

            # Let us ignore the call depth
            balance_ia = global_state["balance"]["Ia"]
            is_enough_fund = (transfer_amount <= balance_ia)
            solver.push()
            solver.add(is_enough_fund)

            if check_sat(solver) == unsat:
                # this means not enough fund, thus the execution will result in exception
                solver.pop()
                stack.insert(0, 0)   # x = 0
            else:
                # the execution is possibly okay
                stack.insert(0, 1)   # x = 1
                solver.pop()
                solver.add(is_enough_fund)
                path_conditions_and_vars["path_condition"].append(is_enough_fund)
                last_idx = len(path_conditions_and_vars["path_condition"]) - 1
                analysis["time_dependency_bug"][last_idx] = global_state["pc"] - 1
        else:
            raise ValueError('STACK underflow')
    elif opcode in ("DELEGATECALL", "STATICCALL"):
        if len(stack) > 5:
            global_state["pc"] += 1
            stack.pop(0)
            recipient = stack.pop(0)
            if global_params.USE_GLOBAL_STORAGE:
                if isReal(recipient):
                    recipient = hex(recipient)
                    if recipient[-1] == "L":
                        recipient = recipient[:-1]
                    recipients.add(recipient)
                else:
                    recipients.add(None)

            stack.pop(0)
            stack.pop(0)
            stack.pop(0)
            stack.pop(0)
            new_var_name = gen.gen_arbitrary_var()  # some_var_*
            new_var = BitVec(new_var_name, 256)
            stack.insert(0, new_var)
        else:
            raise ValueError('STACK underflow')
    elif opcode in ("RETURN", "REVERT"):
        # TODO: Need to handle miu_i
        if len(stack) > 1:
            if opcode == "REVERT":
                revertible_overflow_pcs.update(overflow_pcs)
                global_state["pc"] = global_state["pc"] + 1
            stack.pop(0)
            stack.pop(0)
            # TODO
            pass
        else:
            raise ValueError('STACK underflow')
    elif opcode == "SUICIDE":
        global_state["pc"] = global_state["pc"] + 1
        recipient = stack.pop(0)
        transfer_amount = global_state["balance"]["Ia"]
        global_state["balance"]["Ia"] = 0
        if isReal(recipient):
            new_address_name = "concrete_address_" + str(recipient)
        else:
            new_address_name = gen.gen_arbitrary_address_var()  # some_address_*
        old_balance_name = gen.gen_arbitrary_var()  # some_var_*
        old_balance = BitVec(old_balance_name, 256)
        path_conditions_and_vars[old_balance_name] = old_balance
        constraint = (old_balance >= 0)
        solver.add(constraint)
        path_conditions_and_vars["path_condition"].append(constraint)
        new_balance = (old_balance + transfer_amount)
        global_state["balance"][new_address_name] = new_balance
        # TODO
        return

    else:
        log.debug("UNKNOWN INSTRUCTION: " + opcode)
        if global_params.UNIT_TEST == 2 or global_params.UNIT_TEST == 3:
            log.critical("Unknown instruction: %s" % opcode)
            exit(UNKNOWN_INSTRUCTION)
        raise Exception('UNKNOWN INSTRUCTION: ' + opcode)

# Detect if a money flow depends on the timestamp
# 检测资金流向是否取决于时间戳
def detect_time_dependency():
    global results
    global g_src_map
    global time_dependency

    TIMESTAMP_VAR = "IH_s"
    is_dependant = False
    pcs = []
    if global_params.PRINT_PATHS:
        log.info("ALL PATH CONDITIONS")
    for i, cond in enumerate(path_conditions):
        if global_params.PRINT_PATHS:
            log.info("PATH " + str(i + 1) + ": " + str(cond))
        for j, expr in enumerate(cond):
            if is_expr(expr):
                if TIMESTAMP_VAR in str(expr) and j in global_problematic_pcs["time_dependency_bug"][i]:
                    pcs.append(global_problematic_pcs["time_dependency_bug"][i][j])
                    is_dependant = True
                    continue

    time_dependency = TimeDependency(g_src_map, pcs)

    if g_src_map:
        results['vulnerabilities']['time_dependency'] = time_dependency.get_warnings()
    else:
        results['vulnerabilities']['time_dependency'] = time_dependency.is_vulnerable()
    log.info('\t  Timestamp Dependency: \t\t %s', time_dependency.is_vulnerable())

    if global_params.REPORT_MODE:
        file_name = g_disasm_file.split("/")[len(g_disasm_file.split("/"))-1].split(".")[0]
        report_file = file_name + '.report'
        with open(report_file, 'w') as rfile:
            if is_dependant:
                rfile.write("yes\n")
            else:
                rfile.write("no\n")


# detect if two paths send money to different people
# 检测两条路径是否向不同的人汇款
def detect_money_concurrency():
    global results
    global g_src_map
    global money_concurrency

    n = len(money_flow_all_paths)
    for i in range(n):
        log.debug("Path " + str(i) + ": " + str(money_flow_all_paths[i]))
        log.debug(all_gs[i])
    i = 0
    false_positive = []
    concurrency_paths = []
    flows = []
    for flow in money_flow_all_paths:
        i += 1
        if len(flow) == 1:
            continue  # pass all flows which do not do anything with money
        for j in range(i, n):
            jflow = money_flow_all_paths[j]
            if len(jflow) == 1:
                continue
            # 检查两个不同的轨迹是否具有不同的以太流量
            if is_diff(flow, jflow):
                flows.append(global_problematic_pcs["money_concurrency_bug"][i-1])
                flows.append(global_problematic_pcs["money_concurrency_bug"][j])
                concurrency_paths.append([i-1, j])
                if global_params.CHECK_CONCURRENCY_FP and \
                        is_false_positive(i-1, j, all_gs, path_conditions) and \
                        is_false_positive(j, i-1, all_gs, path_conditions):
                    false_positive.append([i-1, j])
                break
        if flows:
            break

    money_concurrency = MoneyConcurrency(g_src_map, flows)

    if g_src_map:
        results['vulnerabilities']['money_concurrency'] = money_concurrency.get_warnings_of_flows()
    else:
        results['vulnerabilities']['money_concurrency'] = money_concurrency.is_vulnerable()
    log.info('\t  Transaction-Ordering Dependence (TOD): %s', money_concurrency.is_vulnerable())

    # if PRINT_MODE: print "All false positive cases: ", false_positive
    log.debug("Concurrency in paths: ")
    if global_params.REPORT_MODE:
        rfile.write("number of path: " + str(n) + "\n")
        # number of FP detected
        rfile.write(str(len(false_positive)) + "\n")
        rfile.write(str(false_positive) + "\n")
        # number of total races
        rfile.write(str(len(concurrency_paths)) + "\n")
        # all the races
        rfile.write(str(concurrency_paths) + "\n")

def detect_parity_multisig_bug_2():
    global g_src_map
    global results
    global parity_multisig_bug_2

    parity_multisig_bug_2 = ParityMultisigBug2(g_src_map)

    results['vulnerabilities']['parity_multisig_bug_2'] = parity_multisig_bug_2.get_warnings()
    s = "\t  Parity Multisig Bug 2: \t\t %s" % parity_multisig_bug_2.is_vulnerable()
    log.info(s)

def check_callstack_attack(disasm):
    problematic_instructions = ['CALL', 'CALLCODE']
    pcs = []
    for i in range(0, len(disasm)):
        instruction = disasm[i]
        if instruction[1] in problematic_instructions:
            try:
                pc = int(instruction[0])
                if not disasm[i+1][1] == 'SWAP':
                    continue
                swap_num = int(disasm[i+1][2])
                if not all(disasm[i+j+2][1] == 'POP' for j in range(swap_num)):
                    continue
            except IndexError:
                continue

            try:
                opcode1 = disasm[i + swap_num + 2][1]
                opcode2 = disasm[i + swap_num + 3][1]
                opcode3 = disasm[i + swap_num + 4][1]
                if opcode1 == "ISZERO" \
                    or opcode1 == "DUP" and opcode2 == "ISZERO" \
                    or opcode1 == "JUMPDEST" and opcode2 == "ISZERO" \
                    or opcode1 == "JUMPDEST" and opcode2 == "DUP" and opcode3 == "ISZERO":
                        pass
                else:
                    pcs.append(pc)
            except IndexError:
                pcs.append(pc)
    return pcs


def detect_callstack_attack():
    global results
    global g_src_map
    global calls_affect_state
    global callstack

    disasm_data = open(g_disasm_file).read()
    instr_pattern = r"([\d]+) ([A-Z]+)([\d]+)?(?: => 0x)?(\S+)?"
    instr = re.findall(instr_pattern, disasm_data)
    pcs = check_callstack_attack(instr)

    callstack = CallStack(g_src_map, pcs, calls_affect_state)

    if g_src_map:
        results['vulnerabilities']['callstack'] = callstack.get_warnings()
    else:
        results['vulnerabilities']['callstack'] = callstack.is_vulnerable()
    log.info('\t  Callstack Depth Attack Vulnerability:  %s', callstack.is_vulnerable())

def detect_reentrancy():
    global g_src_map
    global results
    global reentrancy

    pcs = global_problematic_pcs["reentrancy_bug"]
    reentrancy = Reentrancy(g_src_map, pcs)

    if g_src_map:
        results['vulnerabilities']['reentrancy'] = reentrancy.get_warnings()
    else:
        results['vulnerabilities']['reentrancy'] = reentrancy.is_vulnerable()
    log.info("\t  Re-Entrancy Vulnerability: \t\t %s", reentrancy.is_vulnerable())

def detect_integer_underflow():
    global integer_underflow

    integer_underflow = IntegerUnderflow(g_src_map, global_problematic_pcs['integer_underflow'])

    if g_src_map:
        results['vulnerabilities']['integer_underflow'] = integer_underflow.get_warnings()
    else:
        results['vulnerabilities']['integer_underflow'] = integer_underflow.is_vulnerable()
    log.info('\t  Integer Underflow: \t\t\t %s', integer_underflow.is_vulnerable()) # True/False 

def detect_integer_overflow():
    global integer_overflow

    overflows = []
    for overflow in global_problematic_pcs['integer_overflow']:
        if overflow.pc not in revertible_overflow_pcs:
            overflows.append(overflow)
    integer_overflow = IntegerOverflow(g_src_map, overflows)

    if g_src_map:
        results['vulnerabilities']['integer_overflow'] = integer_overflow.get_warnings()
    else:
        results['vulnerabilities']['integer_overflow'] = integer_overflow.is_vulnerable()
    log.info('\t  Integer Overflow: \t\t\t %s', integer_overflow.is_vulnerable())

def detect_assertion_failure():
    global g_src_map
    global results
    global assertion_failure

    assertion_failure = AssertionFailure(g_src_map, global_problematic_pcs['assertion_failure'])

    results['vulnerabilities']['assertion_failure'] = assertion_failure.get_warnings()
    s = "\t  Assertion Failure: \t\t\t %s" % assertion_failure.is_vulnerable()
    log.info(s)

def detect_vulnerabilities():
    global results
    global g_src_map
    global visited_pcs
    global global_problematic_pcs
    global begin

    if instructions:
        evm_code_coverage = float(len(visited_pcs)) / len(instructions.keys()) * 100
        log.info("\t  EVM Code Coverage: \t\t\t %s%%", round(evm_code_coverage, 1))
        results["evm_code_coverage"] = str(round(evm_code_coverage, 1))

        if g_src_map:
            detect_integer_underflow()
            detect_integer_overflow()
            detect_parity_multisig_bug_2()

        log.debug("Checking for Callstack attack...")
        detect_callstack_attack()

        if global_params.REPORT_MODE:
            rfile.write(str(total_no_of_paths) + "\n")

        detect_money_concurrency()  # Transaction-Ordering Dependence (TOD)
        detect_time_dependency()

        stop = time.time()
        if global_params.REPORT_MODE:
            rfile.write(str(stop-begin))
            rfile.close()

        log.debug("Results for Reentrancy Bug: " + str(reentrancy_all_paths))
        detect_reentrancy()

        if global_params.CHECK_ASSERTIONS:
            if g_src_map:
                detect_assertion_failure()
            else:
                raise Exception("Assertion checks need a Source Map")

        if g_src_map:
            log_info()

    else:
        log.info("\t  EVM code coverage: \t 0/0")
        log.info("\t  Callstack bug: \t False")
        log.info("\t  Money concurrency bug: False")
        log.info("\t  Time dependency bug: \t False")
        log.info("\t  Reentrancy bug: \t False")
        if global_params.CHECK_ASSERTIONS:
            log.info("\t  Assertion failure: \t False")
        results["evm_code_coverage"] = "0/0"

    return results, vulnerability_found()

def log_info():
    global g_src_map
    global time_dependency
    global callstack
    global money_concurrency
    global reentrancy
    global assertion_failure
    global parity_multisig_bug_2

    vulnerabilities = [integer_underflow, integer_overflow, callstack, money_concurrency, time_dependency, reentrancy]
    if g_src_map:
        vulnerabilities.append(parity_multisig_bug_2)
        if global_params.CHECK_ASSERTIONS:
            vulnerabilities.append(assertion_failure)

    for vul in vulnerabilities:
        s = str(vul)
        if s:
            log.info(s)

def vulnerability_found():
    global g_src_map
    global time_dependency
    global callstack
    global money_concurrency
    global reentrancy
    global assertion_failure
    global parity_multisig_bug_2

    vulnerabilities = [callstack, money_concurrency, time_dependency, reentrancy]

    if g_src_map and global_params.CHECK_ASSERTIONS:
        vulnerabilities.append(assertion_failure)
        vulnerabilities.append(parity_multisig_bug_2)

    for vul in vulnerabilities:
        if vul.is_vulnerable():
            return 1
    return 0

def closing_message():
    global g_disasm_file
    global results

    log.info("\t====== Analysis Completed ======")
    if global_params.STORE_RESULT:
        result_file = g_disasm_file.split('.evm.disasm')[0] + '.json'
        with open(result_file, 'w') as of:
            of.write(json.dumps(results, indent=1))
        log.info("Wrote results to %s.", result_file)

class TimeoutError(Exception):
    pass

class Timeout:
   """Timeout class using ALARM signal."""

   def __init__(self, sec=10, error_message=os.strerror(errno.ETIME)):
       self.sec = sec
       self.error_message = error_message

   def __enter__(self):
       signal.signal(signal.SIGALRM, self._handle_timeout)
       signal.alarm(self.sec)

   def __exit__(self, *args):
       signal.alarm(0)    # disable alarm

   def _handle_timeout(self, signum, frame):
       raise TimeoutError(self.error_message)

def do_nothing():
    pass

# 构建 cfg 并分析
def run_build_cfg_and_analyze(timeout_cb=do_nothing):
    # 初始化全局变量
    initGlobalVars()
    global g_timeout

    try:
        with Timeout(sec=global_params.GLOBAL_TIMEOUT):
            build_cfg_and_analyze()
        log.debug('Done Symbolic execution')
    except TimeoutError:
        g_timeout = True
        timeout_cb()

def get_recipients(disasm_file, contract_address):
    global recipients
    global data_source
    global g_src_map
    global g_disasm_file
    global g_source_file

    g_src_map = None
    g_disasm_file = disasm_file
    g_source_file = None
    data_source = EthereumData(contract_address)
    recipients = set()

    evm_code_coverage = float(len(visited_pcs)) / len(instructions.keys())

    run_build_cfg_and_analyze()

    return {
        'addrs': list(recipients),
        'evm_code_coverage': evm_code_coverage,
        'timeout': g_timeout
    }

def test():
    global_params.GLOBAL_TIMEOUT = global_params.GLOBAL_TIMEOUT_TEST

    def timeout_cb():
        traceback.print_exc()
        exit(EXCEPTION)

    run_build_cfg_and_analyze(timeout_cb=timeout_cb)

def analyze():
    def timeout_cb():
        if global_params.DEBUG_MODE:
            traceback.print_exc()

    # 调用 run_build_cfg_and_analyze() 函数，构建 cfg 并分析
    run_build_cfg_and_analyze(timeout_cb=timeout_cb)

# oyente.py 调用此函数来获取结果
# 这个函数获取了生成的汇编文件的位置，源文件的位置和 SourceMap 的对象。
# 然后 run 函数调用了 analyze()
def run(disasm_file=None, source_file=None, source_map=None):
    global g_disasm_file
    global g_source_file
    global g_src_map
    global results

    g_disasm_file = disasm_file
    g_source_file = source_file
    g_src_map = source_map

    if is_testing_evm():
        test()
    else:
        begin = time.time()
        log.info("\t============ Results ===========")
        analyze()
        ret = detect_vulnerabilities()
        closing_message()
        # print_cfg()
        return ret
