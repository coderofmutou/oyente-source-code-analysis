import shlex
import subprocess
import os
import re
import logging
import json
import global_params
import six
from source_map import SourceMap
from utils import run_command, run_command_with_err
from crytic_compile import CryticCompile, InvalidCompilation

class InputHelper:
    BYTECODE = 0
    SOLIDITY = 1
    STANDARD_JSON = 2
    STANDARD_JSON_OUTPUT = 3

    # 根据输入类型设置默认属性值，若 args 中有则替换默认值
    def __init__(self, input_type, **kwargs):
        self.input_type = input_type

        if input_type == InputHelper.BYTECODE:
            attr_defaults = {
                'source': None,
                'evm': False,
            }
        elif input_type == InputHelper.SOLIDITY:
            attr_defaults = {
                'source': None,
                'evm': False,
                'root_path': "",
                'compiled_contracts': [],
                'compilation_err': False,
                'remap': "",
                'allow_paths': ""
            }
        elif input_type == InputHelper.STANDARD_JSON:
            attr_defaults = {
                'source': None,
                'evm': False,
                'root_path': "",
                'allow_paths': None,
                'compiled_contracts': []
            }
        elif input_type == InputHelper.STANDARD_JSON_OUTPUT:
            attr_defaults = {
                'source': None,
                'evm': False,
                'root_path': "",
                'compiled_contracts': [],
            }

        for (attr, default) in six.iteritems(attr_defaults):
            val = kwargs.get(attr, default)
            if val == None:
                raise Exception("'%s' attribute can't be None" % attr)
            else:
                setattr(self, attr, val)

    def get_inputs(self, targetContracts=None):
        inputs = []
        if self.input_type == InputHelper.BYTECODE:
            with open(self.source, 'r') as f:
                bytecode = f.read()
            self._prepare_disasm_file(self.source, bytecode)

            disasm_file = self._get_temporary_files(self.source)['disasm']
            inputs.append({'disasm_file': disasm_file})
        else:
            # 编译合约，返回(path/*.sol:ContractName,'ByteCode_runtime')
            # ('/home/daniel/paper/oyente/remote_contract.sol:Puzzle', '60606040526004361061006d576000357c0100000000000000000000000000000000000000000000000000000000900463ffffffff168063228cb733146102285780634fb60251146102515780638da5cb5b146102df578063a0d7afb714610334578063cf30901214610365575b341561007857600080fd5b6000809054906101000a900473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff163373ffffffffffffffffffffffffffffffffffffffff16141561014c57600060149054906101000a900460ff16156100e757600080fd5b6000809054906101000a900473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff166108fc6001549081150290604051600060405180830381858888f193505050505034600181905550610226565b600080369050111561022557600060149054906101000a900460ff161561017257600080fd5b600254600019166002600036604051808383808284378201915050925050506020604051808303816000865af115156101aa57600080fd5b505060405180519050600019161015610224573373ffffffffffffffffffffffffffffffffffffffff166108fc6001549081150290604051600060405180830381858888f193505050505060003660039190610207929190610474565b506001600060146101000a81548160ff0219169083151502179055505b5b5b005b341561023357600080fd5b61023b610392565b6040518082815260200191505060405180910390f35b341561025c57600080fd5b610264610398565b6040518080602001828103825283818151815260200191508051906020019080838360005b838110156102a4578082015181840152602081019050610289565b50505050905090810190601f1680156102d15780820380516001836020036101000a031916815260200191505b509250505060405180910390f35b34156102ea57600080fd5b6102f2610436565b604051808273ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200191505060405180910390f35b341561033f57600080fd5b61034761045b565b60405180826000191660001916815260200191505060405180910390f35b341561037057600080fd5b610378610461565b604051808215151515815260200191505060405180910390f35b60015481565b60038054600181600116156101000203166002900480601f01602080910402602001604051908101604052809291908181526020018280546001816001161561010002031660029004801561042e5780601f106104035761010080835404028352916020019161042e565b820191906000526020600020905b81548152906001019060200180831161041157829003601f168201915b505050505081565b6000809054906101000a900473ffffffffffffffffffffffffffffffffffffffff1681565b60025481565b600060149054906101000a900460ff1681565b828054600181600116156101000203166002900490600052602060002090601f016020900481019282601f106104b557803560ff19168380011785556104e3565b828001600101855582156104e3579182015b828111156104e25782358255916020019190600101906104c7565b5b5090506104f091906104f4565b5090565b61051691905b808211156105125760008160009055506001016104fa565b5090565b905600a165627a7a723058205dd5ad1a2690fcdf9a613ca17640ae0744024a2f853eb587dfbfdf7659f275dd0029')
            contracts = self._get_compiled_contracts()  
            # 对所有合约生成 .evm 和 .evm.disam 文件(去结尾 hash 的 runtime_bytecode,对字节码进行 Disassembly)
            self._prepare_disasm_files_for_analysis(contracts)

            # contract(绝对路径+文件名.sol:合约名)
            for contract, _ in contracts:
                # 合约绝对路径, 合约名(代码内的名字)
                c_source, cname = contract.split(':')
                if targetContracts is not None and cname not in targetContracts:
                    continue
                c_source = re.sub(self.root_path, "", c_source)
                if self.input_type == InputHelper.SOLIDITY:
                    source_map = SourceMap(contract, self.source, 'solidity', self.root_path, self.remap, self.allow_paths)
                else:
                    source_map = SourceMap(contract, self.source, 'standard json', self.root_path)
                disasm_file = self._get_temporary_files(contract)['disasm']
                inputs.append({
                    'contract': contract,
                    'source_map': source_map,
                    'source': self.source,
                    'c_source': c_source,
                    'c_name': cname,
                    'disasm_file': disasm_file
                })
        if targetContracts is not None and not inputs:
            raise ValueError("Targeted contracts weren't found in the source code!")
        return inputs

    def rm_tmp_files(self):
        if self.input_type == InputHelper.BYTECODE:
            self._rm_tmp_files(self.source)
        else:
            self._rm_tmp_files_of_multiple_contracts(self.compiled_contracts)

    # 编译合约，返回(path/*.sol:ContractName,'ByteCode_runtime')
    def _get_compiled_contracts(self):
        if not self.compiled_contracts:
            if self.input_type == InputHelper.SOLIDITY:
                self.compiled_contracts = self._compile_solidity()
            elif self.input_type == InputHelper.STANDARD_JSON:
                self.compiled_contracts = self._compile_standard_json()
            elif self.input_type == InputHelper.STANDARD_JSON_OUTPUT:
                self.compiled_contracts = self._compile_standard_json_output(self.source)

        return self.compiled_contracts

    def _extract_bin_obj(self, com: CryticCompile):
        return [(com.contracts_filenames[name].absolute + ':' + name, com.bytecode_runtime(name)) for name in com.contracts_names if com.bytecode_runtime(name)]

    def _compile_solidity(self):
        try:
            options = []
            if self.allow_paths:
                options.append(F"--allow-paths {self.allow_paths}")
                
            com = CryticCompile(self.source, solc_remaps=self.remap, solc_args=' '.join(options))
            contracts = self._extract_bin_obj(com)

            libs = com.contracts_names.difference(com.contracts_names_without_libraries)
            if libs:
                return self._link_libraries(self.source, libs)
            
            return contracts
        except InvalidCompilation as err:
            if not self.compilation_err:
                logging.critical("Solidity compilation failed. Please use -ce flag to see the detail.")
                if global_params.WEB:
                    six.print_({"error": "Solidity compilation failed."})
            else:
                logging.critical("solc output:\n" + self.source)
                logging.critical(err)
                logging.critical("Solidity compilation failed.")
                if global_params.WEB:
                    six.print_({"error": err})
            exit(1)


    def _compile_standard_json(self):
        FNULL = open(os.devnull, 'w')
        cmd = "cat %s" % self.source
        p1 = subprocess.Popen(shlex.split(cmd), stdout=subprocess.PIPE, stderr=FNULL)
        cmd = "solc --allow-paths %s --standard-json" % self.allow_paths
        p2 = subprocess.Popen(shlex.split(cmd), stdin=p1.stdout, stdout=subprocess.PIPE, stderr=FNULL)
        p1.stdout.close()
        out = p2.communicate()[0]
        with open('standard_json_output', 'w') as of:
            of.write(out)

        return self._compile_standard_json_output('standard_json_output')

    def _compile_standard_json_output(self, json_output_file):
        with open(json_output_file, 'r') as f:
            out = f.read()
        j = json.loads(out)
        contracts = []
        for source in j['sources']:
            for contract in j['contracts'][source]:
                cname = source + ":" + contract
                evm = j['contracts'][source][contract]['evm']['deployedBytecode']['object']
                contracts.append((cname, evm))
        return contracts
    # 去掉 runtime_bytecode 中的结尾 hash
    def _removeSwarmHash(self, evm):
        evm_without_hash = re.sub(r"a165627a7a72305820\S{64}0029$", "", evm)
        return evm_without_hash

    def _link_libraries(self, filename, libs):
        options = []
        for idx, lib in enumerate(libs):
            lib_address = "0x" + hex(idx+1)[2:].zfill(40)
            options.append("--libraries %s:%s" % (lib, lib_address))
        if self.allow_paths:
            options.append(F"--allow-paths {self.allow_paths}")
        com = CryticCompile(target=self.source, solc_args=' '.join(options), solc_remaps=self.remap)

        return self._extract_bin_obj(com)

    # 对所有合约生成 .evm 和 .evm.disam 文件(去结尾 hash 的 runtime_bytecode,对字节码进行 Disassembly)
    def _prepare_disasm_files_for_analysis(self, contracts):
        for contract, bytecode in contracts:
            self._prepare_disasm_file(contract, bytecode)

    # 生成 .evm 和 .evm.disam 文件(去结尾 hash 的 runtime_bytecode,对字节码进行 Disassembly)
    def _prepare_disasm_file(self, target, bytecode):
        # 写入 evm 字节码文件
        self._write_evm_file(target, bytecode)
        self._write_disasm_file(target)

    def _get_temporary_files(self, target):
        return {
            "evm": target + ".evm",
            "disasm": target + ".evm.disasm",
            "log": target + ".evm.disasm.log"
        }

    # 向 *.sol 写入 .evm 文件(去结尾 hash 的 runtime_bytecode)
    def _write_evm_file(self, target, bytecode):
        evm_file = self._get_temporary_files(target)["evm"]
        with open(evm_file, 'w') as of:
            of.write(self._removeSwarmHash(bytecode))

    # 生成 .evm.disasm 文件(字节码，pc opcode value ...)(方便阅读)
    def _write_disasm_file(self, target):
        tmp_files = self._get_temporary_files(target)
        evm_file = tmp_files["evm"]
        disasm_file = tmp_files["disasm"]
        disasm_out = ""
        try:
            # TODO ?
            disasm_p = subprocess.Popen(    # (参数, 表示需要创建一个新的管道)
                ["evm", "disasm", evm_file], stdout=subprocess.PIPE)
            disasm_out = disasm_p.communicate()[0].decode('utf-8', 'strict')
        except:
            logging.critical("Disassembly failed.")
            exit()

        with open(disasm_file, 'w') as of:
            of.write(disasm_out)

    def _rm_tmp_files_of_multiple_contracts(self, contracts):
        if self.input_type in ['standard_json', 'standard_json_output']:
            self._rm_file('standard_json_output')
        for contract, _ in contracts:
            self._rm_tmp_files(contract)

    def _rm_tmp_files(self, target):
        tmp_files = self._get_temporary_files(target)
        if not self.evm:
            self._rm_file(tmp_files["evm"])
            self._rm_file(tmp_files["disasm"])
        self._rm_file(tmp_files["log"])

    def _rm_file(self, path):
        if os.path.isfile(path):
            os.unlink(path)
