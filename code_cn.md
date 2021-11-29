# Code Structure

## *oyente.py*

这是程序的主要入口点。 Oyente 能够通过以下输入分析智能合约

- solidity 程序
- evm 字节码
- 远程合约

其他配置选项包括获取输入状态、为 z3 设置超时等（检查 ```python oyente.py --help``` 或 ```global_params.py``` 以获取可用配置选项的完整列表。

这些选项在 *global_params* 模块中整理和设置，该模块将在执行的其余部分使用。

然后使用 ```evm disasm``` 命令将合约分解为操作码。

在此之后，symexec 模块使用反汇编文件调用，该文件执行对各种漏洞（TOD、时间戳依赖、错误处理的异常）的合约的分析。

## *symExec.py*

分析从 ```build_cfg_and_analyze``` 函数开始。 我们使用原生 tokenize python 模块将 oyente.py 创建的 disasm 文件分解为 tokens。

```collect_vertices``` 和 ```construct_bb``` 函数识别程序中的基本块，我们将它们存储为顶点。 基本块通过使用诸如 ```JUMPDEST```、```STOP```、```RETURN```、```SUICIDE```、```JUMP``` 和 ```JUMPI``` 之类的操作码作为分隔符来识别。 每个基本块都由 ```basicblock.py``` 中定义的 BasicBlock 类的实例支持。

创建基本块后，我们开始使用 `full_sym_exec` 函数符号地执行每个基本块。 我们获取存储在每个基本块中的指令，并通过 `sym_exec_ins` 函数象征性地执行每个指令。 在这个函数中，我们尽可能接近以太坊黄皮书中描述的行为对每个操作码进行建模。 下面讨论了关于每一类操作码的一些有趣的细节。

### 建模

堆栈是使用简单的 Python 列表建模的。

内存被建模为一个不断增长的列表。 内存列表使用的最大索引存储为 ```current_miu_i``` 变量。

存储作为键值对存储为 python 对象。

### 0s: Stop and Arithmetic Operations, 10s: Comparison & Bitwise Logic Operations

这组操作码是最容易实现的。 如果操作数之一是符号，则它们都被转换为 256 位符号变量。 执行算术运算（象征性地，如果操作数是象征性的）并将结果压入堆栈。

### 20s: SHA3

创建一个通用符号变量来模拟 `SHA3` 操作码的行为。

### 30s: Environmental Information, 40s: Block Information

对于这些操作码中的大多数，会生成一个唯一的符号变量来表示它（类似于 `SHA3`）。 在某些情况下，为了加速符号执行，这些操作码的具体值取自 `state.json` 文件。 此行为是通过 `--state` 标志启用的。 我们还没有找到以符号方式稳健地模拟 ```CODECOPY``` 和 ```EXTCODESIZE``` 的方法。

### 40s: 50s: Stack, Memory, Storage and Flow Operations

在分析 ```JUMP``` 和 ```JUMPI``` 指令期间发现的新边被动态添加到调用图中。

### f0s: System operations

为了处理 ```CALL``` 和 ```CALLCODE``` 操作码，我们构造了符号表达式以确保发送者的帐户中有足够的资金并且发送者的地址与接收者的地址不同。 如果这些条件成立，我们更新相应的全局状态。

在此之后，将此基本块添加到已访问块列表中，并跟随它到下一个基本块。 我们还在 ```path_conditions_and_vars``` 变量中维护了到达块所需的必要路径条件。 对于像 ```JUMP``` 这样的指令，只有一个基本块可以跟随程序执行。 在其他情况下，例如 ```JUMPI```，我们首先使用 z3 检查分支表达式是否可证明为 True 或 False。 如果不是，我们通过将分支表达式和否定分支表达式添加到 ```path_conditions_and_vars``` 变量来探索两个分支。

- Callstack attack

检查调用堆栈攻击由 *check_callstack_attack* 函数完成。如果发现一个 ```CALL``` 或一个 ```CALLCODE``` 指令而后面没有 ```SWAP4, POP, POP, POP, POP, ISZERO```（或 ```SWAP3``` 后跟 3 ```POP``` 等），我们将其标记为容易受到调用堆栈攻击。该操作码序列是由 solc 生成的，对应以下推荐的代码模式，以防止攻击。

```
if (owner.send(amount)) {..}
```

- Timestamp dependence attack

我们找出 ```path_conditions``` 变量是否包含与区块时间戳对应的符号变量。 如果是这样，则可以得出结论，该程序在程序中采用了利用区块时间戳的路径，使其容易受到时间戳依赖性攻击。

- Reentrancy bug

在 analysis.py 中的 ```check_reentrancy_bug``` 函数中分析了此错误的存在。 在每次遇到 ```CALL``` 时，我们都会在执行 ```CALL``` 之前获取执行的路径条件。 然后，我们检查具有更新变量（例如，存储值）的这种条件是否仍然成立（即，是否可以再次执行调用）。 如果是这样，我们认为这是一个漏洞，因为被调用者有可能在完成之前重新执行调用。

我们还考虑了用户使用 `sender` 和 `transfer` 而不是 `call` 函数的情况。 使用 `sender` 和 `transfer` 是安全的，因为作为 `send` 和 `transfer` 的一部分的 gas 是有限的。 作为这些功能的一部分，为了根据 gas 来检查合约是否安全，我们将阈值设置为 2300，这是 ```sender``` 和 ```transfer``` 提供的 gas 量。 然后将与这些函数一起发送的 gas 与阈值进行比较。 如果 gas 大于阈值，我们会将合约标记为易受重入攻击。 否则，我们将其标记为安全。

- Concurrency bug

我们在 ```update_analysis``` 函数中跟踪每个 ```CALL``` 和 ```SUICIDE``` 指令中的发送者、接收者和转移的值。 如果不同流的这些值不同，我们将报告 ```detect_money_concurrency``` 函数中的错误。

- Assertion fails

仅当使用选项 `-a` 时，此功能才处于活动状态。

该功能验证 Solidity 断言，如果程序中可以访问 INVALID 指令，则它会尝试报告 ```assert``` 失败。 因为 INVALID 可能是由 `assert` 以外的不同情况引起的，所以在某些情况下，由于 `assert` 生成的 INVALID 和其他类型的 INVALID 之间存在歧义，会导致误报。 目前，我们认为所有 INVALID 指令都源自 `assert`，除了那些遵循 ```JUMPDEST、CALLVALUE、ISZERO、PUSH、JUMPI``` 指令序列的指令。 为了找到包含断言失败的函数，我们记录导致 INVALID 指令的路径。 通过这条路径，我们可以回溯并找到导致 `symExec.py` 中 ```check_assertions``` 函数失败的顶级函数。

## *vargenerator.py*

这是一个实用程序类，用于提供分析所需的唯一符号变量。

## source_map.py

这是一个实用程序类，用于将有问题的操作码映射到源代码中。

## Tests

在 Oyente 中测试操作码，以根据存储和内存的最终状态检查操作码是否正确实现。 测试基于 [以太坊的虚拟机测试](http://ethdocs.org/en/latest/contracts-and-transactions/ethereum-tests/vm_tests/index.html)。

测试流程：

- 加载测试数据（使用 [here](https://github.com/ethereum/tests/tree/develop/VMTests) 中现有的 EVM 测试）
- 使用测试数据中指定的输入运行 oyente
- 将运行 oyente 后的结果（存储、内存和 gas ）与测试数据中指定的结果进行比较
- 报告错误

### *run_tests.py*

这是测试程序的主要入口点。 程序在文件夹 ```test_evm/test_data/``` 中加载一个特定的测试数据文件，并开始运行 `oyente.py `，在加载的测试数据中指定输入以获取从 `oyente.py` 返回的退出代码。 从这个退出代码测试程序可以报告错误。

### *evm_unit_test.py*

一个实用程序类，用于提取测试数据中的相关部分和字段（`code`、`storage`、`out`、`gas` 和 `exec` 部分中的 `gas`），运行测试，比较结果并返回一个退出代码。

### *symExec.py*

```compare_storage_and_gas_unit_test(global_state, analysis)``` 开始比较结果并在执行最终操作码后返回退出代码。