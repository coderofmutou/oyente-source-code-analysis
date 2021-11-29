# 写在前面
1. 当你阅读到这篇博客时，大概率你已经阅读并尝试过 Oyente 官方安装指导，甚至可能还在其它地方搜过安装教程，如果没有就当我没说。。。
2. 那为什么在有各种版本的教程的情况下我依旧去写一个新的教程呢？这是因为我觉得其它教程解释的不够完整，安装下来容易出现问题。所以我选择花费时间去写一个我认为相对完整一点的安装教程，希望能帮助大家，能让大家少走一点弯路，不要浪费太多时间在工具的安装上。
3. 本教程不是唯一的安装方法，可能还有其他的方法。
4. 如何在 Docker 中安装就不多说了，比较简单，跟着官方文档走就行了，不需要考虑环境问题。本博客主要介绍在 Ubuntu 中的安装。
5. Ubuntu 更换国内软件源，go 和 python 更换国内下载源应该不需要多说吧？
6. 使用系统版本：Ubuntu 18.04

# 几个坑

1. python 的版本要大于 3.5，很多错误都是由于 python 的版本错误而导致的。如果同时有 python2 和 python3，所有命令使用 python3 和 pip3，不要用python 和 pip/pip2（如果你没安装python2，python 命令就是指代 python3，那你可以选择使用 python 命令。

2. Oyente 目前只支持 0.4.19 以下的 solidity 版本，所以直接按照官方文档指导的方法来安装是不行的，最好的办法是使用 solc-select 来管理安装不同版本的solidity。以下是安装高版本运行后的错误提示：

   ```
   WARNING:root:You are using solc version 0.8.10, The latest supported version is 0.4.19
   ```

3. Oyente 目前只支持 geth 1.7.3 和 evm 1.7.3 。以下是安装高版本运行后的错误提示：

   ```
   WARNING:root:You are using evm version 1.10.14. The supported version is 1.7.3
   ```

4. 安装 老版本的 geth 1.7.3 可能也会带来一个坑，geth 1.7.3 需要 go 的版本大于等于 1.7，但是 go 的版本过高在构建 geth 时也会出现问题，在安装 go-ethereum v1.7.3 部分再详细说明。

5. Oyente 目前只支持 z3. 4.5.1 。以下是安装高版本运行后的错误提示：

   ```
   WARNING:root:You are using an untested version of z3. 4.5.1 is the officially tested version
   ```

6. Oyente 官方文档中没有提到需要安装 crytic_compile 库，但是 input_helper 中又引入了这个库，所以我们需要额外通过 pip3 对其进行安装。但 crytic-compile 库安装版本不可以超过 v0.1.13，否则会出现错误：

   ```
   INFO:CryticCompile:Compilation warnings/errors on *.sol
   ```

# 安装

安装 python3、go 等应该不需要强调了吧。。。

## 1. 安装 solc 0.4.19

```shell
# 安装 solc-select
pip3 install solc-select

# 使用 solc-select 安装 solc 0.4.19
solc-select install 0.4.19

# 使用 solc 0.4.19 版本
solc-select use 0.4.19

# 查看 solc 版本，验证是否安装成功（如果无法查看，关闭终端重新打开）
solc --version 
```

## 2. 安装 [go-ethereum v1.7.3](https://github.com/ethereum/go-ethereum)

```shell
# 克隆 go-ethereum
git clone https://github.com/ethereum/go-ethereum.git

# 切换分支
git checkout v1.7.3

# 构建 geth（使用 make geth 指定不会构建 evm）
# 如果这里报错，让你升级 go 版本，但你的 go 版本明明大于 1.7，那么可以重新安装个 go 1.7，安装方法自行百度。
# 就像我明明使用的是 go 1.17.3，远大于 go 1.7，但是也报上面的错，猜测是因为后续版本支持 go mod 有关。
make all

# 配置环境
sudo vim ~/.bashrc

#  增加 geth bin 目录到环境变量
# 以下路径根据实际安装路径进行修改
export PATH=$PATH:$HOME/go-ethereum/build/bin

# 退出并使修改命令生效
source ~/.bashrc

# 查看 geth 版本
geth version
```

## 3. 安装 z3-solver 4.5.1.0

```shell
# 通过 python3 来安装 z3-solver 4.5.1.0
pip3 install z3-solver==4.5.1.0
```

## 4. 安装 crytic-compile 0.1.13

```shell
pip3 install crytic-compile==0.1.13
```

## 5. （可选）安装 [Requests](https://github.com/kennethreitz/requests/) library

```shell
# 这个库不安装应该也没事
pip3 install requests
```

## 6. （可选）安装 [web3](https://github.com/pipermerriam/web3.py) library

```shell
# 这个库不安装应该也没事
pip3 install web3
```

## 7. 下载 Oyente

```shell
git clone https://github.com/enzymefinance/oyente.git
```



# 测试使用

## 1. 新建一个合约

```shell
# 新建目录
mkdir test

# 新建 .sol 智能合约
vim test.sol
```

**【注】这里不在 oyente/oyente 目录中直接新建一个合约进行测试是因为会报错，原因不明，有研究的小伙伴可以指点下。**



test.sol 合约

```solidity
pragma solidity >=0.4.19;

contract test {
    function helloworld() pure public returns (string)
    {
        return "hello world";
    }
}
```



## 2. 测试

```shell
# 进入 oyente 目录
cd ~/oyente/oyente

# 评估本地合约
python3 oyente.py -s ~/test/test.sol
```



执行结果如下：

```
INFO:root:contract /home/jie/test/test.sol:test:
INFO:symExec:   ============ Results ===========
INFO:symExec:     EVM Code Coverage:                     99.5%
INFO:symExec:     Integer Underflow:                     False
INFO:symExec:     Integer Overflow:                      False
INFO:symExec:     Parity Multisig Bug 2:                 False
INFO:symExec:     Callstack Depth Attack Vulnerability:  False
INFO:symExec:     Transaction-Ordering Dependence (TOD): False
INFO:symExec:     Timestamp Dependency:                  False
INFO:symExec:     Re-Entrancy Vulnerability:             False
INFO:symExec:   ====== Analysis Completed ======
```



# 参考文章

1. [enzymefinance/oyente: An Analysis Tool for Smart Contracts (github.com)](https://github.com/enzymefinance/oyente)
2. [hxy-daniel/oyente-study (github.com)](https://github.com/hxy-daniel/oyente-study)
3. [oyente—合约漏洞检测工具安装_5imple的博客-CSDN博客](https://blog.csdn.net/WSX756164967/article/details/117638669?ops_request_misc=%7B%22request%5Fid%22%3A%22163793284816780265472226%22%2C%22scm%22%3A%2220140713.130102334..%22%7D&request_id=163793284816780265472226&biz_id=0&utm_medium=distribute.pc_search_result.none-task-blog-2~all~sobaiduend~default-1-117638669.first_rank_v2_pc_rank_v29&utm_term=oyente&spm=1018.2226.3001.4187)
4. [Oyente搭建，框架结构以及helloworld案例解析(一)_小水的博客-CSDN博客](https://blog.csdn.net/narcissus2_/article/details/115832793)
5. [常用linux命令&&Ubuntu安装z3库及使用_Y1seco的博客-CSDN博客](https://blog.csdn.net/qq_45834505/article/details/117334215)

