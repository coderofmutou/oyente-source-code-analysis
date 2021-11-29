# Oyente Tools Versions

## luongnguyen/oyente 版本

### docker 中的各工具版本

solc：Version: 0.4.21+commit.dfe3193c.Linux.g++

```shell
WARNING:root:You are using solc version 0.4.21, The latest supported version is 0.4.19
```

go：go version go1.8.3 linux/amd64

Geth：Version: 1.8.2-stable

evm：1.8.2-stable-b8b9f7f4

```shell
WARNING:root:You are using evm version 1.8.2. The supported version is 1.7.3
```





greeter.sol

```solidity
contract greeter {
    /* Declare variable admin which will store an address */
    address public admin;

    /* this function is executed at initialization and sets the owner of the contract */
    function greeter() {
        admin = msg.sender;
    }

    /* main function */
    function greet(bytes32 input) returns (bytes32) {
        if (input == "") {  return "Hello, World"; }

        /* Try it yourself: the joker
        if (input=="Who's there?") {
            // insert a joke here
        } else if (msg.value > 1000) {
            // a trillionth of an ether. It's a cheap joke.
            return "Knock knock!";
        }
        */

        return input;
    }

    /* Function to recover the funds on the contract */
    function kill() {
        if (msg.sender == admin) {
            suicide(admin);
        }
    }
}
```



## hrishioa/oyente 版本

### docker 中的各工具版本

solc：Version: 0.4.2-develop.2016.9.17+commit.212e0160.Linux.g++

z3：z3-4.4.1





## 本地原安装各工具版本

solc：Version: 0.8.10+commit.fc410830.Linux.g++

go：go version go1.17.3 linux/amd64

Geth：Version: 1.10.14-unstable

evm：evm version 1.10.14-unstable-4ebeca19-20211125

z3-solver：Z3 [version 4.8.14 - 64 bit]

WARNING:root:You are using an untested version of z3. 4.5.1 is the officially tested version
WARNING:root:You are using evm version 1.10.14. The supported version is 1.7.3
WARNING:root:You are using solc version 0.8.10, The latest supported version is 0.4.19
INFO:CryticCompile:Compilation warnings/errors on helloworld.sol:



## 正确安装各工具版本

solc：Version: 0.4.19+commit.c4cbbb05.Linux.g++

go：go version go1.7 linux/amd64

Geth：Version: 1.7.3-stable

evm：evm version 1.7.3-stable

z3-solver：Version: 4.5.1.0

crytic-compile：Version: 0.1.13

requests：Version: 2.26.0

web3：Version: 5.25.0