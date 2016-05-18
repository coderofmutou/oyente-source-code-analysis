import sys
import json
import os


def run_symExec(address):
    for index in range(1, 20):
        filename = "contracts/contract_data/contract" + str(index) + ".json"
        with open(filename) as json_file:
            c = json.load(json_file)
            # Find and write the source code to disk for disassembly
            if address in c:
                evm_file = address +".evm"
                code_file = address  + ".code"
                with open(code_file, 'w') as tfile:
                    tfile.write(c[address][1][2:])
                    tfile.write("\n")
                    tfile.close()

                sys.stdout.write("\tRunning disassembly on contract %s...\t\r" % address)
                sys.stdout.flush()
                os.system("cat %s | disasm > %s" % (code_file, evm_file))
                os.system("python symExec.py %s" % evm_file)
                #os.system("rm -rf %s*" % address)


def main():
    if (len(sys.argv) < 2):
        print "Usage: python special_run.py <list-of-address>"
        print "Example: python check_concurrency.py 0xcbabcbcbcbcbcbcbcbcbcb"
        return

    for i in xrange(1, len(sys.argv)):
        run_symExec(sys.argv[i])


if __name__ == '__main__':
    main()