# ランダムに問題を作って問題を解かせる
NVAR = 80
NCLAUSE = 320
MINISAT = "/root/minisat/build/release/bin/minisat"

import random
from subprocess import run
from unittest import result

def make_problem():
    with open("/root/minisat/build/problem/rand.cnf", mode="w") as f:
        f.write("p cnf "+str(NVAR)+" "+str(NCLAUSE)+"\n")
        for i in range(NCLAUSE):
            clause = ""
            for j in range(random.randint(1,NVAR)):
                clause += random.choice(["", "-"])
                clause += str(random.randint(1, NVAR)) + " "
            f.write(clause+"0\n")


def solve():
    problem = "/root/minisat/build/problem/rand.cnf"
    proof = "/root/minisat/build/problem/proof.drat"
    result = run([MINISAT ,"-verb=0", problem], capture_output=True, text=True)
    print(result.stdout)
    if len(result.stdout.split("\n")) != 3:
        print(result)
        exit()
    return result.returncode

if __name__ == "__main__":
    while True:
        make_problem()
        returncode = solve()