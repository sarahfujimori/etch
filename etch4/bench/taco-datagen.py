import numpy as np
import sqlite3


def makeV(n=100, p=0.1):
    result = set()
    m = np.random.rand(n)
    it = np.nditer(m, flags=["multi_index"])
    for i in it:
        if i < p:
            result.add((int(it.multi_index[0]), float(i)))
    return result


def makeA(n=100, p=0.1):
    result = set()
    m = np.random.rand(n, n)
    it = np.nditer(m, flags=["multi_index"])
    for i in it:
        if i < p:
            result.add((int(it.multi_index[0]), int(it.multi_index[1]), float(i)))
    return result


def makeC(n=100, p=0.1):
    result = set()
    m = np.random.rand(n, n, n)
    it = np.nditer(m, flags=["multi_index"])
    for i in it:
        if i < p:
            result.add(
                (
                    int(it.multi_index[0]),
                    int(it.multi_index[1]),
                    int(it.multi_index[2]),
                    float(i),
                )
            )
    return result


def main():
    c = sqlite3.connect("./data/pldi.db")
    c.execute("DROP TABLE IF EXISTS A")
    c.execute("DROP TABLE IF EXISTS B")
    c.execute("DROP TABLE IF EXISTS C")
    c.execute("DROP TABLE IF EXISTS V")
    c.execute("CREATE TABLE A(i INTEGER NOT NULL, j INTEGER NOT NULL, v REAL NOT NULL)")
    c.execute("CREATE TABLE B(i INTEGER NOT NULL, j INTEGER NOT NULL, v REAL NOT NULL)")
    c.execute(
        "CREATE TABLE C(i INTEGER NOT NULL, j INTEGER NOT NULL, k INTEGER NOT NULL, v REAL NOT NULL)"
    )
    c.execute("CREATE TABLE V(i INTEGER NOT NULL, v REAL NOT NULL)")
    print("A")
    c.executemany(f"INSERT INTO A VALUES(?,?,?)", makeA(1000))
    print("B")
    c.executemany(f"INSERT INTO B VALUES(?,?,?)", makeA(1000))
    print("C")
    c.executemany(f"INSERT INTO C VALUES(?,?,?,?)", makeC(100))
    print("V")
    c.executemany(f"INSERT INTO V VALUES(?,?)", makeV(1000))
    c.commit()


main()