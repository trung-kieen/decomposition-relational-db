from dataclasses import dataclass
from typing import Iterable, override

# Use to make FD as immutable => able to add in set
def immutable_meta(name, bases, dct):
    class Meta(type):
        def __init__(cls, name, bases, dct):
            type.__setattr__(cls,"attr",set(dct.keys()))
            type.__init__(cls, name, bases, dct)

        def __setattr__(cls, attr, value):
            if attr not in cls.attr:
                raise AttributeError ("Cannot assign attributes to this class")
            return type.__setattr__(cls, attr, value)
    return Meta(name, bases, dct)



class FD():
    __metaclass__ = immutable_meta
    def __init__(self, lhs: Iterable, rhs: Iterable) -> None:
        """
        Example:
        FD: a, b -> c, d
        => lhs = set([a, b])
        => rhs = set([c, d])
        """
        self.lhs  = set(lhs)
        self.rhs  = set(rhs)

    def canonical_extract(self):
        """
        As canonical form FD only have one property on the right hand side
        Return a set of canonical
        """
        s = set()
        for r in self.rhs:
            s.add(FD(self.lhs , r))
        return s
    @override
    def __str__(self) -> str:
        left = "{" + ", ".join(self.lhs) + "}"
        right= "{" + ", ".join(self.rhs) + "}"
        s = left + " -> " + right
        return s

    @override
    def __repr__(self) -> str:
        return self.__str__()
    @override
    def __eq__(self, value: object, /) -> bool:
        if not isinstance(value, FD):
            return False
        return self.__str__  == value.__str__



    @override
    def __hash__(self):
        return hash(self.__str__)

    @staticmethod
    def input_convert(raw):
        left, right = raw.split("->")
        lhs = [prop.strip() for prop in left.strip().split(",")]
        rhs = [prop.strip() for prop in right.strip().split(",")]
        return FD(lhs, rhs)



def minimal_cover(FDs : set[FD]) -> set[FD]:
    canonical_FDs = canonical(FDs)
    return set()





def canonical(FDs: set[FD]):
    s = set()
    for fd in FDs:
        s = s.union(fd.canonical_extract())
    return s


class Relation:
    def __init__(self, name, FDs) -> None:
        self.name = name
        self.FDs  = FDs


def test_canonical():
    """
    INPUT:
    A -> BC
    B -> C
    A -> B
    AB -> C

    EXPECT:
    A -> B (Duplicate should be remove)
    A -> C
    B -> C
    AB -> C
    """
    fd1 = FD.input_convert("A -> B, C")
    fd2 = FD.input_convert("A -> B, C")
    fd3 = FD.input_convert("A -> B")
    fd4 = FD.input_convert("A, B -> C")
    s = set()
    s.add(fd1)
    s.add(fd2)
    s.add(fd3)
    s.add(fd4)
    c = canonical(s)
    print(c)
def test_fd_compare():
    fd1 = FD.input_convert("A-> B")
    fd2 = FD.input_convert("A-> B")
    fd3 = FD.input_convert("A-> C")
    print(fd1 == fd2)
    print(fd1 == fd3)



def test_fd_creation():
    FD1_str = "a, b -> c, d"
    fd1 = FD.input_convert(FD1_str)
    FD2_str = "a -> b, e"
    fd2 = FD.input_convert(FD2_str)
    print(fd1)
    print(fd2)

def main():


    test_canonical()





if __name__ == "__main__":
    main()
