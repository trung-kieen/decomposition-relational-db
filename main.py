# Author: Nguyen Khac Trung Kien @trung-kieen

from copy import deepcopy
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
        return value.__str__() == self.__str__()



    @override
    def __hash__(self):
        return hash(self.__str__())

    @staticmethod
    def input_convert(raw):
        left, right = raw.split("->")
        lhs = set(prop.strip() for prop in left.strip().split(","))
        rhs = set(prop.strip() for prop in right.strip().split(","))
        return FD(lhs, rhs)



class FDSet(set[FD]):
    def __init__(self):
        super().__init__(self)

    @staticmethod
    def closure(FDs):
        """
        Usage:
            Return closure set of functional dependency can inference for Armstrong ruleset
        """
        inner_FDs = FDs.copy() # Avoid inplace change
        while True:
            old_len  = len(inner_FDs)
            Armstrong.ir2(inner_FDs)
            Armstrong.ir3(inner_FDs)
            no_more_inference_fd =  old_len == len(inner_FDs)
            if no_more_inference_fd:
                break
        return inner_FDs




class Armstrong:
    """
    Helper rule to find FD set closure
    Ignore IR1 for some reason =))
    """

    @staticmethod
    def ir2(FDs: FDSet):
        """
        IR2:
        Case 1
        A -> B <=> A -> AB
        AB -> CD <=> {AB -> BCD, AB -> ACD, AB -> ABCD} // all subset available for left hand side
        """

        old = FDs.copy()
        for fd in old:
            # Add all posible subset of left hand to right hand for additional rule
            subsets = subset(fd.lhs)
            for s in subsets:
                right_side = fd.rhs.union(s)
                FDs.add(FD(fd.lhs, right_side))


    @staticmethod
    def ir3(FDs: FDSet):
        """
        IR3: A -> B and B -> C then we have A -> C

        Additional i think it should reconstruct right hand side from composition to make sure transitive work
        For example:
        A -> B
        A -> C
        BC -> E

        Common sense
        A -> B and A -> C then we have A -> B, C
        BC -> E
        """
        old = FDs.copy()
        for fd1 in old:
            for fd2 in old:
                if fd1 == fd2: continue
                if fd1.rhs.issuperset(fd2.lhs):
                    tran_fd = FD(fd1.lhs, fd2.rhs)
                    FDs.add(tran_fd)
                if fd1.lhs.issubset(fd2.lhs) and  fd1.lhs.issubset(fd2.lhs):
                    composite_fd = FD(fd1.lhs, fd2.rhs.union(fd1.rhs))
                    FDs.add(composite_fd)

def subset(superset):
    s = list(superset)
    rs = []
    backtrack(rs, s, [], 0)
    return rs




def backtrack(res  , superset ,  subset , index  = 0 ):
    if subset:
        res.append(subset[:])
    for i in range(index , len( superset)):
        subset.append(superset[i])
        backtrack(res,  superset, subset , i + 1)
        subset.pop()





def minimal_cover(FDs : FDSet) -> FDSet:
    canonical_FDs = canonical(FDs)
    origin =  canonical_FDs.copy()
    infer_FDs =  canonical_FDs.copy()

    # Infer FD from Armstrong rule => if the infer exist in
    return FDSet()





def canonical(FDs: FDSet):
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
    fd2 = FD.input_convert("B -> C")
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
def test_minimal_cover():

    """
    Input: B->A, D -> A, AB -> D
    """
    fd1 = FD.input_convert("B-> A")
    fd2 = FD.input_convert("D-> A")
    fd3 = FD.input_convert("A, B-> D")
    pass

def test_ir2():
    """
    Input: B->A, D -> A, AB -> D
    Output: Result of additional rule
    {B} -> {A, B}
    {A, B} -> {A, D}
    {A, B} -> {A, B, D}
    {A, B} -> {D}
    {D} -> {A, D}
    {A, B} -> {B, D}
    {B} -> {A}
    {D} -> {A}}
    """
    fd1 = FD.input_convert("B-> A")
    fd2 = FD.input_convert("D-> A")
    fd3 = FD.input_convert("A, B-> D")
    FDs = FDSet()
    FDs.add(fd1)
    FDs.add(fd2)
    FDs.add(fd3)
    Armstrong.ir2(FDs)
    print(FDs)
def test_ir3():
    """
    Input: A -> B, B -> C, C -> D
    Output:
    A -> B, B -> C, C -> D
    A -> C, A -> D, B -> D,
    But might be more additional like: A -> B, C, D will appear it fine when we finding closure
    """
    fd1 = FD.input_convert("A-> B")
    fd2 = FD.input_convert("B-> C")
    fd3 = FD.input_convert("C-> D")
    FDs = FDSet()
    FDs.add(fd1)
    FDs.add(fd2)
    FDs.add(fd3)
    Armstrong.ir3(FDs)
    Armstrong.ir3(FDs)
    Armstrong.ir3(FDs)
    print(FDs)



def attribute_closure(attr_x, FDs: FDSet) -> set:
    """
    Use algorithm 15.1
    Input: single attr of list, set attr
    Output: set attr
    """
    x_closure  :  set
    if isinstance(attr_x, Iterable):
        x_closure = set(attr_x)
    else:
        x_closure = set()
        x_closure.add(attr_x)

    while True:
        old_len = len(x_closure)
        for fd in FDs:
            if x_closure.issuperset(fd.lhs):
                x_closure = x_closure.union(fd.rhs)
        apply_fds_not_add_new_property: bool = old_len == len(x_closure)
        if apply_fds_not_add_new_property:
            break
    return x_closure

def main():

    test_ir3()
    # test_fd_compare()
    # test_canonical()

    pass


if __name__ == "__main__":
    main()
