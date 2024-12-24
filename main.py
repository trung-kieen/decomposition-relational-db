# Author: Nguyen Khac Trung Kien @trung-kieen

from copy import deepcopy
from dataclasses import dataclass
from typing import Iterable, override, Self

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
    def __init__(self, *args):
        super().__init__(self)
        for fd in args:
            self.add(fd)
    def iscover(self, other:Self ) -> bool:
        # https://www.javatpoint.com/dbms-equivalence-of-functional-dependency
        for fd in other:
            attrs = fd.lhs

            if not AttributeSets.closure(attrs, self).issuperset(AttributeSets.closure(attrs, other)):
                return False
        return True


class FDSets:
    """
    Helper method for FDSet
    FDSet is a set of immutable FD so it guarantee unique value in this collection.
    """
    @staticmethod
    def closure(FDs) -> FDSet:
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


    @staticmethod
    def canonical(FDs):
        s = set()
        for fd in FDs:
            s = s.union(fd.canonical_extract())
        return s




    @staticmethod
    def equivalent(a : FDSet, b :FDSet ):
        return a.iscover(b) and b.iscover(a)

    @staticmethod
    def minimal_cover(FDs : FDSet) -> FDSet:
        """
        Algorithm 15.2
        """

        canonical_FDs = FDSets.canonical(FDs)



        eliminated_lhs_fds = FDSets.minimal_lhs(canonical_FDs)

        print(eliminated_lhs_fds)

        # Infer FD from Armstrong rule => if the infer exist in
        return FDSet()



    @staticmethod
    def minimal_lhs(FDs):


        """
        If {F - {X -> A}} union {X - {B} -> A} is equivalent to original F
        then replace X->A in original F with (X - {B} -> A)
        X -> A  = target_fd
        B = attr
        X - B  = eliminated_lhs_fds
        """

        def fd_minus_attr_lhs(fd: FD, attr):
            f = deepcopy(fd)
            f.lhs.remove(attr)
            return f


        eliminated_fds =  FDs.copy()
        for fd in list(FDs):  # Set is unorder data structure so not allow remove item when iterator itself
            target_fd = fd.copy() # This FD may be remove attr inplace
            for attr in list(fd.lhs):
                fd_minus_attr = fd_minus_attr_lhs(fd, attr)
                eliminated_lhs_fds = (eliminated_fds - {target_fd}) + {fd_minus_attr}

                if  len(fd_minus_attr.lhs) > 0 and  FDSets.equivalent(eliminated_lhs_fds, FDs):
                    eliminated_fds.remove(target_fd)
                    eliminated_fds.add(eliminated_lhs_fds)
                    target_fd = eliminated_lhs_fds

        return eliminated_fds




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

        for fd in list(FDs):
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
        (UPDATE this is IR5 but ok if add it to IR3?? TODO  refactor )
        """
        for fd1 in list(FDs):
            for fd2 in list(FDs):
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
    c = FDSets.canonical(s)
    if FD.input_convert("A -> B") not in c: print("ERROR canonical")
    if FD.input_convert("A -> C") not in c: print("ERROR canonical")
    if FD.input_convert("B -> C") not in c: print("ERROR canonical")
    if FD.input_convert("A, B -> C") not in c: print("ERROR canonical")
def test_fd_compare():
    fd1 = FD.input_convert("A-> B")
    fd2 = FD.input_convert("A-> B")
    fd3 = FD.input_convert("A-> C")
    if fd1 != fd2: print("ERROR compare same FD")
    if fd1 == fd3: print("ERROR compare difference FD")



def test_fd_creation():
    FD1_str = "a, b -> c, d"
    fd1 = FD.input_convert(FD1_str)
    FD2_str = "a -> b, e"
    fd2 = FD.input_convert(FD2_str)
    fd3 = FD(["a", "b"], ["c", "d"])
    fd4 = FD(["a"], ["b", "e"])


    if fd1 != fd3: print("ERROR creation from string")
    if fd2 != fd4: print("ERROR creation from string")

def test_minimal_cover():

    """
    Input: B->A, D -> A, AB -> D
    """
    fd1 = FD.input_convert("B-> A")
    fd2 = FD.input_convert("D-> A")
    fd3 = FD.input_convert("A, B-> D")
    # TODO
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
    # print(FDs)
    if FD.input_convert("B -> A, B") not in FDs: print("ERROR IR2")
    if FD.input_convert("A, B -> A, B, D") not in FDs: print("ERROR IR2")
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
    fds = FDSet()
    fds.add(fd1)
    fds.add(fd2)
    fds.add(fd3)
    Armstrong.ir3(fds)
    Armstrong.ir3(fds)
    Armstrong.ir3(fds)
    if FD.input_convert("A -> C") not in fds: print("ERROR transitive")
    if FD.input_convert("A -> D") not in fds: print("ERROR transitive")
    # print(fds)

def test_attr_closure():
    fds = FDSet(
        FD.input_convert("A -> C, D"),
        FD.input_convert("E -> A , H ")
    )
    attr_closure = AttributeSets.closure(AttributeSet("E"), fds)

    a = ["A", "E", "H" , "C", "D"]
    for v in a:
        if v not in attr_closure: print("ERROR attr closure")

def test_fds_equivalent():
    FD1 = FDSet(FD.input_convert("A-> B"), FD.input_convert("B-> C"), FD.input_convert("A, B-> D"))
    FD2 = FDSet(FD.input_convert("A -> B"), FD.input_convert("B-> C"), FD.input_convert("A-> C"), FD.input_convert("A-> D"))

    if not FDSets.equivalent(FD1, FD2): print("ERROR compare to equivalent fds")


def test_fds_equivalent_2():
    # FD1 = FDSet(FD.input_convert("A -> B"), FD.input_convert("B-> C"))
    # FD2 = FDSet(FD.input_convert("A -> C"), FD.input_convert("A -> B"), FD.input_convert("A-> C"))
    # print(*sorted(FDSets.closure(FD1), key = lambda x: list(x.lhs)[0] ) , sep = "\n", end = "\n =============== \n")
    # print(*sorted(FDSets.closure(FD2), key = lambda x: list(x.lhs)[0] ) , sep = "\n", end = "\n =============== \n")
    # if not FDSets.equivalent(FD1, FD2): print("ERROR compare to equivalent fds")

    FD1 = FDSet(
        FD.input_convert("A -> C"),
        FD.input_convert("A, C -> D"),
        FD.input_convert("E -> A, D"),
        FD.input_convert("E-> H"))
    FD2 = FDSet(
        FD.input_convert("A -> C, D"),
        FD.input_convert("E  -> A, H "))
    # print(*sorted(FDSets.closure(FD1), key = lambda x: list(x.lhs)[0] ) , sep = "\n", end = "\n =============== \n")
    # print(*sorted(FDSets.closure(FD2), key = lambda x: list(x.lhs)[0] ) , sep = "\n", end = "\n =============== \n")
    if not FDSets.equivalent(FD1, FD2): print("ERROR compare to equivalent fds")

class AttributeSet(set[str]):
    def __init__(self, *args):
        for v in args:
            self.add(v)

class AttributeSets:
    """
    Helper method work around attribute in relation
    """


    @staticmethod
    def closure(atrs: AttributeSet, FDs: FDSet) -> set:
        """
        Use algorithm 15.1
        Input: single attr of list, set attr
        Output: set attr
        """
        x_closure   = atrs.copy()
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

    # TODO: Convert pure unit test not base on language
    test_fd_compare()
    test_ir3()
    test_ir2()
    test_fd_creation()
    test_attr_closure()
    test_fds_equivalent()
    test_fds_equivalent_2()
    test_canonical()


    pass


if __name__ == "__main__":
    main()
