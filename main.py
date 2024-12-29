# Author: Nguyen Khac Trung Kien @trung-kieen

import inspect
from copy import deepcopy
from os import name, system
from typing import Any, Iterable, Self, Union, override


# Use to make FD as immutable => able to add in set
def immutable_meta(name, bases, dct):
    class Meta(type):
        def __init__(cls, name, bases, dct):
            type.__setattr__(cls, "attr", set(dct.keys()))
            type.__init__(cls, name, bases, dct)

        def __setattr__(cls, attr, value):
            if attr not in cls.attr:
                raise AttributeError("Cannot assign attributes to this class")
            return type.__setattr__(cls, attr, value)

    return Meta(name, bases, dct)


class FD:
    __metaclass__ = immutable_meta

    def __init__(self, lhs: Iterable, rhs: Iterable) -> None:
        """
        Example:
        FD: a, b -> c, d
        => lhs = set([a, b])
        => rhs = set([c, d])
        """
        self.lhs: set[str] = set(lhs)
        self.rhs: set[str] = set(rhs)

    @classmethod
    def scan(cls):
        a = ui.scan(f"Enter FD: ")
        return cls.translate_semantic(a)

    @override
    def __str__(self) -> str:
        left = "{" + ", ".join(sorted(self.lhs)) + "}"
        right = "{" + ", ".join(sorted(self.rhs)) + "}"
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
    def translate_semantic(raw):
        """
        Translate natural language of FD to immutable object
        Using `->` to seprate left and right side
        Using comma to seprate attribute name
        Example: translate_semantic("A, B -> C")
        """
        left, right = raw.split("->")
        lhs = set(prop.strip() for prop in left.strip().split(","))
        rhs = set(prop.strip() for prop in right.strip().split(","))
        return FD(lhs, rhs)

    def attrs(self) -> set:
        return self.lhs.union(self.rhs)


class FDSet(set[FD]):
    def __init__(self, ir: Iterable | None = None):
        """
        Input a iterator of FD or None
        EX1:  a = FDSet() // Empty FDSet
        EX2:  b = FDSet([fd1, fd2])
        """
        super().__init__(self)
        if ir:
            for fd in ir:
                self.add(fd)

    def iscover(self, other: Self) -> bool:
        # https://www.javatpoint.com/dbms-equivalence-of-functional-dependency
        for fd in other:
            attrs = fd.lhs

            if not AttributeSets.closure(attrs, self).issuperset(
                AttributeSets.closure(attrs, other)
            ):
                return False
        return True

    def __sub__(self, other) -> Self:
        # https://stackoverflow.com/questions/10810926/can-a-python-class-return-a-new-instance-of-its-class
        return type(self)(self.copy() - other.copy())

    def __add__(self, other) -> Self:
        a = self.copy().union(other.copy())
        return type(self)(list(a))

    def attrs(self):
        s = set()
        for fd in self:
            s = s.union(fd.attrs())
        return s


class Armstrong:
    """
    Helper rule to find FD set closure
    Ignore IR1
    """

    @staticmethod
    def apply_ir2(fds: FDSet):
        """
        IR2:
        Case 1
        A -> B <=> A -> AB
        AB -> CD <=> {AB -> BCD, AB -> ACD, AB -> ABCD} // all subset available for left hand side
        """

        for fd in list(fds):
            # Add all posible subset of left hand to right hand for additional rule
            subsets = subset(fd.lhs)
            for s in subsets:
                right_side = fd.rhs.union(s)
                fds.add(FD(fd.lhs, right_side))

    @staticmethod
    def apply_ir4(fds: FDSet):
        for fd in fds:
            subsets = subset(fd.lhs)
            fds.add(FD(fd.lhs, subsets))

    @staticmethod
    def apply_ir3_ir5(fds: FDSet):
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
        for fd1 in list(fds):
            for fd2 in list(fds):
                if fd1 == fd2:
                    continue
                if fd1.rhs.issuperset(fd2.lhs):
                    tran_fd = FD(fd1.lhs, fd2.rhs)
                    fds.add(tran_fd)
                if fd1.lhs.issubset(fd2.lhs) and fd1.lhs.issubset(fd2.lhs):
                    composite_fd = FD(fd1.lhs, fd2.rhs.union(fd1.rhs))
                    fds.add(composite_fd)


class FDSets:
    """
    Helper method for FDSet
    FDSet is a set of immutable FD so it guarantee unique value in this collection.
    """

    @staticmethod
    def closure(fds) -> FDSet:
        """
        Usage:
            Return closure set of functional dependency can inference for Armstrong ruleset
        """
        inner_fds = fds.copy()  # Avoid inplace change
        while True:
            old_len = len(inner_fds)
            Armstrong.apply_ir2(inner_fds)
            Armstrong.apply_ir3_ir5(inner_fds)
            no_more_inference_fd = old_len == len(inner_fds)
            if no_more_inference_fd:
                break
        return inner_fds

    @staticmethod
    def copy(fds: FDSet) -> FDSet:
        a = fds.copy()
        return FDSet(list(a))

    @staticmethod
    def canonical_extract(fd: FD) -> FDSet:
        """
        As canonical form FD only have one property on the right hand side
        Return a set of canonical
        """
        s = FDSet()
        for r in fd.rhs:
            s.add(FD(fd.lhs, r))
        return s

    @staticmethod
    def canonical(fds: FDSet) -> FDSet:
        s = FDSet()
        for fd in fds:
            for r in fd.rhs:
                s.add(FD(fd.lhs, r))
        return s

    @staticmethod
    def equivalent(a: FDSet, b: FDSet) -> bool:
        return a.iscover(b) and b.iscover(a)

    @staticmethod
    def minimal_cover(fds: FDSet) -> FDSet:
        """
        Algorithm 15.2
        """

        canonical_fds = FDSets.canonical(fds)

        eliminated_lhs_fds = FDSets._minimal_lhs(canonical_fds)

        # Remove redundance
        for fd in list(eliminated_lhs_fds):
            test_removed_fd_fds = eliminated_lhs_fds - FDSet([fd])
            if FDSets.equivalent(eliminated_lhs_fds, test_removed_fd_fds):
                eliminated_lhs_fds = test_removed_fd_fds

        # merge right hand side
        lsh_sorted = sorted(eliminated_lhs_fds, key=lambda x: x.lhs)
        if len(lsh_sorted) == 0:
            return FDSet()

        left = lsh_sorted[0].lhs

        merged_fds = FDSet()

        right_attrs_to_merge = lsh_sorted[0].rhs.copy()
        for i in range(1, len(lsh_sorted)):
            if left == lsh_sorted[i].lhs:
                right_attrs_to_merge = right_attrs_to_merge.union(
                    lsh_sorted[i].rhs)
            else:
                merged_fds.add(FD(left, right_attrs_to_merge))
                right_attrs_to_merge = lsh_sorted[i].rhs.copy()
                left = lsh_sorted[i].lhs
        else:
            merged_fds.add(FD(left, right_attrs_to_merge))

        return merged_fds

    @staticmethod
    def _minimal_lhs(fds: FDSet):
        """
        If {F - {X -> A}} + {X - {B} -> A} is equivalent to original F
        then replace X->A in original F with (X - {B} -> A)
        X -> A  = target_fd
        B = attr
        X - B  = eliminated_lhs_fds
        """

        def fd_minus_attr_lhs(fd: FD, attr):
            f = deepcopy(fd)
            f.lhs.remove(attr)
            return f

        eliminated_fds: FDSet = fds

        for fd in list(
            fds
        ):  # Set is unorder data structure so not allow remove item when iterator itself
            target_fd = fd  # This FD may be remove attr inplace

            if len(fd.lhs) <= 1:
                continue
            for attr in list(fd.lhs):
                fd_minus_attr = fd_minus_attr_lhs(fd, attr)
                B = FDSet([target_fd])
                A = FDSet([fd_minus_attr])
                eliminated_lhs_fds = (eliminated_fds - B) + A

                if len(fd_minus_attr.lhs) > 0 and FDSets.equivalent(
                    eliminated_lhs_fds, fds
                ):
                    eliminated_fds = eliminated_lhs_fds
                    target_fd = fd_minus_attr

        return eliminated_fds


def subset(superset):
    s = list(superset)
    rs = []
    backtrack(rs, s, [], 0)
    return rs


def backtrack(res, superset, subset, index=0):
    if subset:
        res.append(subset[:])
    for i in range(index, len(superset)):
        subset.append(superset[i])
        backtrack(res, superset, subset, i + 1)
        subset.pop()


class Relation:
    _name_counter = 0

    def __init__(
        self,
        attrs: set | None = None,
        fds: FDSet | None = None,
        name: str = "",
        candidate_keys: Iterable[set] = [],
        primary_key: None | set = None,
    ) -> None:
        """
        Example 1: Relation construct from FDSet will use all attribute exist in FDSet and primary_key define following previous data
        Relation(Fds = FDSet([
            FD.translate_semantic("A -> B"),
            FD.translate_semantic("A -> C"),
        ]))
        So from FDSet can determine:
        self.attrs = set(["A", "B", "C"])
        self.primary_key = "A"

        Example 2: Relation construct from attribute and relation name ony will use composite of all attribute as primary_key
        Relation.translate_semantic("R1 (A, B, C)")
        Then we have:
        self.attrs = set(["A", "B", "C"])
        self.primary_key = set(["A", "B", "C"])
        """
        self.name = name if name else self.__class__.generate_name()
        self.fds = fds
        # one of the candidate key will be primary key
        self.candidate_keys = candidate_keys

        if attrs:
            self.attrs = attrs
        elif fds:
            self.attrs = fds.attrs()
        else:
            self.attrs = set()

        self.primary_key = primary_key if primary_key else None
        if not self.primary_key:
            self.primary_key = self.get_primary_key()

    @classmethod
    def generate_name(cls):
        cls._name_counter += 1
        return "R" + str(cls._name_counter)

    def __repr__(self) -> str:
        return self.__str__()

    @override
    def __str__(self):
        attrs_str = ", ".join(self.attrs)
        relation_name = self.name + "({0})".format(attrs_str)

        if self.primary_key:
            relation_name += "\n" + \
                f"Primary Key: {attributes_repr(self.primary_key)}"

        if self.candidate_keys:
            candidate_name = "Unique: "
            candidate_name += ", ".join(
                attributes_repr(key) for key in self.candidate_keys
            )
            relation_name += "\n" + candidate_name
        if self.fds:
            relation_name += "\n" + self.fds.__str__()
        return relation_name

    @staticmethod
    def translate_semantic(raw: str):
        """
        Example:
        Input: raw = R1(A, B, C, D)
        """
        raw = raw.strip()
        name_resparete = raw.find("(")
        name = raw[:name_resparete]
        attrs = set(raw[name_resparete:].strip()[1:-1].split(","))
        return Relation(attrs=attrs, name=name)

    def _isvalid_key(self):
        if not getattr(self, "primary_key", ""):
            return False
        if self.primary_key and self.fds:
            attr_closure = AttributeSets.closure(self.primary_key, self.fds)
            if attr_closure == self.attrs:
                return True
        return False

    def get_primary_key(self):
        if self._isvalid_key():
            return self.primary_key
        elif not self.fds:
            return None
        else:
            return AttributeSets.primary_key(self.attrs, self.fds)

    def to_3nf(self) -> Iterable[Self]:
        """
        NOTICE: current it show not unique value return in many run times
        A relation can be divide in many way that valid 3NF base on hash value of set order change will matter
        """

        pk = self.get_primary_key()
        if not pk:
            ui.echo("Missing primary for relation can not extract to 3nf")
            return []
        if not self.fds:
            UserInteraction.echo("Can not decompose relation without fds")
            return []
        min_fd = FDSets.minimal_cover(self.fds)
        # SORT?
        relation_fd = []
        relation_attribute_closure = []
        for fd in list(min_fd):
            # Can not use hash to table to mapping set
            def add_fd_to_relation(fd: FD):
                """
                If contain FD1: A, B -> C, D and FD2: D -> B then 2 dependency will use to create on relation because FD1 have all attribute of FD2
                """
                i = 0
                fd_attrs = fd.attrs()
                for i in range(len(relation_attribute_closure)):
                    if fd_attrs.issubset(relation_attribute_closure[i]):
                        relation_fd[i].append(fd)
                        return
                    elif fd_attrs.issuperset(relation_attribute_closure[i]):
                        relation_fd[i].append(fd)
                        relation_attribute_closure[i] = fd_attrs
                        return

                relation_attribute_closure.append(fd_attrs)
                relation_fd.append([fd])
                return

            add_fd_to_relation(fd)

        relations = []
        have_relation_cover_pk = False
        # Constructor relation from list of minimal cover fd
        for i in range(len(relation_fd)):
            attrs = relation_attribute_closure[i]
            r = Relation(attrs=attrs, fds=FDSet(relation_fd[i]))
            relations.append(r)
            if attrs.issuperset(pk):
                have_relation_cover_pk = True

        # Add global key
        if not have_relation_cover_pk:
            r = Relation(attrs=pk, fds=FDSet())
            relations.append(r)
        return relations

    def violent_bcnf(self, fd: FD) -> bool:
        """
        A fd is not violent bncf when left hand side attribute determine all attribute in relation
        Example 1:
        R7(A, L, P, C)
        {P} -> {A, C, L} valid because P determine relation
        {C, L} -> {A, P} valid because C, L determine relation
        """
        lhs = fd.lhs
        left_fd_attrs_closure = AttributeSets.closure(lhs, self.fds)
        return left_fd_attrs_closure != self.attrs

    def to_bcnf(self) -> list:

        # Not require
        # self.fds = FDSets.minimal_cover(self.fds)

        # Use recursive
        if not self.fds:
            return [self]
        stack: Iterable = [self]
        results = []

        while stack:
            relation = stack.pop()
            if not relation.fds:
                continue
            for fd in relation.fds:
                if relation.violent_bcnf(fd):
                    # Create relation XA form fd X -> A
                    sub_fd = FDSet([fd])
                    origin_fd = relation.fds - sub_fd

                    a = Relation(fds=sub_fd)
                    b = Relation(fds=origin_fd)
                    stack.append(a)
                    stack.append(b)

                    # Recursive decompose to bncf base on stack
                    break

            else:
                # No violent fd found => BCNF relation
                results.append(relation)

        return results


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
    fd1 = FD.translate_semantic("A -> B, C")
    fd2 = FD.translate_semantic("B -> C")
    fd3 = FD.translate_semantic("A -> B")
    fd4 = FD.translate_semantic("A, B -> C")
    s = set()
    s.add(fd1)
    s.add(fd2)
    s.add(fd3)
    s.add(fd4)
    c = FDSets.canonical(s)
    if FD.translate_semantic("A -> B") not in c:
        print("ERROR canonical")
    if FD.translate_semantic("A -> C") not in c:
        print("ERROR canonical")
    if FD.translate_semantic("B -> C") not in c:
        print("ERROR canonical")
    if FD.translate_semantic("A, B -> C") not in c:
        print("ERROR canonical")


def test_fd_compare():
    fd1 = FD.translate_semantic("A-> B")
    fd2 = FD.translate_semantic("A-> B")
    fd3 = FD.translate_semantic("A-> C")
    if fd1 != fd2:
        print("ERROR compare same FD")
    if fd1 == fd3:
        print("ERROR compare difference FD")


def test_fd_creation():
    FD1_str = "a, b -> c, d"
    fd1 = FD.translate_semantic(FD1_str)
    FD2_str = "a -> b, e"
    fd2 = FD.translate_semantic(FD2_str)
    fd3 = FD(["a", "b"], ["c", "d"])
    fd4 = FD(["a"], ["b", "e"])

    if fd1 != fd3:
        print("ERROR creation from string")
    if fd2 != fd4:
        print("ERROR creation from string")


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
    fd1 = FD.translate_semantic("B-> A")
    fd2 = FD.translate_semantic("D-> A")
    fd3 = FD.translate_semantic("A, B-> D")
    fds = FDSet()
    fds.add(fd1)
    fds.add(fd2)
    fds.add(fd3)
    Armstrong.apply_ir2(fds)
    # print(fds)
    if FD.translate_semantic("B -> A, B") not in fds:
        print("ERROR IR2")
    if FD.translate_semantic("A, B -> A, B, D") not in fds:
        print("ERROR IR2")


def test_ir3_ir5():
    """
    Input: A -> B, B -> C, C -> D
    Output:
    A -> B, B -> C, C -> D
    A -> C, A -> D, B -> D,
    But might be more additional like: A -> B, C, D will appear it fine when we finding closure
    """
    fd1 = FD.translate_semantic("A-> B")
    fd2 = FD.translate_semantic("B-> C")
    fd3 = FD.translate_semantic("C-> D")
    fds = FDSet()
    fds.add(fd1)
    fds.add(fd2)
    fds.add(fd3)
    Armstrong.apply_ir3_ir5(fds)
    Armstrong.apply_ir3_ir5(fds)
    Armstrong.apply_ir3_ir5(fds)
    if FD.translate_semantic("A -> C") not in fds:
        print("ERROR transitive")
    if FD.translate_semantic("A -> D") not in fds:
        print("ERROR transitive")


def test_ir4():
    # TODO:
    pass


def test_attr_closure():
    fds = FDSet(
        [FD.translate_semantic("A -> C, D"),
         FD.translate_semantic("E -> A , H ")]
    )
    attr_closure = AttributeSets.closure(set(["E"]), fds)

    a = ["A", "E", "H", "C", "D"]
    for v in a:
        if v not in attr_closure:
            print("ERROR attr closure")


def test_fds_equivalent():
    FD1 = FDSet(
        [
            FD.translate_semantic("A-> B"),
            FD.translate_semantic("B-> C"),
            FD.translate_semantic("A, B-> D"),
        ]
    )
    FD2 = FDSet(
        [
            FD.translate_semantic("A -> B"),
            FD.translate_semantic("B-> C"),
            FD.translate_semantic("A-> C"),
            FD.translate_semantic("A-> D"),
        ]
    )

    if not FDSets.equivalent(FD1, FD2):
        print("ERROR compare to equivalent fds")


def test_lhs_minimize():
    """
    Input:
    B -> A
    D -> A
    A, B -> D  (Check if this left hand side is redundance)
    Output:
    B -> A
    D -> A
    B -> D (Ok  B -> AB and B -> D so we know that B -> D)
    """
    fds = FDSet(
        [
            FD.translate_semantic("B -> A"),
            FD.translate_semantic("D -> A"),
            FD.translate_semantic("A, B -> D"),
        ]
    )
    rs = FDSets._minimal_lhs(fds)
    if rs.__contains__(FD.translate_semantic("A, B -> D")):
        print("ERROR eliminated left hand side")
    if not rs.__contains__(FD.translate_semantic("B -> D")):
        print("ERROR eliminated left hand side")


def test_fds_equivalent_2():

    FD1 = FDSet(
        [
            FD.translate_semantic("A -> C"),
            FD.translate_semantic("A, C -> D"),
            FD.translate_semantic("E -> A, D"),
            FD.translate_semantic("E-> H"),
        ]
    )
    FD2 = FDSet(
        [FD.translate_semantic("A -> C, D"),
         FD.translate_semantic("E  -> A, H ")]
    )
    if not FDSets.equivalent(FD1, FD2):
        print("ERROR compare to equivalent fds")


def test_minimal_cover():
    A = FDSet(
        [
            FD.translate_semantic("B -> A"),
            FD.translate_semantic("D -> A"),
            FD.translate_semantic("A, B -> D"),
        ]
    )

    A_min = FDSets.minimal_cover(A)
    if len(A_min) != 2:
        print("ERROR: minimial cover")
    if FD.translate_semantic("B -> D") not in A_min:
        print("ERROR: minimial cover")
    if FD.translate_semantic("D -> A") not in A_min:
        print("ERROR: minimial cover")


def test_find_primary_key():
    attrs = set(["A", "B", "C", "D", "E", "F", "G", "H", "I", "J"])

    fds = FDSet(
        [
            FD.translate_semantic("A, B -> C"),
            FD.translate_semantic("B, D -> E, F"),
            FD.translate_semantic("A, D -> G, H"),
            FD.translate_semantic("A -> I"),
            FD.translate_semantic("H -> J"),
        ]
    )
    r = AttributeSets.primary_key(attrs, fds)
    if r != set(["A", "B", "D"]):
        print("ERROR find key")


def test_decompose_to_3nf():
    fds = FDSet(
        [
            FD.translate_semantic("P -> L, C, A"),
            FD.translate_semantic("L, C -> A, P"),
            FD.translate_semantic("A -> C"),
        ]
    )
    attrs = fds.attrs()
    test_lst_atrs = ["P", "L", "C", "A"]
    for v in test_lst_atrs:
        if v not in attrs:
            print("ERROR get attribute value from set of function dependency")

    r = Relation(fds=fds)
    sub_relations = r.to_3nf()
    test_relation_preservation(r, sub_relations)


def test_decompose_to_bcnf():
    # Will not preservation dependency
    fds = FDSet(
        [
            FD.translate_semantic("P -> L, C, A"),
            FD.translate_semantic("L, C -> A, P"),
            FD.translate_semantic("A -> C"),
        ]
    )
    r = Relation(fds=fds)

    a = r.to_bcnf()
    test_relation_preservation(r, a, False)


def test_relation_preservation(
    super_relation: Relation,
    sub_relations: Iterable[Relation],
    check_fds_preservation=True,
) -> None:

    fds = super_relation.fds
    attrs = super_relation.attrs

    if not fds and not attrs:
        print("ERROR when try to compare a empty relation after decomposition")
        return

    total_sub_attrs = set()
    total_sub_fds = FDSet()
    for relation in sub_relations:
        total_sub_fds = total_sub_fds + relation.fds
        total_sub_attrs = total_sub_attrs.union(relation.attrs)

    # Check new relation is equivalent with before decompose
    if check_fds_preservation:
        if not FDSets.equivalent(fds, total_sub_fds):
            print("ERROR 3nf relation not preservation")
    if attrs != total_sub_attrs:
        print("ERROR property preservation")


class AttributeSets:
    """
    Helper method work around attribute in relation
    """

    @staticmethod
    def closure(attrs: set, fds: FDSet) -> set:
        """
        Use algorithm 15.1
        Input: single attr of list, set attr
        Output: set attr
        """
        x_closure = attrs.copy()
        while True:
            old_len = len(x_closure)
            for fd in fds:
                if x_closure.issuperset(fd.lhs):
                    x_closure = x_closure.union(fd.rhs)
            apply_fds_not_add_new_property: bool = old_len == len(x_closure)
            if apply_fds_not_add_new_property:
                break
        return x_closure

    @staticmethod
    def primary_key(attrs: set, fds: FDSet) -> set:
        if len(fds) == 0:
            return attrs
        key = attrs
        for attr in list(key):
            reduce_attrs = key - set([attr])
            if AttributeSets.is_superkey(reduce_attrs, attrs, fds):
                key = reduce_attrs
        return key

    @staticmethod
    def is_superkey(attrs_check: set, all_attrs: set, fds: FDSet) -> bool:
        return AttributeSets.closure(attrs_check, fds) == all_attrs


def attributes_repr(collection: Iterable):
    return "({0})".format({", ".join(collection)})


class UserInteraction:
    @staticmethod
    def scan(prompt):
        while True:
            try:
                ans = input(prompt)
                return ans
            except Exception as ex:
                print("Ops! Something went wrong")

    @staticmethod
    def interact_input(inline_prompt):
        input(inline_prompt + "\n>")

    @staticmethod
    def menu_get_option(options: list[str]):
        """
        Return index select from menu
        """

        for idx, opt in enumerate(options):
            s = "[{0}] {1}".format(idx, opt.title())
            UserInteraction.echo(s)
        while True:
            ans = UserInteraction.scan("Choice: ")
            if ans.isdigit() and int(ans) in range(len(options)):
                return int(ans)

    @staticmethod
    def echo(
        *args,
        **kwargs,
    ):
        UserInteraction.clear()
        print(args, kwargs)

    @staticmethod
    def input_fd():
        print("input fd")
        return FD.translate_semantic("A -> B")

    @staticmethod
    def input_fds():
        print("input fds")
        return FDSet([FD.translate_semantic("C -> B")])

    @staticmethod
    def input_relation():
        print("input relation")
        return Relation.translate_semantic("R(A, B, C, D)")

    @staticmethod
    def input_attrs():
        print("input attrs")
        return set(list("ABCD"))

    @staticmethod
    def clear():

        # for windows
        if name == "nt":
            _ = system("cls")

        else:
            _ = system("clear")


def inject_args(f):
    def match_type_or_contain(A: type, B: type | Union[Any, Any]):
        try:
           return A == B or A in B.__args__
        except Exception as ex:
            return False
    def wrapper(*args, **kwargs):
        func_prototype = inspect.signature(f)

        params = func_prototype.parameters

        ui = UserInteraction
        datatype_to_input_method = {
            set: ui.input_attrs,
            FD: ui.input_fd,
            FDSet: ui.input_fds,
            Relation: ui.input_relation,
        }

        for arg_name in params:
            annotate_class = params[arg_name].annotation
            for datatype in datatype_to_input_method:
                if match_type_or_contain(datatype, annotate_class):
                    kwargs[arg_name] = datatype_to_input_method[datatype]()
            # if match_type_or_contain(set, annotate_class):
            #     kwargs[arg_name] = UserInteraction.input_attrs()
            # if match_type_or_contain(FD, annotate_class):
            #     kwargs[arg_name] = UserInteraction.input_fd()

            # if match_type_or_contain(FDSet, annotate_class):
            #     kwargs[arg_name] = UserInteraction.input_fds()
            # if match_type_or_contain(Relation, annotate_class):
            #     kwargs[arg_name] = UserInteraction.input_relation()


        result = f(*args, **kwargs)
        print(result)
        return result

    return wrapper


class RelationModel:
    """
    Mapping all tool in class to display in menu
    Use docstring of function as purpose of method in menu
    Any parameter will get input from user via injection so leave them None as default
    """

    @inject_args
    @staticmethod
    def attribute_closure(attrs: set | None = None, fds: FDSet | None = None) -> set:
        return AttributeSets.closure(attrs, fds)

    @inject_args
    @staticmethod
    def apply_ir2(fds: FDSet | None = None) -> None:
        Armstrong.apply_ir2(fds)

    @inject_args
    @staticmethod
    def apply_ir4(fds: FDSet | None = None) -> None:
        Armstrong.apply_ir4(fds)

    @inject_args
    @staticmethod
    def apply_ir3_ir5(fds: FDSet | None = None) -> None:
        Armstrong.apply_ir3_ir5(fds)

    @inject_args
    @staticmethod
    def is_fds_equivalen(a: FDSet | None = None, b: FDSet | None = None) -> bool:
        return FDSets.equivalent(a, b)

    @inject_args
    @staticmethod
    def fds_closure(fds: FDSet | None = None) -> FDSet:
        return FDSets.closure(fds)

    @inject_args
    @staticmethod
    def find_key(attrs: set | None = None, fds: FDSet | None = None) -> set:
        return AttributeSets.primary_key(attrs, fds)

    @inject_args
    @staticmethod
    def find_key_from_relation(relation: Relation | None = None) -> set | None:
        return relation.get_primary_key()

    @inject_args
    @staticmethod
    def is_superkey(
        attrs_check: set | None = None,
        all_attrs: set | None = None,
        fds: FDSet | None = None,
    ) -> bool:
        return AttributeSets.is_superkey(attrs_check, all_attrs, fds)

    @inject_args
    @staticmethod
    def decompose_to_3nf(relation: Relation | None = None) -> Iterable[Relation]:
        return relation.to_3nf()

    @inject_args
    @staticmethod
    def decompose_to_bcnf(relation: Relation | None = None) -> Iterable[Relation]:
        return relation.to_bcnf()


def get_methods_name(cls):
    method_list = [
        func
        for func in dir(cls)
        if callable(getattr(cls, func)) and not func.startswith("__")
    ]
    return method_list


def get_func_callable(cls, func_name):
    return getattr(cls, func_name)


def main():

    # TODO: Convert pure unit test not base on language
    test_fd_compare()
    test_ir3_ir5()
    test_ir2()
    test_ir4()
    test_fd_creation()
    test_attr_closure()
    test_fds_equivalent()
    test_fds_equivalent_2()
    test_canonical()
    test_lhs_minimize()
    test_minimal_cover()
    test_find_primary_key()
    test_decompose_to_3nf()
    test_decompose_to_bcnf()


if __name__ == "__main__":
    main()
    RelationModel.find_key_from_relation()
    RelationModel.decompose_to_bcnf()
    RelationModel.is_fds_equivalen()
