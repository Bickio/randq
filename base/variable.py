from abc import ABC

from typing import Set, List, Union, Tuple

import z3


class Variable(ABC):
    __next_id = 0

    __id: int
    __parents: Set["Variable"]
    __difficulty: Union[int, z3.ArithRef]
    _constraints: List[z3.ExprRef]
    __base_used: bool = False
    __dependents: List[Tuple["Variable", Union[bool, z3.BoolRef]]]

    def __init__(
        self,
        parents: Set["Variable"] = None,
        difficulty: Union[int, z3.ArithRef] = 0,
        auto_dependents: bool = True,
    ):
        if parents is None:
            parents = set()
        self.__parents = parents
        self.__id = Variable.__next_id
        Variable.__next_id += 1
        self.__difficulty = z3.IntSort().cast(difficulty)
        self._constraints = []
        self.__dependents = []
        if auto_dependents:
            for parent in self.__parents:
                parent.add_dependent(self)

    def id(self):
        return self.__id

    def __repr__(self):
        return f"Variable({self.id()})"

    def difficulty(self) -> z3.ArithRef:
        return z3.If(self.used(), self.__difficulty, 0)

    def total_difficulty(self):
        return self.difficulty() + z3.Sum(
            *(ancestor.difficulty() for ancestor in self.ancestors())
        )

    def ancestors(self) -> Set["Variable"]:
        """
        All variables directly or indirectly contributing to self
        Does not include self
        """
        ancestors = set()
        stack = [parent for parent in self.parents()]
        while stack:
            v = stack.pop()
            if v not in ancestors:
                ancestors.add(v)
                for parent in v.parents():
                    stack.append(parent)
        return ancestors

    def parents(self) -> Set["Variable"]:
        return self.__parents

    def constraints(self) -> List[z3.ExprRef]:
        return self._constraints

    def used(self) -> z3.BoolRef:
        return z3.Or(
            self.__base_used,
            *(
                z3.And(other.used(), condition)
                for other, condition in self.__dependents
            ),
        )

    def override_used(self):
        self.__base_used = True

    def add_dependent(self, other, condition: Union[bool, z3.BoolRef] = True):
        self.__dependents.append((other, condition))
