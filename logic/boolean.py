from typing import Union, Set

import z3

from base.variable import Variable


class Boolean(Variable):
    """Represents a boolean variable"""

    __value: z3.BoolRef

    def __init__(
        self,
        value: Union[z3.BoolRef, bool] = None,
        parents: Set[Variable] = None,
        difficulty: int = 0,
        auto_dependents: bool = True,
    ):
        super().__init__(parents, difficulty, auto_dependents)
        if value is not None:
            self.__value = z3.BoolSort().cast(value)
        else:
            self.__value = z3.Bool(f"Boolean({self.id()})")

    def value(self):
        return self.__value

    def __and__(self, other):
        value = z3.And(self.value(), other.value())
        return Boolean(value, parents={self, other}, difficulty=1)

    def __or__(self, other):
        value = z3.Or(self.value(), other.value())
        return Boolean(value, parents={self, other}, difficulty=1)

    def __invert__(self):
        value = z3.Not(self.value())
        return Boolean(value, parents={self}, difficulty=1)
