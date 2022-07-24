from typing import Union, Set

import z3

from base.variable import Variable


class Integer(Variable):
    """Represents an integer variable"""

    __next_id = 0

    __value: z3.ArithRef

    def __init__(
        self,
        value: Union[z3.ArithRef, int] = None,
        parents: Set[Variable] = None,
    ):
        super().__init__(parents)
        if value is not None:
            self.__value = z3.IntSort().cast(value)
        else:
            self.__value = z3.Int(f"Integer({self.id()})")

    def value(self):
        return self.__value

    def __add__(self, other: "Integer"):
        return Integer(self.value() + other.value(), {self, other})

    def __sub__(self, other: "Integer"):
        return Integer(self.value() - other.value(), {self, other})
