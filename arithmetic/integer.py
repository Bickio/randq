from typing import Union, Set

import z3

from base.variable import Variable
from logic.boolean import Boolean


class Integer(Variable):
    """Represents an integer variable"""

    __value: z3.ArithRef

    def __init__(
        self,
        value: Union[z3.ArithRef, int] = None,
        parents: Set[Variable] = None,
        difficulty: int = 0,
        auto_dependents: bool = True,
        maximum: int = None,
        minimum: int = None,
    ):
        super().__init__(parents, difficulty, auto_dependents)
        if value is not None:
            self.__value = z3.IntSort().cast(value)
        else:
            self.__value = z3.Int(f"Integer({self.id()})")

        if maximum is not None:
            self._constraints.append(self.__value <= maximum)
        if minimum is not None:
            self._constraints.append(self.__value >= minimum)

    def value(self):
        return self.__value

    def __add__(self, other: "Integer"):
        difficulty = int_complexity(self.value()) + int_complexity(other.value())
        return Integer(
            self.value() + other.value(), {self, other}, difficulty=difficulty
        )

    def __sub__(self, other: "Integer"):
        difficulty = (
            int_complexity(self.value())
            + int_complexity(other.value())
            + 1  # One additional negation
        )
        return Integer(
            self.value() - other.value(), {self, other}, difficulty=difficulty
        )

    def __mul__(self, other: "Integer"):
        difficulty = int_complexity(self.value()) * int_complexity(other.value()) * 2
        return Integer(
            self.value() * other.value(), {self, other}, difficulty=difficulty
        )

    def __pow__(self, other: "Integer"):
        difficulty = (
            int_complexity(absolute(self.value())) * (absolute(other.value()) - 1)
        ) + z3.If(self.value() < 0, 1, 0)
        return Integer(
            z3.ToInt(self.value() ** other.value()),
            {self, other},
            difficulty=difficulty,
        )

    def __floordiv__(self, other):
        """
        NOTE: This is not really floor div!
        It is standard division, but the result must also be an integer
        """
        difficulty = int_complexity(self.value()) * int_complexity(other.value()) * 2
        self._constraints.append(self.value() % other.value() == 0)
        return Integer(
            self.value() / other.value(),
            {self, other},
            difficulty=difficulty,
        )

    def __mod__(self, other):
        difficulty = int_complexity(self.value()) * int_complexity(other.value()) * 2
        return Integer(
            self.value() % other.value(),
            {self, other},
            difficulty=difficulty,
        )

    def __gt__(self, other: "Integer") -> Boolean:
        return Boolean(
            self.value() > other.value(),
            {self, other},
            difficulty=1,
        )

    def __lt__(self, other: "Integer") -> Boolean:
        return Boolean(
            self.value() < other.value(),
            {self, other},
            difficulty=1,
        )

    def __ge__(self, other: "Integer") -> Boolean:
        return Boolean(
            self.value() >= other.value(),
            {self, other},
            difficulty=1,
        )

    def __le__(self, other: "Integer") -> Boolean:
        return Boolean(
            self.value() <= other.value(),
            {self, other},
            difficulty=1,
        )

    def eq(self, other):
        return Boolean(
            self.value() == other.value(),
            {self, other},
            difficulty=1,
        )

    def __ne__(self, other):
        return Boolean(
            self.value() != other.value(),
            {self, other},
            difficulty=1,
        )


def int_complexity(num: z3.ArithRef):
    """An arbitrary measure of how complex an integer is to manipulate"""
    return num_digits(num) + z3.If(num < 0, 1, 0)


def num_digits(num: z3.ArithRef):
    return z3.If(
        absolute(num) < 10,
        1,
        z3.If(
            absolute(num) < 100,
            2,
            z3.If(absolute(num) < 1000, 3, z3.If(absolute(num) < 10000, 4, 5)),
        ),
    )


def absolute(x):
    return z3.If(x >= 0, x, -x)
