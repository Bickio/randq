from abc import ABC, abstractmethod
from typing import Any, TypeVar, Dict, Tuple, Generator

import z3

from .variable import Variable

GivensType = TypeVar("GivensType", bound=Dict[str, Variable])
AnswerType = TypeVar("AnswerType", bound=Variable)


class Question(ABC):
    __solver: z3.Solver

    def __init__(self, min_difficulty=0, max_difficulty=None):
        self.__solver = z3.Solver()
        self.__givens = self.givens()
        self.__solution = self.solve(self.__givens)
        self.__difficulty = self.__solution.total_difficulty()
        self.__solver.add(self.__difficulty >= min_difficulty)
        if max_difficulty is not None:
            self.__solver.add(self.__difficulty <= max_difficulty)
        self.__variations = all_smt(
            self.__solver, [given.value() for given in self.__givens.values()]
        )

    @staticmethod
    @abstractmethod
    def givens() -> GivensType:
        """Instantiate and return given variables"""
        raise NotImplementedError

    @staticmethod
    @abstractmethod
    def solve(givens: GivensType) -> AnswerType:
        """Solve the question as a student would"""
        raise NotImplementedError

    @staticmethod
    @abstractmethod
    def format_question(givens: Dict[str, Any]):
        """Format the question for humans"""
        raise NotImplementedError

    @staticmethod
    @abstractmethod
    def format_answer(answer: Any):
        """Format the answer for humans"""
        raise NotImplementedError

    def variations(self) -> Generator[Tuple[str, str, int], None, None]:
        for m in self.__variations:
            given_values = {
                name: m.eval(given.value(), model_completion=True)
                for name, given in self.__givens.items()
            }
            solution_value = m.eval(self.__solution.value(), model_completion=True)
            difficulty = m.eval(self.__difficulty)
            yield (
                self.format_question(given_values),
                self.format_answer(solution_value),
                difficulty,
            )


def all_smt(s, initial_terms):
    def block_term(s, m, t):
        s.add(t != m.eval(t, model_completion=True))

    def fix_term(s, m, t):
        s.add(t == m.eval(t, model_completion=True))

    def all_smt_rec(terms):
        if s.check() == z3.sat:
            m = s.model()
            yield m
            for i in range(len(terms)):
                s.push()
                block_term(s, m, terms[i])
                for j in range(i):
                    fix_term(s, m, terms[j])
                yield from all_smt_rec(terms[i:])
                s.pop()

    yield from all_smt_rec(list(initial_terms))
