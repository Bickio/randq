from abc import ABC
from itertools import chain

from typing import Set


class Variable(ABC):
    __next_id = 0

    __id: int
    __parents: Set["Variable"]
    __difficulty: int

    def __init__(self, parents: Set["Variable"] = None, difficulty: int = 0):
        if parents is None:
            parents = set()
        self.__parents = parents
        self.__id = Variable.__next_id
        Variable.__next_id += 1
        self.__difficulty = difficulty

    def id(self):
        return self.__id

    def difficulty(self):
        return self.__difficulty

    def total_difficulty(self):
        return self.difficulty() + sum(
            ancestor.difficulty() for ancestor in self.ancestors()
        )

    def ancestors(self) -> Set["Variable"]:
        return self.__parents | set(
            chain(*(parent.ancestors() for parent in self.__parents))
        )
