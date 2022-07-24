from abc import ABC

from typing import Set


class Variable(ABC):
    __next_id = 0

    __id: int
    __parents: Set["Variable"]

    def __init__(self, parents: Set["Variable"] = None):
        if parents is None:
            parents = {}
        self.__parents = parents
        self.__id = Variable.__next_id

    def id(self):
        return self.__id
