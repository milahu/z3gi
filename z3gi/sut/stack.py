from sut import SUT, SUTType
from sut.scalable import ActionSignature, ObjectSUT, ScalableSUTClass


class Stack():
    INTERFACE = [ActionSignature("get", 1), ActionSignature("put", 1)]

    def __init__(self, size):
        super()
        self.size = size
        self.list = list()

    def get(self, val):
        if len(self.list) == 0:
            return SUT.NOK
        else:
            if val == self.list[-1]:
                self.list.pop()
                return SUT.OK
            else:
                return SUT.NOK

    def put(self, val):
        if len(self.list) < self.size:
            self.list.append(val)
            return SUT.OK
        else:
            return SUT.NOK

class StackClass(ScalableSUTClass):
    def __init__(self):
        super().__init__({
            SUTType.IORA: Stack,
            SUTType.RA: Stack,
        })

    def num_states(self, sut_type : SUTType, size:int):
        ra_states = {1: 3, 2: 5}
        if sut_type is SUTType.RA:
            return ra_states.get(size)
        elif sut_type is SUTType.IORA:
            return ra_states.get(size) - 1 if size in ra_states else None

def new_stack_sut(size):
    return ObjectSUT(Stack.INTERFACE, lambda : Stack(size))
