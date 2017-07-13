from sut import SUT, ObjectSUT, ActionSignature, ScalableSUTClass, SUTType


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

def new_stack_sut(size):
    return ObjectSUT(Stack.INTERFACE, lambda : Stack(size))
