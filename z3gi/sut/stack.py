from sut import SUT, ObjectSUT, ActionSignature


class Stack():
    INTERFACE = [ActionSignature("get", 0), ActionSignature("put", 1)]
    def __init__(self, size):
        super()
        self.size = size
        self.list = list()

    def get(self):
        if len(self.list) == 0:
            return SUT.NOK
        else:
            return ("OGET", self.list.pop())

    def put(self, val):
        if len(self.list) < self.size:
            self.list.append(val)
            return SUT.OK
        else:
            return SUT.NOK


def new_stack_sut(size):
    return ObjectSUT(Stack.INTERFACE, lambda : Stack(size))
