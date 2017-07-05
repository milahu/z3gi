from sut import SUT, ObjectSUT, ActionSignature


class FIFOSet():
    INTERFACE = [ActionSignature("get", 0), ActionSignature("put", 1)]
    def __init__(self, size):
        super()
        self.size = size
        self.list = list()

    def get(self):
        if len(self.list) == 0:
            return SUT.NOK
        else:
            return ("OGET", self.list.pop(len(self.list)-1))

    def put(self, val):
        if len(self.list) < self.size and val not in self.list:
            self.list.append(val)
            return SUT.OK
        else:
            return SUT.NOK


def new_fifoset_sut(size):
    return ObjectSUT(FIFOSet.INTERFACE, lambda : FIFOSet(size))
