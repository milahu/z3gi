from sut import SUT, ObjectSUT, ActionSignature, ScalableSUTClass, SUTType


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
            return ("OGET", self.list.pop())

    def put(self, val):
        if len(self.list) < self.size and val not in self.list:
            self.list.append(val)
            return SUT.OK
        else:
            return SUT.NOK

class RAFIFOSet():
    INTERFACE = [ActionSignature("get", 1), ActionSignature("put", 1)]

    def __init__(self, size):
        super()
        self.size = size
        self.list = list()

    def get(self, val):
        if len(self.list) == 0:
            return SUT.NOK
        else:
            if self.list[-1] == val:
                self.list.pop()
                return SUT.OK
            else:
                return SUT.NOK

    def put(self, val):
        if len(self.list) < self.size and val not in self.list:
            self.list.append(val)
            return SUT.OK
        else:
            return SUT.NOK

class MealyFIFOSet():
    INTERFACE = [ActionSignature("get", 0), ActionSignature("put", 0)]
    def __init__(self, size):
        super()
        self.size = size
        self.stored = 0

    def get(self):
        if self.stored == 0:
            return SUT.NOK
        else:
            self.stored -= 1
            return SUT.OK

    def put(self, val):
        if self.stored == self.size:
            return SUT.NOK
        else:
            self.stored += 1
            return SUT.OK

class FIFOSetClass(ScalableSUTClass):
    def __init__(self):
        super({
            SUTType.IORA: FIFOSet,
            SUTType.RA: RAFIFOSet,
            SUTType.Mealy: MealyFIFOSet,
            SUTType.DFA: MealyFIFOSet
        })

def new_fifoset_sut(size):
    return ObjectSUT(FIFOSet.INTERFACE, lambda : FIFOSet(size))
