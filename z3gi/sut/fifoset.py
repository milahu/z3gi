from sut import SUT, SUTType
from sut.scalable import ActionSignature, ScalableSUTClass


class FIFOSet():
    INTERFACE = [ActionSignature("get", 1), ActionSignature("put", 1)]

    def __init__(self, size):
        super()
        self.size = size
        self.list = list()

    def get(self, val):
        if len(self.list) == 0 or self.list[0] != val:
            return SUT.NOK
        else:
            self.list.pop(0)
            return SUT.OK

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

    def put(self):
        if self.stored == self.size:
            return SUT.NOK
        else:
            self.stored += 1
            return SUT.OK

class FIFOSetClass(ScalableSUTClass):
    def __init__(self):
        super().__init__({
            SUTType.IORA: FIFOSet,
            SUTType.RA: FIFOSet,
            SUTType.Mealy: MealyFIFOSet,
            SUTType.DFA: MealyFIFOSet
        })

    def num_states(self, sut_type : SUTType, size:int):
        ra_num = {1:3, 2:6}
        if not sut_type.has_registers():
            mealy_size = size + 1
            if sut_type is SUTType.DFA:
                return  mealy_size +1
            elif sut_type is SUTType.Mealy:
                return mealy_size
        if sut_type is SUTType.RA:
            return ra_num.get(size)
        elif sut_type is SUTType.IORA:
            return ra_num.get(size) - 1 if size in ra_num else None