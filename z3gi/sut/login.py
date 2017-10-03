from sut import SUT, SUTType, ScalableSUTClass
from sut.scalable import ActionSignature, ObjectSUT


class Login():
    INTERFACE = [ActionSignature("register", 1), ActionSignature("login", 1), ActionSignature("logout", 1)]
    def __init__(self, size):
        super()
        self.size = size
        self.logged = {}

    def register(self, val):
        if len(self.logged) == self.size or val in self.logged:
            return SUT.NOK
        else:
            new_id = val
            self.logged[new_id] = False
            return SUT.OK

    def login(self, val):
        if val not in self.logged or self.logged[val]:
            return SUT.NOK
        else:
            self.logged[val] = True
            return SUT.OK

    def logout(self, val):
        if val not in self.logged or not self.logged[val]:
            return SUT.NOK
        else:
            self.logged[val] = False
            return SUT.OK

class FSMLogin():
    INTERFACE = [ActionSignature("register", 0), ActionSignature("login", 0), ActionSignature("logout", 0)]

    def __init__(self, size):
        super()
        self.size = size
        self.registered = 0
        self.logged = 0

    def register(self):
        if self.registered == self.size:
            return SUT.NOK
        else:
            self.registered += 1
            return SUT.OK

    def login(self):
        if self.logged < self.registered:
            self.logged += 1
            return SUT.OK
        else:
            return SUT.NOK

    def logout(self):
        if self.logged == 0:
            return SUT.NOK
        else:
            self.logged -= 1
            return SUT.OK

class LoginClass(ScalableSUTClass):
    def __init__(self):
        super().__init__({
            SUTType.IORA: Login,
            SUTType.RA: Login,
            SUTType.Mealy: FSMLogin,
            SUTType.DFA: FSMLogin
        })


def new_login_sut(size, sut_type = SUTType.IORA):
    return ObjectSUT(Login.INTERFACE, lambda : Login(size))
