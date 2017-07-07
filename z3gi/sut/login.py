from sut import SUT, ObjectSUT, ActionSignature, SUTType



class Login():
    INTERFACE = [ActionSignature("register", 0), ActionSignature("login", 1), ActionSignature("logout", 1)]
    def __init__(self, size):
        super()
        self.size = size
        self.logged = {}

    def register(self):
        if len(self.logged) == self.size:
            return SUT.NOK
        else:
            new_id = 100 if len(self.logged) == 0 else max(self.logged.keys()) + 100
            self.logged[new_id] = False
            return ("OREG", new_id)

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

def new_login_sut(size, sut_type = SUTType.IORA):
    return ObjectSUT(Login.INTERFACE, lambda : Login(size))
