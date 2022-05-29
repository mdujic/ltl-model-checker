from re import sub
from base import AtomicFormula
from parser.ltlf import LTLfAnd, LTLfAtomic, LTLfNext, LTLfNot, LTLfUntil
from parser.ltlf import return_subformulae, LTLfParser
from itertools import islice

def algorithm(Gamma, i, _l, s):
    
    l = [set() for _ in range(i+ _l + 1)]
    

    if not s:
        return 'empty'
    
    psi = return_subformulae(s)
    if(psi == EOFError):
        return EOFError
    if(isinstance(psi, str)):
        return 'str'

    #trenutno imamo polje praznih skupova

    for a in range(0, len(psi)):
        if isinstance(psi[a], LTLfAtomic):
            for j in range(i + _l + 1):
                if(psi[a] in Gamma[j]):
                    l[j].add(psi[a])
                else:
                    l[j].add(LTLfNot(psi[a]))
        elif isinstance(psi[a], LTLfNot):
            for j in range(i + _l + 1):
                if(not(psi[a] in l[j])):
                    l[j].add(LTLfNot(psi[a]))
        elif isinstance(psi[a], LTLfAnd):
            for j in range(i + _l + 1):
                both = True
                t = psi[a]._members()[1]
                for c in t:
                    if(not(c in l[j])):
                        both = False
                if(both):
                    l[j].add(psi[a])
                else:
                    l[j].add(LTLfNot(psi[a]))
        elif isinstance(psi[a], LTLfNext):
            for j in range(i + _l + 1):
                t = psi[a]._members()[1]
                if((j < i + _l and t in l[j+1]) or (j == i + _l and t in l[i+1])):
                    l[j].add(psi[a])
                else:
                    l[j].add(LTLfNot(psi[a]))
        elif isinstance(psi[a], LTLfUntil):
            for j in range(i + _l + 1):
                exists = False
                t1 = next(islice(psi[a]._members()[1], 0, None))
                t2 = next(islice(psi[a]._members()[1], 1, None))
                for j_ in range(j,i + _l + 1):
                    if(t2 in l[j_]):
                        exists = True
                        for j__ in range(j, j_):
                            if(not(t1 in l[j__])):
                                exists = False
                if(exists):
                    l[j].add(psi[a])
                else:
                    exists = False
                    for j_ in range(i,j):
                        if(i <= j and t2 in l[j_]):
                            exists = True
                            for j__ in range(i,j_):
                                if(not(t1 in l[j__])):
                                    exists = False
                            for j__ in range(j, i + _l + 1):
                                if(not(t1 in l[j__])):
                                    exists = False
                    if(exists):
                        l[j].add(psi[a])
                    else:
                        l[j].add(LTLfNot(psi[a]))
      

    return (bool)(psi[-1] in l[0])

import sys
from PyQt5.QtWidgets import QMainWindow, QApplication, QWidget, QPushButton, QAction, QLineEdit, QMessageBox
from PyQt5.QtGui import QIcon
from PyQt5.QtCore import pyqtSlot

class App(QMainWindow):

    def __init__(self):
        super().__init__()
        self.title = 'PyQt5'
        self.left = 10
        self.top = 10
        self.width = 400
        self.height = 140
        self.initUI()
    
    def initUI(self):
        self.setWindowTitle(self.title)
        self.setGeometry(self.left, self.top, self.width, self.height)
    
        # Create textbox
        self.textbox = QLineEdit(self)
        self.textbox.move(20, 20)
        self.textbox.resize(280,40)
        
        # Create a button in the window
        self.button = QPushButton('Check if valid', self)
        self.button.move(20,80)
        
        # connect button to function on_click
        self.button.clicked.connect(self.on_click)
        self.show()
    
    @pyqtSlot()
    def on_click(self):
        textboxValue = self.textbox.text()
        
        i = 1
        l = 4
        parser = LTLfParser()
        Gamma = [set() for _ in range(i + l + 1)]
        Gamma[0].add(parser('p'))
        Gamma[1].add(parser('q'))
        Gamma[2].add(parser('p'))
        Gamma[2].add(parser('r'))
        Gamma[3].add(parser('r'))
        Gamma[4].add(parser('q'))
        Gamma[5].add(parser('q'))
        

        s = algorithm(Gamma, i, l, textboxValue)
        if s == 'empty':
            textboxValue = 'You have not entered formula.'
        elif(s == EOFError):
            textboxValue = 'EOFError'
        elif(s == 'str'):
            textboxValue = 'Invalid syntax.'
        else:
            textboxValue = str(s)

        QMessageBox.question(self, 'Message', "Result is: " + textboxValue, QMessageBox.Ok, QMessageBox.Ok)
        self.textbox.setText("")



if __name__ == "__main__":
    app = QApplication(sys.argv)
    ex = App()
    sys.exit(app.exec_())

