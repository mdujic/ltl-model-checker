from re import sub
from base import AtomicFormula
from parser.ltlf import LTLfAlways, LTLfAnd, LTLfAtomic, LTLfEquivalence, LTLfEventually, LTLfFalse, LTLfImplies, LTLfLast, LTLfNext, LTLfNot, LTLfOr, LTLfRelease, LTLfTrue, LTLfUntil, LTLfWeakNext
from parser.ltlf import return_subformulae, LTLfParser
from itertools import islice

def algorithm(Gamma, i, _l, s):
    

    if not s:
        return 'empty'
    
    psi = return_subformulae(s)
    if(psi == EOFError):
        return EOFError
    if(isinstance(psi, str)):
        return 'str'

    #trenutno imamo polje praznih skupova
    l = [set() for _ in range(i+ _l + 1)]
    
    for a in range(0, len(psi)):
        if isinstance(psi[a], LTLfAtomic):
            for j in range(i + _l + 1):
                if(psi[a] in Gamma[j]):
                    l[j].add(psi[a])
                else:
                    l[j].add(LTLfNot(psi[a]))
        
        #veznici
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
                    
        elif isinstance(psi[a], LTLfOr):
            for j in range(i + _l + 1):
                both = True
                t = psi[a]._members()[1]
                for c in t:
                    if(c in l[j]):
                        both = False
                if(not both):
                    l[j].add(psi[a])
                else:
                    l[j].add(LTLfNot(psi[a]))
                    
        elif isinstance(psi[a], LTLfImplies):
            for j in range(i + _l + 1):
                t1 = next(islice(psi[a]._members()[1], 0, None))
                t2 = next(islice(psi[a]._members()[1], 1, None))
                if (not (t2 in l[j]) and (t1 in l[j])):
                    l[j].add(LTLfNot(psi[a]))
                else:
                    l[j].add(psi[a])
                    
        elif isinstance(psi[a], LTLfEquivalence):
            for j in range(i + _l + 1):
                t1 = next(islice(psi[a]._members()[1], 0, None))
                t2 = next(islice(psi[a]._members()[1], 1, None))
                if ((t1 in l[j] and t2 in l[j]) or (not (t1 in l[j]) and not (t2 in l[j]))):
                    l[j].add(psi[a])
                else:
                    l[j].add(LTLfNot(psi[a]))
                    
        #operatori
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
                        break #zanima nas samo kad se t2 prvi put ispuni
                if(exists):
                    l[j].add(psi[a])
                else:
                    #exists = False
                    for j_ in range(i,j):
                        if(i <= j and t2 in l[j_]):
                            exists = True
                            for j__ in range(i,j_):
                                if(not(t1 in l[j__])):
                                    exists = False
                            for j__ in range(j, i + _l + 1):
                                if(not(t1 in l[j__])):
                                    exists = False
                            break #zanima nas samo kad se t2 prvi put ispuni
                    if(exists):
                        l[j].add(psi[a])
                    else:
                        l[j].add(LTLfNot(psi[a]))
        
        elif isinstance(psi[a], LTLfAlways):
            t = psi[a]._members()[1]
            always = True
            for j in range(i, i + _l + 1): #prvo provjeravamo period
                if (not(t in l[j])):
                    always = False
                    break
            if (not always):
                for j in range(i + _l + 1):
                    l[j].add(LTLfNot(psi[a])) #ako na periodu postoji stanje na kojem psi nije istinita, onda G psi nikad nije istinita
            else:
                for j in range(i, i + _l + 1): #na periodu je psi istinita
                    l[j].add(psi[a])
                for j in range(i - 1, -1, -1): #provjeravamo je li psi na pretperiodu istinita; unazad jer znamo da je na periodu istinita
                    if (not(t in l[j])): #cim psi nije istinita za prvi j (iduci unazad), G psi nije istinita ni za jedan j'<=j
                        always = False
                        break
                    else:
                        l[j].add(psi[a])
                if(not always):
                    for j_ in range(j + 1):
                        l[j_].add(LTLfNot(psi[a]))

        elif isinstance(psi[a], LTLfEventually):
            t = psi[a]._members()[1]
            period = False
            for j in range(i, i+ _l + 1): #prvo provjeravamo period
                if (t in l[j]):
                    period = True
                    break
            if (period):
                for j in range(i + _l + 1):
                    l[j].add(psi[a]) #ako je na periodu istinita, onda ce svakako biti istinita u svakom stanju
            else:
                for j in range(i, i + _l + 1): #na periodu je lazna
                    l[j].add(LTLfNot(psi[a]))
                for j in range(i): #jos provjeravamo je li na pretperiodu istinita
                    event = False
                    for j_ in range(j, i):
                        if (t in l[j_]):
                            event = True
                            break
                    if(event):
                        l[j].add(psi[a])
                    else:
                        l[j].add(LTLfNot(psi[a]))
                        
        elif isinstance(psi[a], LTLfRelease):
            t1 = next(islice(psi[a]._members()[1], 0, None))
            t2 = next(islice(psi[a]._members()[1], 1, None))
            t1_never = True
            t2_always = True
            period = True
            
            for j in range(i + _l + 1):
                if (t1 in l[j]):
                    t1_never = False
                    break
                if (not(t2 in l[j])):
                    if j in range(i, i + _l + 1):
                        period = False
                    t2_always = False
            if (t1_never):
                if (t2_always): #t1 nikad nije istinita i t2 je uvijek istinita - t1 R t2 je istinita
                    for j_ in range(i + _l + 1):
                        l[j_].add(psi[a])
                else:
                    if (not period): #t1 nikad nije istinita i na nekom mjestu perioda t2 nije istinita - t1 R t2 nije istinita
                        for j_ in range(i + _l + 1):
                            l[j_].add(LTLfNot(psi[a]))
                    else:
                        for j_ in range (i-1, -1, -1): #vracamo se unazad od perioda sve do trenutka kad t2 postane neistinita
                            if (t2 in l[j_]):
                                l[j_].add(psi[a])
                            else:
                                break
                        for j__ in range (j_+1): #svugdje prije i ukljucujuci mjesto gdje je t2 neistinita - t1 R t2 nije istinita
                            l[j__].add(LTLfNot(psi[a]))
            else: #na j. mjestu t1 prvi put postane istinita
                t2_always = True                
                for j_ in range(j, -1, -1): #vracamo se unazad
                    if (t2 in l[j_] and t2_always):
                        l[j_].add(psi[a])
                    else:
                        t2_always = False
                        break
                if (not t2_always):
                    for j__ in range(j_ + 1):
                        l[j__].add(LTLfNot(psi[a]))  

    return (bool)(psi[-1] in l[0])

import sys
from PyQt5.QtWidgets import * 
from PyQt5 import QtCore, QtGui
from PyQt5.QtGui import *
from PyQt5.QtCore import *

with open('unos_modela.txt') as f:
    lines = f.readlines()


k = int(lines[0])
n = int(lines[1])

assert "Ukupna duljina pretperioda i perioda ne poklapa se s brojem linija" and k+n+1 == len(lines) - 2
assert "(k+2). i zadnja linija se ne poklapaju - ne vrijedi periodičnost" and lines[2 + k] == lines[-1]
parser = LTLfParser()
Gamma = [set() for _ in range(k + n + 1)]
for p in range(2, k+n+1 + 2):
    lines[p] = ' '.join( lines[p] ).split()
    for var in lines[p]:       
        Gamma[p-2].add( parser(var) )

class App(QMainWindow):

    def __init__(self):
        super().__init__()
        self.title = 'Provjera modela'
        self.left = 20
        self.top = 20
        self.width = 400
        self.height = 500
        self.initUI()
    
    def initUI(self):
        self.setWindowTitle(self.title)
        self.setGeometry(self.left, self.top, self.width, self.height)
    
        self.l1 = QLabel(self)
        self.l1.setText("Upiši formulu LTLa:")
        self.l1.move(20,20)
        self.l1.resize(280,40)

        # Create textbox
        self.textbox1 = QLineEdit(self)
        self.textbox1.move(20, 60)
        self.textbox1.resize(280,40)

        self.l2 = QLabel(self)
        self.l2.setText("Model (pretperiod i period):")
        self.l2.move(20,120)
        self.l2.resize(280,40)
        
        self.w = [None] * (k+n+1)
        bottom = 160
        for i in range(k):
            self.w[i] = QLabel(self)
            self.w[i].setText( 'Gamma['+ str(i) + '] = { '+ ''.join( [ str(t)+' ' for t in Gamma[i] ] ) + '}' )
            self.w[i].move(20, bottom)
            bottom += 40
            self.w[i].resize(280,40)
        
        bottom -= 10
        self.p = QLabel(self)
        self.p.setText('_______________________________________')                
        self.p.move(20,bottom)
        self.p.resize(280,40)
        bottom += 40        

        for i in range(k, k+n+1):
            self.w[i] = QLabel(self)
            self.w[i].setText( 'Gamma['+ str(i) + '] = { '+ ''.join( [ str(t)+' ' for t in Gamma[i] ] ) + '}' )
            self.w[i].move(20, bottom)
            bottom += 40
            self.w[i].resize(280,40)
  
 
        # Create a button in the window
        self.button = QPushButton('Provjeri istinitost!', self)
        self.button.move(20,bottom)
        self.button.resize(150,40)

        # connect button to function on_click
        self.button.clicked.connect(self.on_click)
        self.show()
    
    @pyqtSlot()
    def on_click(self):
        textboxValue = self.textbox1.text()

        s = algorithm(Gamma, k, n, textboxValue)
        if s == 'empty':
            textboxValue = 'You have not entered formula.'
        elif(s == EOFError):
            textboxValue = 'EOFError'
        elif(s == 'str'):
            textboxValue = 'Invalid syntax.'
        else:
            textboxValue = str(s)

        QMessageBox.question(self, 'Message', "Result is: " + textboxValue, QMessageBox.Ok, QMessageBox.Ok)
        self.textbox1.setText("")



if __name__ == "__main__":
    app = QApplication(sys.argv)
    ex = App()
    sys.exit(app.exec_())

