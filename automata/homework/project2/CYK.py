'''
 CYK algorithm for Context Free Language
 Author: Chenguang Zhu
 CS154, Stanford University
'''
import sys,traceback
import os
import string

maxProductionNum = 100 #max number of productions
VarNum = 4

production = [[0] * 3 for i in range(maxProductionNum+1)]
'''Prouductions in Chomsky Normal Form (CNF)
  production[i][0] is the number for the variable (0~3, 0: S 1: A, 2: B, 3: C)
  If this production is A->BC (two variables), then production[i][1] and production[i][2] will contain the numbers for these two variables
  If this production is A->a (a single terminal), then production[i][1] will contain the number for the terminal (0 or 1, 0: a, 1: b), production[i][2]=-1'''

X = [[[False]*3 for i in range(10)] for j in range(10)]
'''X[i][j][s]=true if and only if variable s (0~3, 0: S 1: A, 2: B, 3: C) is in X_ij defined in CYK
  Suppose the length of string to be processed is L, then 0<=i<=j<L '''

#check whether (a,b,c) exists in production
def existProd(a, b, c):
    global production
    for i in range(len(production)):
        if ((production[i][0]==a) and
            (production[i][1]==b) and
            (production[i][2]==c)):
            return True
    return False

'''CYK algorithm
   Calculate the array X
   w is the string to be processed'''
def calcCYK(w):
    global X
    global VarNum
    L=len(w)
    X=[[[False]*VarNum for i in range(L)] for j in range(L)]
#    X=[[[] for i in range(L)] for j in range(L)]

    for x in range(L):
        calc_cell_basic(x, w)

    for dist in range(1,L):
        calc_row(dist, L)

    tmp = [[lengthify(i) for i in j] for j in X]
    X = tmp


def calc_row(dist, l):
    global X

    for i in range(l - dist):
        head = i
        tail = i + dist
        calc_cell(head, tail)

def lengthify(xs):
    global VarNum
    result = [False] * VarNum
    i = 0

    for x in xs:
        result[i] = x
        i += 1
    return result

def calc_cell_basic(col, w):
    global X

    ww = w[col]
    poss = [False] * VarNum

    for i in range(7):
        if existProd(i,ww,-1):
            poss[i] = True

    X[col][col] = poss

def prod(xs, ys):
    result = []
    for x in range(len(xs)):
        for y in range(len(ys)):
            if xs[x] and ys[y]:
                for i in range(7):
                    if existProd(i, x, y):
                        result.append(i)
    return result

def calc_cell(head, tail):
    global X

    poss = [False] * VarNum

    for i in range(tail - head):
        xs = X[head][head + i]
        ys = X[head + i + 1][tail]
        for i in prod(xs, ys):
            poss[i] = True

    X[head][tail] = poss




def Start(filename):
    global X
    global VarNum
    global production
    result=''
    #read data case line by line from file
    try:
        br=open(filename,'r')

	#example on Page 8 of lecture 15_CFL5
        production=[[0]*3 for i in range(7)]
        production[0][0]=0; production[0][1]=1; production[0][2]=2  #S->AB
        production[1][0]=1; production[1][1]=2; production[1][2]=3  #A->BC
        production[2][0]=1; production[2][1]=0; production[2][2]=-1 #A->a
        production[3][0]=2; production[3][1]=1; production[3][2]=3  #B->AC
        production[4][0]=2; production[4][1]=1; production[4][2]=-1 #B->b
        production[5][0]=3; production[5][1]=0; production[5][2]=-1 #C->a
        production[6][0]=3; production[6][1]=1; production[6][2]=-1 #C->b

        result=''
	#Read File Line By Line
        for string in br:
            string=string.strip()
            print 'Processing '+string+'...'
            length=len(string)
            w=[0]*length
            for i in range(length):
            	w[i]=ord(string[i])-ord('a')  #convert 'a' to 0 and 'b' to 1
            #Use CYK algorithm to calculate X
            calcCYK(w)
            #Get/print the full table X
            for step in range(length-1,-1,-1):
                for i in range(length-step):
                    j=i+step
                    for k in range(VarNum):
                        if (X[i][j][k]):
                            result=result+str(k)
                    result=result+' '
                result=result+'\n'
	#Close the input stream
        br.close()
    except:
        exc_type, exc_value, exc_traceback = sys.exc_info()
        print "*** print_exception:"
        traceback.print_exception(exc_type, exc_value, exc_traceback,limit=2, file=sys.stdout)
        result=result+'error'

    return result

def main(filepath):
    return Start(filepath)

if __name__ == '__main__':
    main(sys.argv[1])
