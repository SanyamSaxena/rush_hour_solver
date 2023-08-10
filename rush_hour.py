from z3 import *
import sys
N=int(0)
T=int(0)
s=Solver()
file1 = open(sys.argv[1],"r")
i=0
numhorz=0
numvert=0
nummines=0
def satadder(time, s, S, X, N, numhorz, numvert):
    onlyhorcarmove = []
    onlyvercarmove = []
    onlyredcarmove = []
    for i in range(N):
        for j in range(N):
            onlyhorcarmove.insert(0,(Xor(S[i][j][time][1], S[i][j][time+1][1]),1))
            if j==0 or j==1:
                s.add(Implies(Xor(S[i][j][time][1], S[i][j][time+1][1]),And(Xor(S[i][j][time][1],S[i][j+2][time][1]),Xor(S[i][j][time+1][1],S[i][j+2][time+1][1]),S[i][j+1][time][1],S[i][j+1][time+1][1],M[time]==i*N+j+1)))
            elif j==N-1 or j==N-2:
                s.add(Implies(Xor(S[i][j][time][1], S[i][j][time+1][1]),And(Xor(S[i][j][time][1],S[i][j-2][time][1]),Xor(S[i][j][time+1][1],S[i][j-2][time+1][1]),S[i][j-1][time][1],S[i][j-1][time+1][1],M[time]==i*N+j-1)))
            else:
                s.add(Implies(Xor(S[i][j][time][1], S[i][j][time+1][1]), Xor(And(Xor(S[i][j][time][1],S[i][j+2][time][1]),Xor(S[i][j][time+1][1],S[i][j+2][time+1][1]),S[i][j+1][time][1],S[i][j+1][time+1][1],M[time]==i*N+j+1),And(Xor(S[i][j][time][1],S[i][j-2][time][1]),Xor(S[i][j][time+1][1],S[i][j-2][time+1][1]),S[i][j-1][time][1],S[i][j-1][time+1][1],M[time]==i*N+j-1))))
            # # #collisions
            s.add(Implies(And(Not(S[i][j][time][1]), S[i][j][time+1][1]),Not(S[i][j][time][2])))
            s.add(Implies(And(Not(S[i][j][time][1]), S[i][j][time+1][1]),Not(S[i][j][time][1])))
            s.add(Implies(And(Not(S[i][j][time][1]), S[i][j][time+1][1]),Not(S[i][j][time][0])))
            s.add(Implies(And(Not(S[i][j][time][1]), S[i][j][time+1][1]),Not(X[i][j])))
    for i in range(N):
        for j in range(N):
            onlyredcarmove.insert(0,(Xor(S[i][j][time][0], S[i][j][time+1][0]),1))
            if j==0 or j==1:
                s.add(Implies(Xor(S[i][j][time][0], S[i][j][time+1][0]),And(Xor(S[i][j][time][0],S[i][j+2][time][0]),Xor(S[i][j][time+1][0],S[i][j+2][time+1][0]),S[i][j+1][time][0],S[i][j+1][time+1][0],M[time]==i*N+j+1)))
            elif j==N-1 or j==N-2:
                s.add(Implies(Xor(S[i][j][time][0], S[i][j][time+1][0]),And(Xor(S[i][j][time][0],S[i][j-2][time][0]),Xor(S[i][j][time+1][0],S[i][j-2][time+1][0]),S[i][j-1][time][0],S[i][j-1][time+1][0],M[time]==i*N+j-1)))
            else:
                s.add(Implies(Xor(S[i][j][time][0], S[i][j][time+1][0]), Xor(And(Xor(S[i][j][time][0],S[i][j+2][time][0]),Xor(S[i][j][time+1][0],S[i][j+2][time+1][0]),S[i][j+1][time][0],S[i][j+1][time+1][0],M[time]==i*N+j+1),And(Xor(S[i][j][time][0],S[i][j-2][time][0]),Xor(S[i][j][time+1][0],S[i][j-2][time+1][0]),S[i][j-1][time][0],S[i][j-1][time+1][0],M[time]==i*N+j-1))))
            s.add(Implies(And(Not(S[i][j][time][0]), S[i][j][time+1][0]),Not(S[i][j][time][2])))
            s.add(Implies(And(Not(S[i][j][time][0]), S[i][j][time+1][0]),Not(S[i][j][time][1])))
            s.add(Implies(And(Not(S[i][j][time][0]), S[i][j][time+1][0]),Not(S[i][j][time][0])))
            s.add(Implies(And(Not(S[i][j][time][0]), S[i][j][time+1][0]),Not(X[i][j])))
    for i in range(N):
        for j in range(N):
            onlyvercarmove.insert(0,(Xor(S[i][j][time][2], S[i][j][time+1][2]),1))
            if i==0 or i==1:
                s.add(Implies(Xor(S[i][j][time][2], S[i][j][time+1][2]),And(Xor(S[i][j][time][2],S[i+2][j][time][2]),Xor(S[i][j][time+1][2],S[i+2][j][time+1][2]),S[i+1][j][time][2],S[i+1][j][time+1][2],M[time]==(i+1)*N+j)))
            elif i==N-1 or i==N-2:
                s.add(Implies(Xor(S[i][j][time][2], S[i][j][time+1][2]),And(Xor(S[i][j][time][2],S[i-2][j][time][2]),Xor(S[i][j][time+1][2],S[i-2][j][time+1][2]),S[i-1][j][time][2],S[i-1][j][time+1][2],M[time]==(i-1)*N+j)))
            else:
                s.add(Implies(Xor(S[i][j][time][2], S[i][j][time+1][2]), Xor(And(Xor(S[i][j][time][2],S[i+2][j][time][2]),Xor(S[i][j][time+1][2],S[i+2][j][time+1][2]),S[i+1][j][time][2],S[i+1][j][time+1][2],M[time]==(i+1)*N+j),And(Xor(S[i][j][time][2],S[i-2][j][time][2]),Xor(S[i][j][time+1][2],S[i-2][j][time+1][2]),S[i-1][j][time][2],S[i-1][j][time+1][2],M[time]==(i-1)*N+j))))
            s.add(Implies(And(Not(S[i][j][time][2]), S[i][j][time+1][2]),Not(S[i][j][time][2])))
            s.add(Implies(And(Not(S[i][j][time][2]), S[i][j][time+1][2]),Not(S[i][j][time][1])))
            s.add(Implies(And(Not(S[i][j][time][2]), S[i][j][time+1][2]),Not(S[i][j][time][0])))
            s.add(Implies(And(Not(S[i][j][time][2]), S[i][j][time+1][2]),Not(X[i][j])))
    s.add(PbEq(tuple(onlyredcarmove+onlyvercarmove+onlyhorcarmove),2))
for line in file1:
    if(i==0):
        x=line.split(",")
        N=int(x[0])
        T=int(x[1])
        global S,X
        S = [[[[Bool("m_%s_%s_%s_%s" % (i,j,t,v)) for v in range(3) ] for t in range(T+1) ] for j in range(N) ] for i in range(N) ]
        X = [[Bool("x_%s_%s" % (i,j)) for j in range(N) ] for i in range(N) ] # 0 red 1 H 2 V
        M = [Int("move_%s" %t) for t in range(T)]
    elif(i==1):
        x=line.split(",")
        a=int(x[0])
        b=int(x[1])
        s.add(S[a][b][0][0]==True)
        s.add(S[a][b+1][0][0]==True)
    else:
        x=line.split(",")
        q=int(x[0])
        a=int(x[1])
        b=int(x[2])
        if(q==0):
            numvert=numvert+1
            s.add(S[a][b][0][2]==True)
            s.add(S[a+1][b][0][2]==True)
        elif(q==1):
            numhorz=numhorz+1
            s.add(S[a][b][0][1]==True)
            s.add(S[a][b+1][0][1]==True)
        else:
            nummines+=1
            s.add(X[a][b]==True)
    i=i+1   

file1.close()
horzcars=Sum([Sum([If(S[i][j][0][1],1,0) for i in range(N)]) for j in range(N)])
vertcars=Sum([Sum([If(S[i][j][0][2],1,0) for i in range(N)]) for j in range(N)])
redcar=Sum([Sum([If(S[i][j][0][0],1,0) for i in range(N)]) for j in range(N)])
mines=Sum([Sum([If(X[i][j],1,0) for i in range(N)]) for j in range(N)])
s.add(horzcars==2*numhorz)
s.add(vertcars==2*numvert)
s.add(redcar==2)
s.add(mines==nummines)
move=0
while(move<T):
    satadder(move, s, S, X, N, numhorz, numvert)
    finalcon = []
    for k in range(N):
        finalcon.insert(0, (S[k][N-1][move+1][0],1))
    s2=Solver()
    s2.add(s.assertions())
    s2.add(PbGe(finalcon,1))
    global res
    res=s2.check()
    if(res==sat):
        V=[0]*T
        m=s2.model()
        for d in m:
            p=str(d).split("_")
            if(p[0]=="move"):
                V[int(p[1])]=int(str(m[d]))
        for i in range(move):
            print("%s,%s"%(int(V[i]/N),V[i]%N),end="\n")
        print("%d,%d"%(int(V[move]/N),V[move]%N),end="")
        break
    move = move + 1

if(res==unsat):
    print("unsat")



