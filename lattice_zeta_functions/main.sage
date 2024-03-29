R=
r=
def decimal(dec):
   n=0
   while(dec<=10^(-n)):
      n+=1
   return n

err=decimal(exp(-2*pi*r*R).n())+30

K.<h> = NumberField()
field_to_reals2 = K.real_embeddings(err)
OK = K.ring_of_integers()
disc = K.absolute_discriminant()

f=
u=
eps=
etha=eps^2

M=matrix([[-r,sqrt(r)*(sqrt(r^(-1)-1)-I)],[-r^2,r*(sqrt(r^(-2)-1)-I)]])
alp=(M^(-1))[0][0]
bet=(M^(-1))[0][1]

def reduction(w1,w2):
    T, w = abs(w2/w1), w1
    if(field_to_reals2[0](w2)*field_to_reals2[1](w2)>0):
        T, w = abs(w1/w2), w2
    if T < 0:
        T = -T
    if T[1]<0 or (floor(T)<T[0]<ceil(T) and T[1] < min(a-floor(a),ceil(a)-a)):
        return 0
    return [w,-floor(T-2*T[1]*h)+T]

def reduction_integers(h):
    if disc%4 == 1:
        return reduction(1,(1+h)/2)
    if (disc//4)%4 == 2 or (disc//4)%4 == 3:
        return reduction(1,h)
    
tau=reduction_integers(h)[1]
bk_liste = continued_fraction_list(field_to_reals2[1](tau), type = 'hj', nterms=20)
                                   
A_LAMBDA_tau = []
A0 = K(1)
Ak = A0
Ak_moins_1 = tau
k = 0

while Ak_moins_1 != etha^(-1):
    A_LAMBDA_tau.append(Ak) 
    Ak_plus_1 = bk_liste[k]*Ak - Ak_moins_1
    Ak_moins_1 = Ak; Ak = Ak_plus_1; k += 1
N=len(A_LAMBDA_tau)-1

S2=[]; n=0; 
while abs(field_to_reals2[0](etha^n))+abs(field_to_reals2[1](etha^n))<R or abs(field_to_reals2[0](etha^n*A_LAMBDA_tau[N]))+abs(field_to_reals2[1](etha^n*A_LAMBDA_tau[N]))<R:
    for j in range(0,len(A_LAMBDA_tau)-1):
        a=1; b=0
        while abs(field_to_reals2[0](etha^n*a*(A_LAMBDA_tau[j])))+abs(field_to_reals2[1](etha^n*a*(A_LAMBDA_tau[j])))<R:
            T=a*A_LAMBDA_tau[j]*etha^n+b*A_LAMBDA_tau[j+1]*etha^n
            while abs(field_to_reals2[0](T))+abs(field_to_reals2[1](T))<R:
                S2.append(-T)
                b=b+1
                T=a*A_LAMBDA_tau[j]*etha^n+b*A_LAMBDA_tau[j+1]*etha^n
            a=a+1; b=0
    n=n+1
n=-1
while abs(field_to_reals2[0](etha^n))+abs(field_to_reals2[1](etha^n))<R or abs(field_to_reals2[0](etha^n*A_LAMBDA_tau[N]))+abs(field_to_reals2[1](etha^n*A_LAMBDA_tau[N]))<R:
    for j in range(0,len(A_LAMBDA_tau)-1):
        a=1; b=0
        while abs(field_to_reals2[0](etha^n*a*(A_LAMBDA_tau[j])))+abs(field_to_reals2[1](etha^n*a*(A_LAMBDA_tau[j])))<R:
            T=a*A_LAMBDA_tau[j]*etha^n+b*A_LAMBDA_tau[j+1]*etha^n
            while abs(field_to_reals2[0](T))+abs(field_to_reals2[1](T))<R:
                S2.append(-T)
                b=b+1
                T=a*A_LAMBDA_tau[j]*etha^n+b*A_LAMBDA_tau[j+1]*etha^n
            a=a+1; b=0
    n=n-1
n=0
while abs(field_to_reals2[0](eps*etha^n))+abs(field_to_reals2[1](eps*etha^n))<R or abs(field_to_reals2[0](eps*etha^n*A_LAMBDA_tau[N]))+abs(field_to_reals2[1](eps*etha^n*A_LAMBDA_tau[N]))<R:
    for j in range(0,len(A_LAMBDA_tau)-1):
        a=1; b=0
        while abs(field_to_reals2[0](eps*etha^n*a*(A_LAMBDA_tau[j])))+abs(field_to_reals2[1](eps*etha^n*a*(A_LAMBDA_tau[j])))<R:
            T=a*eps*A_LAMBDA_tau[j]*etha^n+b*eps*A_LAMBDA_tau[j+1]*etha^n
            while abs(field_to_reals2[0](T))+abs(field_to_reals2[1](T))<R:
                S2.append(T)
                b=b+1
                T=a*eps*A_LAMBDA_tau[j]*etha^n+b*eps*A_LAMBDA_tau[j+1]*etha^n
            a=a+1; b=0
    n=n+1
n=-1
while abs(field_to_reals2[0](etha^n*eps))+abs(field_to_reals2[1](etha^n*eps))<R or abs(field_to_reals2[0](eps*etha^n*A_LAMBDA_tau[N]))+abs(field_to_reals2[1](eps*etha^n*A_LAMBDA_tau[N]))<R:
    for j in range(0,len(A_LAMBDA_tau)-1):
        a=1; b=0
        while abs(field_to_reals2[0](eps*etha^n*a*(A_LAMBDA_tau[j])))+abs(field_to_reals2[1](eps*etha^n*a*(A_LAMBDA_tau[j])))<R:
            T=a*eps*A_LAMBDA_tau[j]*etha^n+b*eps*A_LAMBDA_tau[j+1]*etha^n
            while abs(field_to_reals2[0](T))+abs(field_to_reals2[1](T))<R:
                S2.append(T)
                b=b+1
                T=a*eps*A_LAMBDA_tau[j]*etha^n+b*eps*A_LAMBDA_tau[j+1]*etha^n
            a=a+1; b=0
    n=n-1

def reduceshint(mu):
    if norm(mu)>0:
        if field_to_reals2[1](mu)<0:
            mu=-mu
    else:
        if field_to_reals2[1](mu)>0:
            mu=eps*mu          
        else:
            mu=-eps*mu
    while 1>field_to_reals2[0](mu)/field_to_reals2[1](mu):
        mu=mu/etha
    while field_to_reals2[0](-5/2*h + 27/2)/field_to_reals2[1](-5/2*h + 27/2)<=field_to_reals2[0](mu)/field_to_reals2[1](mu):
        mu=etha*mu
    return mu

def bfu(d):
    suma=0
    for A in divisors(d*OK):
        D1=reduceshint(A.gens_reduced()[0])
        d2=d/D1
        if d2+u in f*OK:
            if field_to_reals2[0](d2)<0:
                suma-=1
            else:
                suma+=1
        d2=-d/D1
        if d2+u in f*OK:
            if field_to_reals2[0](d2)<0:
                suma-=1
            else:
                suma+=1
        d2=d/(eps*D1)
        if d2+u in f*OK:
            if field_to_reals2[0](d2)<0:
                suma-=1
            else:
                suma+=1
        d2=-d/(eps*D1)
        if d2+u in f*OK:
            if field_to_reals2[0](d2)<0:
                suma-=1
            else:
                suma+=1
    return suma

def Rfu(r):
    suma=0
    for d in S2:
        suma+=(alp*bfu(d)*bessel_K(0,(2*pi*abs(field_to_reals2[1](d))*r).n(digits=err))*exp(-2*pi*abs(field_to_reals2[0](d))*r)*exp(-2*pi*I*r*sqrt(r^(-1)-1)*(field_to_reals2[0](d)+field_to_reals2[1](d)))).n(digits = err)
        suma+=(r*bet*bfu(d)*bessel_K(0,(2*pi*abs(field_to_reals2[1](d))*r^2).n(digits=err))*exp(-2*pi*abs(field_to_reals2[0](d))*r^2)*exp(-2*pi*I*r^2*sqrt(r^(-2)-1)*(field_to_reals2[0](d)+field_to_reals2[1](d)))).n(digits = err)
    return -4*r*pi*I*sqrt(disc)*abs(field_to_reals2[0](f)*field_to_reals2[1](f))*suma

coef=-1/(h^2*f)

S3star=[]; n=0
while abs(field_to_reals2[0](coef*etha^n))+abs(field_to_reals2[1](coef*etha^n))<r*R or abs(field_to_reals2[0](coef*etha^n*A_LAMBDA_tau[N]))+abs(field_to_reals2[1](coef*etha^n*A_LAMBDA_tau[N]))<r*R:
    for j in range(0,len(A_LAMBDA_tau)-1):
        a=1; b=0
        while abs(field_to_reals2[0](coef*etha^n*a*(A_LAMBDA_tau[j])))+abs(field_to_reals2[1](coef*etha^n*a*(A_LAMBDA_tau[j])))<r*R:
            T=coef*a*A_LAMBDA_tau[j]*etha^n+coef*b*A_LAMBDA_tau[j+1]*etha^n
            while abs(field_to_reals2[0](T))+abs(field_to_reals2[1](T))<r*R:
                S3star.append(T)
                b=b+1
                T=coef*a*A_LAMBDA_tau[j]*etha^n+coef*b*A_LAMBDA_tau[j+1]*etha^n
            a=a+1; b=0
    n=n+1
n=-1
while abs(field_to_reals2[0](coef*etha^n))+abs(field_to_reals2[1](coef*etha^n))<r*R or abs(field_to_reals2[0](coef*etha^n*A_LAMBDA_tau[N]))+abs(field_to_reals2[1](coef*etha^n*A_LAMBDA_tau[N]))<r*R:
    for j in range(0,len(A_LAMBDA_tau)-1):
        a=1; b=0
        while abs(field_to_reals2[0](coef*etha^n*a*(A_LAMBDA_tau[j])))+abs(field_to_reals2[1](coef*etha^n*a*(A_LAMBDA_tau[j])))<r*R:
            T=coef*a*A_LAMBDA_tau[j]*etha^n+coef*b*A_LAMBDA_tau[j+1]*etha^n
            while abs(field_to_reals2[0](T))+abs(field_to_reals2[1](T))<r*R:
                S3star.append(T)
                b=b+1
                T=coef*a*A_LAMBDA_tau[j]*etha^n+coef*b*A_LAMBDA_tau[j+1]*etha^n
            a=a+1; b=0
    n=n-1
n=0
while abs(field_to_reals2[0](coef*eps*etha^n))+abs(field_to_reals2[1](coef*eps*etha^n))<r*R or abs(field_to_reals2[0](coef*eps*etha^n*A_LAMBDA_tau[N]))+abs(field_to_reals2[1](coef*eps*etha^n*A_LAMBDA_tau[N]))<r*R:
    for j in range(0,len(A_LAMBDA_tau)-1):
        a=1; b=0
        while abs(field_to_reals2[0](coef*eps*etha^n*a*(A_LAMBDA_tau[j])))+abs(field_to_reals2[1](coef*eps*etha^n*a*(A_LAMBDA_tau[j])))<r*R:
            T=coef*a*eps*A_LAMBDA_tau[j]*etha^n+coef*b*eps*A_LAMBDA_tau[j+1]*etha^n
            while abs(field_to_reals2[0](T))+abs(field_to_reals2[1](T))<r*R:
                S3star.append(-T)
                b=b+1
                T=coef*a*eps*A_LAMBDA_tau[j]*etha^n+coef*b*eps*A_LAMBDA_tau[j+1]*etha^n
            a=a+1; b=0
    n=n+1
n=-1
while abs(field_to_reals2[0](coef*etha^n*eps))+abs(field_to_reals2[1](coef*etha^n*eps))<r*R or abs(field_to_reals2[0](coef*eps*etha^n*A_LAMBDA_tau[N]))+abs(field_to_reals2[1](coef*eps*etha^n*A_LAMBDA_tau[N]))<r*R:
    for j in range(0,len(A_LAMBDA_tau)-1):
        a=1; b=0
        while abs(field_to_reals2[0](coef*eps*etha^n*a*(A_LAMBDA_tau[j])))+abs(field_to_reals2[1](coef*eps*etha^n*a*(A_LAMBDA_tau[j])))<r*R:
            T=coef*a*eps*A_LAMBDA_tau[j]*etha^n+coef*b*eps*A_LAMBDA_tau[j+1]*etha^n
            while abs(field_to_reals2[0](T))+abs(field_to_reals2[1](T))<r*R:
                S3star.append(-T)
                b=b+1
                T=coef*a*eps*A_LAMBDA_tau[j]*etha^n+coef*b*eps*A_LAMBDA_tau[j+1]*etha^n
            a=a+1; b=0
    n=n-1

def bstar(d):
    suma=0
    for A in divisors(f*h^2*d*OK):
        d1=reduceshint((A.gens_reduced()[0]))/(f*h)
        d2=d/d1
        if d2 in (1/h)*OK:
            if field_to_reals2[0](d2)>0:
                suma+=exp(2*pi*I*(field_to_reals2[0](u*d1)+field_to_reals2[1](u*d1))).n(digits = err)
                suma-=exp(2*pi*I*(field_to_reals2[0](-u*d1)+field_to_reals2[1](-u*d1))).n(digits = err)
                suma-=exp(2*pi*I*(field_to_reals2[0](u*eps*d1)+field_to_reals2[1](u*eps*d1))).n(digits = err)
                suma+=exp(2*pi*I*(field_to_reals2[0](-u*eps*d1)+field_to_reals2[1](-u*eps*d1))).n(digits = err)
            if field_to_reals2[0](d2)<0:
                suma-=exp(2*pi*I*(field_to_reals2[0](u*d1)+field_to_reals2[1](u*d1))).n(digits = err)
                suma+=exp(2*pi*I*(field_to_reals2[0](-u*d1)+field_to_reals2[1](-u*d1))).n(digits = err)
                suma+=exp(2*pi*I*(field_to_reals2[0](u*eps*d1)+field_to_reals2[1](u*eps*d1))).n(digits = err)
                suma-=exp(2*pi*I*(field_to_reals2[0](-u*eps*d1)+field_to_reals2[1](-u*eps*d1))).n(digits = err)
    return suma

def Rfustar(r):
    suma=0
    for d in S3star:
        suma+=(sqrt(r)*(sqrt(r^(-1)-1)-I)*alp*bstar(d)*bessel_K(0,(2*pi*abs(field_to_reals2[1](d))).n(digits=err))*exp(-2*pi*abs(field_to_reals2[0](d)))*exp(2*pi*I*sqrt(r^(-1)-1)*(field_to_reals2[0](d)+field_to_reals2[1](d)))).n(digits = err)
        suma+=(r*(sqrt(r^(-2)-1)-I)*bet*bstar(d)*bessel_K(0,(2*pi*abs(field_to_reals2[1](d))).n(digits=err))*exp(-2*pi*abs(field_to_reals2[0](d)))*exp(2*pi*I*sqrt(r^(-2)-1)*(field_to_reals2[0](d)+field_to_reals2[1](d)))).n(digits = err)
    return (-4*pi*I/sqrt(disc))*suma

def zetafu(r):
    return (Rfu(r)-Rfustar(r))/(abs(norm(f))*abs(disc))

Z=zetafu(r).n(digits=err)

with open('second_invariant.txt','w') as f:
	sys.stdout=f
	print(Z)
	print(exp((-I*sqrt(29)*Z/(4*pi)).n(digits=err)))
