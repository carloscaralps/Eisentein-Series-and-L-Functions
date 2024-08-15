R=
r=
p=

def decimal(dec):
   n=0
   while(dec<=10^(-n)):
      n+=1
   return n

err=decimal(exp(-2*pi*r*R).n())+30

K.<h> = NumberField(p)
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

def tr(alpha):
    return field_to_reals2[0](alpha)+field_to_reals2[1](alpha)

def abstr(alpha):
    return abs(field_to_reals2[0](alpha))+abs(field_to_reals2[1](alpha))

S2=[]; n=0; 
while abstr(etha^n)<R or abstr(etha^n*A_LAMBDA_tau[n])<R:
    for j in range(0,N):
        a=1; b=0
        while abstr(etha^n*a*A_LAMBDA_tau[j])<R:
            T=a*A_LAMBDA_tau[j]*etha^n+b*A_LAMBDA_tau[j+1]*etha^n
            while abstr(T)<R:
                S2.append(-T)
                b=b+1
                T=a*A_LAMBDA_tau[j]*etha^n+b*A_LAMBDA_tau[j+1]*etha^n
            a=a+1; b=0
    n=n+1
n=-1
while abstr(etha^n)<R or abstr(etha^n*A_LAMBDA_tau[n])<R:
    for j in range(0,N):
        a=1; b=0
        while abstr(etha^n*a*A_LAMBDA_tau[j])<R:
            T=a*A_LAMBDA_tau[j]*etha^n+b*A_LAMBDA_tau[j+1]*etha^n
            while abstr(T)<R:
                S2.append(-T)
                b=b+1
                T=a*A_LAMBDA_tau[j]*etha^n+b*A_LAMBDA_tau[j+1]*etha^n
            a=a+1; b=0
    n=n-1
n=0
while abstr(eps*etha^n)<R or abstr(eps*etha^n*A_LAMBDA_tau[n])<R:
    for j in range(0,N):
        a=1; b=0
        while abstr(eps*etha^n*a*A_LAMBDA_tau[j])<R:
            T=a*eps*A_LAMBDA_tau[j]*etha^n+b*eps*A_LAMBDA_tau[j+1]*etha^n
            while abstr(T)<R:
                S2.append(T)
                b=b+1
                T=a*eps*A_LAMBDA_tau[j]*etha^n+b*eps*A_LAMBDA_tau[j+1]*etha^n
            a=a+1; b=0
    n=n+1
n=-1
while abstr(eps*etha^n)<R or abstr(eps*etha^n*A_LAMBDA_tau[n])<R:
    for j in range(0,N):
        a=1; b=0
        while abstr(eps*etha^n*a*A_LAMBDA_tau[j])<R:
            T=a*eps*A_LAMBDA_tau[j]*etha^n+b*eps*A_LAMBDA_tau[j+1]*etha^n
            while abstr(T)<R:
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
    while field_to_reals2[0](A_LAMBDA_tau[N])/field_to_reals2[1](A_LAMBDA_tau[N])<=field_to_reals2[0](mu)/field_to_reals2[1](mu):
        mu=etha*mu
    return mu

def bfu(d):
    suma=0
    for A in divisors(K.ideal(d)):
        D1=reduceshint(A.gens_reduced()[0])
        d2=d/D1
        if (d2+u)/f in OK:
            if field_to_reals2[0](d2)<0:
                suma-=1
            else:
                suma+=1
        d2=-d/D1
        if (d2+u)/f in OK:
            if field_to_reals2[0](d2)<0:
                suma-=1
            else:
                suma+=1
        d2=d/(eps*D1)
        if (d2+u)/f in OK:
            if field_to_reals2[0](d2)<0:
                suma-=1
            else:
                suma+=1
        d2=-d/(eps*D1)
        if (d2+u)/f in OK:
            if field_to_reals2[0](d2)<0:
                suma-=1
            else:
                suma+=1
    return suma

def Rfu(r):
    suma=0
    for d in S2:
        suma+=(alp*bfu(d)*bessel_K(0,(2*pi*abs(field_to_reals2[1](d))*r).n(digits=err))*exp(-2*pi*abs(field_to_reals2[0](d))*r)*exp(-2*pi*I*r*sqrt(r^(-1)-1)*tr(d))).n(digits = err)
        suma+=(r*bet*bfu(d)*bessel_K(0,(2*pi*abs(field_to_reals2[1](d))*r^2).n(digits=err))*exp(-2*pi*abs(field_to_reals2[0](d))*r^2)*exp(-2*pi*I*r^2*sqrt(r^(-2)-1)*tr(d))).n(digits = err)
    return -4*r*pi*I*sqrt(disc)*abs(field_to_reals2[0](f)*field_to_reals2[1](f))*suma

coef=-1/(h^2*f)

S3star=[]; n=0
while abstr(coef*etha^n)<r*R or abstr(coef*etha^n*A_LAMBDA_tau[N])<r*R:
    for j in range(0,N):
        a=1; b=0
        while abstr(coef*etha^n*a*A_LAMBDA_tau[j])<r*R:
            T=coef*a*A_LAMBDA_tau[j]*etha^n+coef*b*A_LAMBDA_tau[j+1]*etha^n
            while abstr(T)<r*R:
                S3star.append(T)
                b=b+1
                T=coef*a*A_LAMBDA_tau[j]*etha^n+coef*b*A_LAMBDA_tau[j+1]*etha^n
            a=a+1; b=0
    n=n+1
n=-1
while abstr(coef*etha^n)<r*R or abstr(coef*etha^n*A_LAMBDA_tau[N])<r*R:
    for j in range(0,N):
        a=1; b=0
        while abstr(coef*etha^n*a*A_LAMBDA_tau[j])<r*R:
            T=coef*a*A_LAMBDA_tau[j]*etha^n+coef*b*A_LAMBDA_tau[j+1]*etha^n
            while abstr(T)<r*R:
                S3star.append(T)
                b=b+1
                T=coef*a*A_LAMBDA_tau[j]*etha^n+coef*b*A_LAMBDA_tau[j+1]*etha^n
            a=a+1; b=0
    n=n-1
n=0
while abstr(coef*eps*etha^n)<r*R or abstr(coef*eps*etha^n*A_LAMBDA_tau[N])<r*R:
    for j in range(0,N):
        a=1; b=0
        while abstr(coef*eps*etha^n*a*A_LAMBDA_tau[j])<r*R:
            T=coef*a*eps*A_LAMBDA_tau[j]*etha^n+coef*b*eps*A_LAMBDA_tau[j+1]*etha^n
            while abstr(T)<r*R:
                S3star.append(-T)
                b=b+1
                T=coef*a*eps*A_LAMBDA_tau[j]*etha^n+coef*b*eps*A_LAMBDA_tau[j+1]*etha^n
            a=a+1; b=0
    n=n+1
n=-1
while abstr(coef*eps*etha^n)<r*R or abstr(coef*eps*etha^n*A_LAMBDA_tau[N])<r*R:
    for j in range(0,N):
        a=1; b=0
        while abstr(coef*eps*etha^n*a*A_LAMBDA_tau[j])<r*R:
            T=coef*a*eps*A_LAMBDA_tau[j]*etha^n+coef*b*eps*A_LAMBDA_tau[j+1]*etha^n
            while abstr(T)<r*R:
                S3star.append(-T)
                b=b+1
                T=coef*a*eps*A_LAMBDA_tau[j]*etha^n+coef*b*eps*A_LAMBDA_tau[j+1]*etha^n
            a=a+1; b=0
    n=n-1

def bstar(d):
    suma=0
    for A in divisors(K.ideal(f*h^2*d)):
        d1=reduceshint((A.gens_reduced()[0]))/(f*h)
        d2=d/d1
        if d2*h in OK:
            if field_to_reals2[0](d2)>0:
                suma+=(2*I*sin(2*pi*tr(u*d1))).n(digits = err)
                suma-=(2*I*sin(2*pi*tr(u*eps*d1))).n(digits = err)
            if field_to_reals2[0](d2)<0:
                suma-=(2*I*sin(2*pi*tr(u*d1))).n(digits = err)
                suma+=(2*I*sin(2*pi*tr(u*eps*d1))).n(digits = err)
    return suma

def Rfustar(r):
    suma=0
    for d in S3star:
        suma+=(sqrt(r)*(sqrt(r^(-1)-1)-I)*alp*bstar(d)*bessel_K(0,(2*pi*abs(field_to_reals2[1](d))).n(digits=err))*exp(-2*pi*abs(field_to_reals2[0](d)))*exp(2*pi*I*sqrt(r^(-1)-1)*tr(d))).n(digits = err)
        suma+=(r*(sqrt(r^(-2)-1)-I)*bet*bstar(d)*bessel_K(0,(2*pi*abs(field_to_reals2[1](d))).n(digits=err))*exp(-2*pi*abs(field_to_reals2[0](d)))*exp(2*pi*I*sqrt(r^(-2)-1)*tr(d))).n(digits = err)
    return (-4*pi*I/sqrt(disc))*suma

def zetafu(r):
    return (Rfu(r)-Rfustar(r))/(abs(norm(f))*abs(disc))

Z=zetafu(r).n(digits=err)

with open('main.txt','w') as f:
	sys.stdout=f
	print(Z)
	print(exp((-I*sqrt(29)*Z/(4*pi)).n(digits=err)))
