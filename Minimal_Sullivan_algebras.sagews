︠b06ede28-b62d-4650-ae6a-a53542c1c538︠
#-------------------------------------------------------------------------------------------------------------------------------------
#AUXILIARY FUNCTIONS:
#-------------------------------------------------------------------------------------------------------------------------------------

#-------------------------------------------------------------------------------------------------------------------------------------
#FUNCTION tuple:
#-------------------------------------------------------------------------------------------------------------------------------------
#Input:  A = a Sullivan algebra
#        p = product of generators of A
#Output: t = tuple such that the exponent of i-th generator in p appears at the position i
#-------------------------------------------------------------------------------------------------------------------------------------
def tuple(A,p):
    G = A.gens()
    d = p.degree()
    B1 = A.basis(d)
    B2 = A._basis_for_free_alg(d)
    i = B1.index(p)
    t = B2[i]
    return t
︡53f4b0d7-86d3-41f7-ac7b-c4104406fee3︡{"done":true}
︠9d576c21-6a43-4d2a-998b-0b364a0d7f30s︠
#Example:
A.<a1,b1,c1,v2,u3> = GradedCommutativeAlgebra(QQ, degrees=(1,1,1,2,3))
dA = A.cdg_algebra({a1:v2, u3:v2^2})
p = a1*v2^2
tuple(A,p)
︡10fb3060-ddff-472c-abe4-bbb0f78247b8︡{"stdout":"(1, 0, 0, 2, 0)\n"}︡{"done":true}
︠3a52cc62-f405-48ba-8c0e-335a68d5813fs︠
#-------------------------------------------------------------------------------------------------------------------------------------
#FUNCTION coef:
#-------------------------------------------------------------------------------------------------------------------------------------
#Input:  s = a linear combination of generators of A
#        m = a generator of A
#Output: c = coefficient of m in s
#-------------------------------------------------------------------------------------------------------------------------------------
def coef(s,m):
    L = s.monomials()
    if m in L:
        d = s.degree()
        B = A.basis(d)
        j = B.index(m)
        coef = s.basis_coefficients()
        c = coef[j]
    else:
        c = 0
    return c
︡30a08451-e00c-4af5-8371-9888d69bd9a4︡{"done":true}
︠dcd79f64-72d2-4708-a28c-6efd0434df02s︠
#Examples:
s = 2*v2*c1 - a1*b1*c1 + 3*u3
coef(s,u3)
coef(s,a1)
︡ffb31ab7-4845-46a2-b92f-4e4b5444caa1︡{"stdout":"3\n"}︡{"stdout":"0\n"}︡{"done":true}
︠1f5ad665-35e5-4ad3-a308-ac572e643651︠
#-------------------------------------------------------------------------------------------------------------------------------------
#FUNCTION Lambda2:
#-------------------------------------------------------------------------------------------------------------------------------------
#Input: A = a Sullivan algebra
#       s = a linear combination of elements of A
#Output: It is 1 if s is generated by elements of A obtained as the product of two or more generators of A.
#        It is 0 in the other case.
#-------------------------------------------------------------------------------------------------------------------------------------
def Lambda2(A,s):
    if s == 0:
        n = 1
    else:
        n = 1
        M = s.monomials()
        for m in M:
            t = tuple(A,m)
            pos_non_zero = [i for i,x in enumerate(t) if x!=0]
            if len(pos_non_zero)==1 and t[pos_non_zero[0]]==1:
                n = 0
    return n
︡a0289e1a-bdba-430a-82d4-92b39f5c9672︡{"done":true}
︠1d86d668-f369-4160-8750-03b18811fa44s︠
#Examples:
s1 = 2*v2*c1 - a1*b1*c1
s2 = 2*v2*c1 - u3
s3 = a1 + b1
s4 = v2^3-2*v2*u3
Lambda2(A,s1)
Lambda2(A,s2)
Lambda2(A,s3)
Lambda2(A,s4)
︡5b4ce6d4-4255-4c3b-866e-35e6723f310a︡{"stdout":"1\n"}︡{"stdout":"0\n"}︡{"stdout":"0\n"}︡{"stdout":"1\n"}︡{"done":true}
︠bdf6e1d5-5f6b-43fd-b30f-b61b2bfd257c︠
#-------------------------------------------------------------------------------------------------------------------------------------
#FUNCTION phi_homotopy_p:
#-------------------------------------------------------------------------------------------------------------------------------------
#Input: A = a Sullivan algebra
#       p = product of generators of A
#       f,g,phi = imagens of the morphisms f,g and phi of the generators of A
#Output: If p = p1*p2 -> phi_homotopy_p(A,p,f,g,phi) = p1*phi(p2) + phi(p1)*gf(p2)
#-------------------------------------------------------------------------------------------------------------------------------------
def phi_homotopy_p(A,p,f,g,phi):
    G = A.gens()
    t = tuple(A,p)
    pos_non_zero = [i for i,x in enumerate(t) if x!=0]
    p1 = G[pos_non_zero[0]]
    p2 = G[pos_non_zero[0]]^(t[pos_non_zero[0]]-1)
    for j in range(len(pos_non_zero)-1):
        p2 = p2*G[pos_non_zero[j+1]]^(t[pos_non_zero[j+1]])
    if t[pos_non_zero[0]]==1 and p2 == 1:
        c = phi[pos_non_zero[0]]
    else:
        c = p1*phi_homotopy_p(A,p2,f,g,phi)+phi[pos_non_zero[0]]*g(f(p2))
    return c
︡6a6be492-a95b-4f48-8aa2-ce5818a8d790︡{"done":true}
︠f9e9b9a1-02d4-495d-81ed-60ef48128e97s︠
#Example:
p = a1*b1
M = Hom(A,A)
f = M([a1,b1,c1,0,0]) #f(a1)=a1,f(b1)=b1,f(c1)=c1,f(v2)=0,f(u3)=0
g = M([a1,b1,c1,0,0]) #g(a1)=a1,g(b1)=b1,g(c1)=c1,g(v2)=0,g(u3)=0
phi=[c1,0,0,u3,0]     #phi(a1)=c1,phi(b1)=0,phi(c1)=0,phi(v2)=u3,phi(u3)=0
phi_homotopy_p(A,p,f,g,phi) #phi(a1*b1)=a1*phi(b1) + phi(a1)*gf(b1)=a1*0+c1*b1=-b1*c1
︡41c8132a-71da-4198-98aa-4e2e57827c18︡{"stdout":"-b1*c1\n"}︡{"done":true}
︠b0863f6b-b61b-4a6d-b7b4-f67b1776bbc9s︠
#-------------------------------------------------------------------------------------------------------------------------------------
#FUNCTION phi_homotopy:
#-------------------------------------------------------------------------------------------------------------------------------------
#Input: A = a Sullivan algebra
#       s = a linear combination of elements of A
#       f,g,phi = imagens of the morphisms f,g and phi of the generators of A
#Output: If s = a1*p1+...+an*pn, ai numbers and pi products of generators of A ->
#        phi_homotopy(A,s,f,g,phi) = a1*phi_homotopy_p(A,p1,f,g,phi) + ... + an*phi_homotopy_p(A,pn,f,g,phi)
#-------------------------------------------------------------------------------------------------------------------------------------
def phi_homotopy(A,s,f,g,phi):
    if s == 0:
        return 0
    else:
        result = 0
        M = s.monomials()
        for m in M:
            result = result + coef(s,m)*phi_homotopy_p(A,m,f,g,phi)
    return result
︡568184e6-ea33-4c7e-80e3-4899079799f4︡{"done":true}
︠db71c397-bec4-49bf-a461-fcaa648a431bs︠
#Examples:
s1 = v2^2-a1*u3 #phi(v2^2)-phi(a1*u3)=[v2*phi(v2)+phi(v2)*gf(v2)]-[a1*phi(u3)+phi(a1)*gf(u3)]=v2*u3-0
phi_homotopy(A,s1,f,g,phi)
︡27de9630-c13f-4a2c-827f-40bf57cac46a︡{"stdout":"v2*u3\n"}︡{"done":true}
︠57231f69-eda3-45a0-b8b7-b1320cb3e45fs︠
s2 = v2^2*u3 #phi(v2^2*u3)-phi(a1*u3)=[v2^2*phi(u3)+phi(v2^2)*gf(u3)]=0
phi_homotopy(A,s2,f,g,phi)
︡0d53843e-091c-4688-9975-349cd8b7dc33︡{"stdout":"0\n"}︡{"done":true}
︠43e6b6ef-29df-4ef3-8c5a-e372dd8e30b0s︠
#-------------------------------------------------------------------------------------------------------------------------------------
#FUNCTION main:
#-------------------------------------------------------------------------------------------------------------------------------------
#Input:  A = Sullivan algebra
#        B = algebra with the same generators as A and differential null.
#        V =  ordering of the generators of A that defines a filtration
#Output: (W,dW) = minimal Sullivan algebra
#        (f,g,phi) = full contraction from A to W
#-------------------------------------------------------------------------------------------------------------------------------------
def main(A,B,V):
    Gen = A.gens()
    num_gen = len(Gen)
    M = Hom(A,B)
    f = M.zero() #Inicialmente, f morfismo nulo
    N = Hom(B,A)
    g = N.zero()
    phi = [0]*len(Gen)
    W = [0]*len(Gen)
    dW = [0]*len(Gen)
    for mi in V:
        a = f(dA.differential()(mi)) #fd(mi)
        b = mi-phi_homotopy(A,dA.differential()(mi),f,g,phi) #mi-phid(mi)
        if Lambda2(A,a) == 1:
            pos = Gen.index(mi) #posición de mi en los generadores
            W[pos] = mi #añadimos mi a W
            #Modificamos f:
            F = f.im_gens()
            F[pos] = mi
            f = M(F)
            #Modificamos g:
            G = g.im_gens()
            G[pos] = b
            g = M(G)
            #Modificamos la diferencial de mi en W
            dW[pos] = a
        else:
            j = 1
            while W[num_gen-j]==0 or coef(a,W[num_gen-j])==0:
                j = j+1
            mj = W[num_gen-j]
            l2 = coef(a,mj)
            #Eliminamos mj de W
            W[num_gen-j]=0
            #Hacemos g(mj)=0
            G = g.im_gens()
            G[num_gen-j]=0
            g = M(G)
            #Modificamos f y phi
            F = f.im_gens()
            for k in range(num_gen):
                l1 = coef(F[k],mj)
                l = l1/l2
                F[k] = F[k] - l*a
                phi[k] = phi[k] + l*b
            f = M(F)
    return f, g, phi, W, dW
︡aa1a8f00-6d66-4ccd-8138-47b91b424580︡{"done":true}
︠ecff1592-7d2a-43c6-90d3-ff754770953a︠
#-------------------------------------------------------------------------------------------------------------------------------------
#EXAMPLE 1:
#-------------------------------------------------------------------------------------------------------------------------------------
A.<a1,b1,c1,v2,u3> = GradedCommutativeAlgebra(QQ, degrees=(1,1,1,2,3))
dA = A.cdg_algebra({a1:v2, u3:v2^2})
B.<a1,b1,c1,v2,u3> = GradedCommutativeAlgebra(QQ, degrees=(1,1,1,2,3))
dB = B.cdg_algebra({})
V = [b1, c1, v2, a1, u3]
[f1,g1,phi1,W1,dW1] = main(A,B,V)
︡ec874864-2802-4e1b-beb6-67294d979667︡{"done":true}
︠e477816a-9908-4b73-9ebf-1a93ea2e5929s︠
#-------------------------------------------------------------------------------------------------------------------------------------
#EXAMPLE 2:
#-------------------------------------------------------------------------------------------------------------------------------------
A.<a1,b1,c1,v2,u3> = GradedCommutativeAlgebra(QQ, degrees=(1,1,1,2,3))
dA = A.cdg_algebra({a1:v2, b1:v2, c1:v2, u3:v2^2})
B.<a1,b1,c1,v2,u3> = GradedCommutativeAlgebra(QQ, degrees=(1,1,1,2,3))
dB = B.cdg_algebra({})
V = [v2, a1, b1, c1, u3]
[f2,g2,phi2,W2,dW2] = main(A,B,V)
︡85a70537-e3dd-40da-a144-c0bcb21c1bee︡{"done":true}
︠81fd9f90-8acc-48da-bac4-6d6274b70792s︠
#-------------------------------------------------------------------------------------------------------------------------------------
#EXAMPLE 3:
#-------------------------------------------------------------------------------------------------------------------------------------
A.<a1,b1,c1,x1,y1,v2,p2,q2,r2,u3> = GradedCommutativeAlgebra(QQ, degrees=(1,1,1,1,1,2,2,2,2,3))
dA = A.cdg_algebra({x1:v2-2*a1*b1+2*b1*c1, y1:v2-2*a1*c1-2*b1*c1, p2:2*v2*a1, q2:2*v2*b1, r2:2*v2*c1, u3:v2^2})
B.<a1,b1,c1,x1,y1,v2,p2,q2,r2,u3> = GradedCommutativeAlgebra(QQ, degrees=(1,1,1,1,1,2,2,2,2,3))
dB = B.cdg_algebra({})
V = [a1,b1,c1,v2,x1,y1,p2,q2,r2,u3]
[f3,g3,phi3,W3,dW3] = main(A,B,V)
︡0a221f27-4f77-41c7-9d47-3e019cf9d1bb︡{"done":true}
︠20cf8b4c-c9ab-407c-9584-5f9436da7dbfs︠
#-------------------------------------------------------------------------------------------------------------------------------------
#EXAMPLE 4:
#-------------------------------------------------------------------------------------------------------------------------------------
A.<v2,w2,v4,w4,x1,x3,x5,x7> = GradedCommutativeAlgebra(QQ, degrees=(2,2,4,4,1,3,5,7))
dA = A.cdg_algebra({x1:v2+w2, x3:v4+w4+v2*w2, x5:v4*w2+v2*w4, x7:v4*w4})
B.<v2,w2,v4,w4,x1,x3,x5,x7> = GradedCommutativeAlgebra(QQ, degrees=(2,2,4,4,1,3,5,7))
dB = B.cdg_algebra({})
V = [v2,w2,v4,w4,x1,x3,x5,x7]
[f4,g4,phi4,W4,dW4] = main(A,B,V)
︡2dab1246-c98a-404f-8ef4-3bf45d533f5b︡{"done":true}
︠5acd6f04-162c-4c0f-99d0-7251a64e1705︠









