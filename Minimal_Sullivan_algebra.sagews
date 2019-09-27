︠cc7aed79-5a38-4259-8e2d-2dc430fecc70︠
#-------------------------------------------------------------------------------------------------------------------------------------
#AUXILIARY FUNCTIONS:
#-------------------------------------------------------------------------------------------------------------------------------------
︡3c30744c-eed0-4a28-bfe5-1cc53323b6ac︡{"done":true}
︠9dfe6a6f-7c0c-4ade-8c60-d7086c93c654s︠
#-------------------------------------------------------------------------------------------------------------------------------------
#FUNCTION aux1:
#-------------------------------------------------------------------------------------------------------------------------------------
#Input:  A = a Sullivan algebra
#        p = a linear combination of elements of the base of A (for example, p = 2*b*c - v)
#Output: M = list of lists where the elements of each sublist are the generators de A that form each sum of the string p (for example, M = [[b,c],[v]])
#        C = list with the coefficients of each sum of p (for example, C = [2,-1])
#-------------------------------------------------------------------------------------------------------------------------------------
def aux1(A,p):
    if p==0:
        return 0
    else:
        M = []
        C = []
        L = p.monomials()
        coef = p.basis_coefficients()
        pos_coef_no_nulos = [i for i,x in enumerate(coef) if x!=0]
        d = p.degree()
        B = A._basis_for_free_alg(d)
        for i in range(0,len(pos_coef_no_nulos)):
            sumando = B[pos_coef_no_nulos[i]]
            N = []
            for j in range(len(sumando)):
                n = sumando[j]
                while n>0:
                    N.append(A.gen(j))
                    n = n-1
            c = pos_coef_no_nulos[i]
            C.append(coef[c])
            M.append(N)
        return M,C
︡5eb162d6-8641-45bc-8627-0dd817de636a︡{"done":true}
︠9fce7837-c38c-4a8b-9845-dab89ba01aeds︠
#-------------------------------------------------------------------------------------------------------------------------------------
#FUNCTION last_simple:
#-------------------------------------------------------------------------------------------------------------------------------------
#Input:  S = output of the function aux1
#        V = ordering of the generators of A that defines a filtration
#Output: V[n] = last simple element of p
#        c = coefficient of the V[n] in p
#        (c = -1 if S = 0 or if there is not simple elements)
#-------------------------------------------------------------------------------------------------------------------------------------
def last_simple(S,V):
    n = -1
    if S == 0:
        return n
    else:
        #n = -1
        c = 0
        M = S[0]
        C = S[1]
        for l in M:
            pos_l = M.index(l)
            if len(l)==1:
                pos = V.index(l[0])
                if pos > n:
                    n = pos
                    c = C[pos_l]
    if n == -1:
        return n
    else:
        return V[n],c
︡93f7f06b-7747-4bc6-bcbc-b9510a184fe7︡{"done":true}
︠a4baf0bb-6866-4177-a98a-1a7c3a39e675s︠
#-------------------------------------------------------------------------------------------------------------------------------------
#FUNCTION aux2:
#-------------------------------------------------------------------------------------------------------------------------------------
#Input:  A = Sullivan algebra
#        F = list with the images of the generators of A
#        mj = generator of A
#Output: M = list of lists [a,b] such that mj appears in the image of the generator at the position a with coefficient b.
#-------------------------------------------------------------------------------------------------------------------------------------
def aux2(A,F,mj): #For example, F = f.im_gens
    M = []
    i = -1
    for g in F:
        i = i+1
        if g != 0:
            #i = i+1
            L = aux1(A,g)[0]
            C = aux1(A,g)[1]
            j = -1
            for l in L:
                j = j+1
                #if mj in l
                if len(l) == 1 and l.count(mj) == 1:
                    pos_l = L.index(l)
                    b = C[pos_l]
                    M.append([i,b])
    return M
︡ec2867f9-b8d6-454c-9a66-8aa0f6a030b0︡{"done":true}
︠11696ed9-6b5f-4d27-9f27-5d4abcba0eeds︠
#-------------------------------------------------------------------------------------------------------------------------------------
#FUNCTION phi_recursive:
#-------------------------------------------------------------------------------------------------------------------------------------
#Input:  A = Sullivan algebra
#        l = product of generators of A
#        f, g, phi = imagens of the morphisms f,g and phi of the generators de A
#Output: result = string phi(l).
#-------------------------------------------------------------------------------------------------------------------------------------
def phi_recursive(A,l,f,g,phi):
    if len(l)==1:
        result = phi[A.gens().index(l[0])]
    else:
        L1 = [l[0]]
        L2 = []
        for j in range(len(l)-1):
            L2.append(l[j+1])
        L1
        L2
        if len(L2)==1:
            result = L1[0]*phi[A.gens().index(L2[0])]+phi[A.gens().index(L1[0])]*g(f(L2[0]))
        else:
            m = 1
            for e in L2:
                m = m*e
            result = L1[0]*phi_recursive(L2,phi,A,f,g) + phi[A.gens().index(L1[0])]*g(f(m))
    return result

︡e81a5cb5-19b8-4b00-8c7e-dba07734364a︡{"done":true}
︠963859b2-b70b-4d40-b8fe-a6f1236d9019s︠
#-------------------------------------------------------------------------------------------------------------------------------------
#FUNCTION phi_homotopy:
#-------------------------------------------------------------------------------------------------------------------------------------
#Input:  A = Sullivan algebra
#        c = a string, that is, a linear combination of elements of the base of A
#        f, g, phi = imagens of the morphisms f,g and phi of the generators de A
#Output: result = string phi(c).
#-------------------------------------------------------------------------------------------------------------------------------------
def phi_homotopy(A,c,f,g,phi):
    if c==0:
        return 0
    else:
        result = 0
        P = aux1(A,c)[0]
        C = aux1(A,c)[1]
        i = 0
        for p in P:
            result = result + C[i]*phi_recursive(A,p,f,g,phi)
            i = i+1
        return result
︡bfcc7344-bb59-46b3-b165-cd79bf130d70︡{"done":true}
︠48770299-b1f1-4b98-b247-617ac45bca69︠
︡34ef8cc0-dbaa-4d91-ad40-6a26b66889de︡
︠8c36632f-cdd3-4346-a07a-974ab1e1d74ds︠
#-------------------------------------------------------------------------------------------------------------------------------------
#FUNCTION main:
#-------------------------------------------------------------------------------------------------------------------------------------
#Input:  A = Sullivan algebra
#        B = algebra with the same generators as A and differential null.
#        V =  ordering of the generators of A that defines a filtration
#Output: (W,dW) = minimal Sullivan algebra
#        (f,g,phi) = full contraction from A to H
#-------------------------------------------------------------------------------------------------------------------------------------
def main(A,B,V):
    Gen = A.gens()
    M = Hom(A,B)
    f = M.zero()       #Inicialmente, f morfismo nulo
    N = Hom(B,A)
    g = N.zero()       #Inicialmente, g morfismo nulo
    phi = [0]*len(Gen) #Inicialmente, phi = 0 para todos los generadores
    W = [0]*len(Gen)   #Inicialmente, H = lista de ceros (lo cual indica h vacía)
    dW = [0]*len(Gen)  #Inicialmente, dH = lista de ceros
    Gen = A.gens()     #Lista con los generadores de A
    for mi in V:
        fd = aux1(A,f(dA.differential()(mi)))
        us = last_simple(fd,V)
        if us == -1: #es decir, si fd(mi) es nulo o suma de elementos no simples
            pos = Gen.index(mi) #posición de mi en los generadores
            #Añadimos mi a H
            W[pos] = mi
            #Modificamos la diferencial en B
            dW[pos] = f(dA.differential()(mi))
            #Modificamos f:
            F = f.im_gens()
            F[pos] = mi
            f = M(F)
            #Modificamos g:
            G = g.im_gens()
            G[pos] = mi - phi_homotopy(A,dA.differential()(mi),f,g,phi)
            g = M(G)
        else:
            mj = us[0]
            a = us[1]
            posj = Gen.index(mj)
            #Eliminamos mj de H
            W[posj] = 0
            #la g de mj la hacemos 0
            G = g.im_gens()
            G[posj] = 0
            g = M(G)
            F = f.im_gens()
            #Buscamos quién tiene mj en la imagen de f
            L = aux2(A,F,mj)
            for l in L:
                b = l[1]
                x = l[0]
                #Modificamos f y phi
                F = f.im_gens()
                F[x] = f(Gen[x]) - b/a*f(dA.differential()(mi))
                f = M(F)
                phi[x] = phi[x]+b/a*(mi-phi_homotopy(A,dA.differential()(mi),f,g,phi))
    return f, g, phi, W, dW
︡fe9db107-1652-4dc6-9b50-7f3ed50d590f︡{"done":true}
︠cc7008ae-be8b-4e32-880e-ed8e7ac8d328s︠
︡0ef2cf36-5849-4179-9bc2-5690426d7924︡
︠6b7c2807-25c7-465a-888f-fa5fa384b51fs︠
#-------------------------------------------------------------------------------------------------------------------------------------
#EJEMPLO 1:
#-------------------------------------------------------------------------------------------------------------------------------------
#Definimos las álgebras A y B y sus diferenciales (la diferencial de B la inicializamos a 0)
A.<a1,b1,c1,v2,u3> = GradedCommutativeAlgebra(QQ, degrees=(1,1,1,2,3))
dA = A.cdg_algebra({a1:v2, u3:v2^2})
B.<a1,b1,c1,v2,u3> = GradedCommutativeAlgebra(QQ, degrees=(1,1,1,2,3))
dB = B.cdg_algebra({})
V = [b1, c1, v2, a1, u3]
︡960444ba-ad63-414d-b90c-55213cbcf7da︡{"done":true}
︠33208471-79d5-429b-a243-a667ab864741s︠
[f,g,phi,W,dW] = main(A,B,V)
︡03352047-fb7c-4c69-b25d-85ab7a3f0e84︡{"done":true}
︠9979b90a-ef37-4e3a-a786-a0aa546df5des︠
#-------------------------------------------------------------------------------------------------------------------------------------
#EJEMPLO 2:
#-------------------------------------------------------------------------------------------------------------------------------------
︡b5cd136f-1143-4357-98c1-08bc7acd6988︡{"done":true}
︠25d7a6dd-2fa7-4c47-9a71-537763887113s︠
#Definimos las álgebras A y B y sus diferenciales (la diferencial de B la inicializamos a 0)
A.<a1,b1,c1,v2,u3> = GradedCommutativeAlgebra(QQ, degrees=(1,1,1,2,3))
dA = A.cdg_algebra({a1:v2, b1:v2, c1:v2, u3:v2^2})
B.<a1,b1,c1,v2,u3> = GradedCommutativeAlgebra(QQ, degrees=(1,1,1,2,3))
dB = B.cdg_algebra({})
V = [v2, a1, b1, c1, u3]
︡fef15b3d-ed2a-41ba-9b13-c3e44360dfa1︡{"done":true}
︠4a42d908-4aec-4e27-99ea-21dfd7c7e50fs︠
[f,g,phi,W,dW] = main(A,B,V)
︡beef33c5-8df3-42a5-bf18-c2247761b445︡{"done":true}
︠2417d60f-97ac-4fda-a495-bc162e086510s︠
#-------------------------------------------------------------------------------------------------------------------------------------
#EJEMPLO 3:
#-------------------------------------------------------------------------------------------------------------------------------------
︡4a6fc6de-c53e-4aec-9f99-236b7ca7a5e9︡{"done":true}
︠e247114d-9cbd-4110-bc21-0e6c2f2498fcs︠
#Definimos las álgebras A y B y sus diferenciales (la diferencial de B la inicializamos a 0)
A.<a1,b1,c1,x1,y1,v2,p2,q2,r2,u3> = GradedCommutativeAlgebra(QQ, degrees=(1,1,1,1,1,2,2,2,2,3))
dA = A.cdg_algebra({x1:v2-2*a1*b1+2*b1*c1, y1:v2-2*a1*c1-2*b1*c1, p2:2*v2*a1, q2:2*v2*b1, r2:2*v2*c1, u3:v2^2})
B.<a1,b1,c1,x1,y1,v2,p2,q2,r2,u3> = GradedCommutativeAlgebra(QQ, degrees=(1,1,1,1,1,2,2,2,2,3))
dB = B.cdg_algebra({})
V = [a1,b1,c1,v2,x1,y1,p2,q2,r2,u3]
︡a7f12e33-9c98-4298-b638-31d1eb4a7c77︡{"done":true}
︠3e85a267-b8d5-47dd-8ab2-f5edf86e7e26s︠
[f,g,phi,W,dW] = main(A,B,V)
︡a7d6ecb9-3021-471c-b40d-7c65527ac3d7︡{"done":true}
︠f194307f-5ef5-466a-981a-84448baf700fs︠
#-------------------------------------------------------------------------------------------------------------------------------------
#EJEMPLO 4:
#-------------------------------------------------------------------------------------------------------------------------------------
︡e362865e-fb8a-464d-8ad7-599258e99cf0︡{"done":true}
︠ae138156-e5e0-4a86-a4ca-2a4cab97448cs︠
#Definimos las álgebras A y B y sus diferenciales (la diferencial de B la inicializamos a 0)
A.<v2,w2,v4,w4,x1,x3,x5,x7> = GradedCommutativeAlgebra(QQ, degrees=(2,2,4,4,1,3,5,7))
dA = A.cdg_algebra({x1:v2+w2, x3:v4+w4+v2*w2, x5:v4*w2+v2*w4, x7:v4*w4})
B.<v2,w2,v4,w4,x1,x3,x5,x7> = GradedCommutativeAlgebra(QQ, degrees=(2,2,4,4,1,3,5,7))
dB = B.cdg_algebra({})
V = [v2,w2,v4,w4,x1,x3,x5,x7]
︡3151e6d6-321d-4e56-89ba-d0e416bc4c93︡{"done":true}
︠878d8b9b-7942-411c-b178-871748135c2cs︠
[f,g,phi,W,dW] = main(A,B,V)
︡4a97fa9f-b119-4ce8-a05d-457213c8bd29︡{"done":true}
︠77c458e1-c8cb-47a7-9754-b89c920d3ec1s︠
︡276b649d-70de-4754-bfae-373427fa9d7f︡{"done":true}
︠5fb1904e-04b8-46be-913a-86ad1f7d48d5s︠
︡57835c3b-dedd-4107-91c8-f96e202463d8︡{"done":true}
︠c89ff726-0cb3-4845-a870-b14440bc8014︠










