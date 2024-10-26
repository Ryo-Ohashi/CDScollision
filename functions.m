/* --------------------------------------------------------     auxiliary functions     -------------------------------------------------------- */

// For a prime q (or q = 1), return a pair [a,b] such that a^2 + d*b^2 = q.
function cornacchia_smith(d,q)
    if q eq 1 then a := 1; b := 0;
    elif LegendreSymbol(-d,q) eq -1 then return [];
    else
        x := q; _,y := IsSquare(GF(q)!(-d)); y := Integers()!y;
        while y gt Isqrt(q) do r := x mod y; x := y; y := r; end while;
        if (q-y^2) mod d eq 0 and IsSquare((q-y^2) div d) then
            a := y; _,b := IsSquare((q-y^2) div d);
        else return []; end if;
    end if;
    return [(-1)^Random(1)*a,(-1)^Random(1)*b];  // randomize output
end function;

// For a positive integer n, return a pair [a,b] such that a^2 + 3*b^2 = n.
function sum_of_two_squares(n)
    if   n eq 1 then return [1,0];
    elif n eq 3 then return [0,1];
    else
        a := 1; b := 0;
        for q in PrimesUpTo(100) do
            e := 0; while n mod q eq 0 do n := n div q; e +:= 1; end while;
            a *:= q^(e div 2); b *:= q^(e div 2);
            if IsOdd(e) then
                if q mod 3 ne 2 then
                    s,t := Explode(cornacchia_smith(3,q)); a,b := Explode([a*s-3*b*t,a*t+b*s]);
                else return []; end if;
            end if;
        end for;
        if n eq 1 or (n mod 3 eq 1 and IsProbablyPrime(n)) then
            s,t := Explode(cornacchia_smith(3,n)); return [a*s-3*b*t,a*t+b*s];
        else return []; end if;
    end if;
end function;

/* -------------------------------------------------------- functions for genus-1 curve -------------------------------------------------------- */

// Return a basis P,Q of the 2^e-torsion group of a supersingular elliptic curve E.
function elltorsion_basis(E,e)
    ord_point := function(E,e)
        K := BaseField(E); p := Characteristic(K); q := (p+1) div 2^e;
        P := q*Random(E); while IsZero(2^(e-1)*P) do P := q*Random(E); end while;
        return P;
    end function;
    P := ord_point(E,e); Q := ord_point(E,e); while WeilPairing(2^(e-1)*P,2^(e-1)*Q,2) eq 1 do Q := ord_point(E,e); end while;
    return P,Q;
end function;

// For a basis P,Q the 2^e-torsion group of E, find integers such that R = a*P + b*Q and S = c*P + d*Q.
function bidiscrete_logarithm(P,Q,R,S,e)
    pairing_PQ := WeilPairing(P,Q,2^e);
    a := Log(pairing_PQ,WeilPairing(R,Q,2^e)); b := Log(pairing_PQ,WeilPairing(P,R,2^e));
    c := Log(pairing_PQ,WeilPairing(S,Q,2^e)); d := Log(pairing_PQ,WeilPairing(P,S,2^e));
    return Matrix(Integers(2^e),[[a,b],[c,d]]);
end function;

// Compute alpha(P) with alpha = a + b*i + c*j + d*k with i^2 = -3, j^2 = -p, k = ij = -ji.
function endomorphism(alpha,P,omega)
    E := Curve(P); K := BaseField(E); p := Characteristic(K);
    sqminus3_action := function(P)
        X := P[1]; Y := P[2]; Z := P[3]; return P + 2*E![omega*X,Y,Z];
    end function;
    frobenius := function(P)
        X := P[1]; Y := P[2]; Z := P[3]; return E![X^p,Y^p,Z^p];
    end function;
    ret  := alpha[1]*P;
    ret +:= alpha[2]*sqminus3_action(P);
    ret +:= alpha[3]*frobenius(P);
    ret +:= alpha[4]*sqminus3_action(frobenius(P)); return ret;
end function;

// Find alpha = a + b*i + c*j + d*ij such that n1*n2 = norm(alpha).
function represent_integer(p,n1,n2)
    while true do
        c := Random(0,Floor(Sqrt(n1*n2/p))); d := Random(0,Floor(Sqrt((n1*n2-p*c^2)/(3*p))));
        tmp := sum_of_two_squares(n1*n2-p*c^2-3*p*d^2);
        if tmp ne [] then a,b := Explode(tmp); return [a,b,c,d]; end if;
    end while;
end function;

/* -------------------------------------------------------- functions for genus-2 curve -------------------------------------------------------- */

// The following codes are Magma implementations of Oudompheng-Pope's formulae for computing (2^e,2^e)-isogenies.
function from_prd_to_jac(E1,E2,P1,Q1,P2,Q2,e)
    K := BaseField(E1); R<x> := PolynomialRing(K);
    a1 := (2^(e-1)*P1)[1]; a2 := (2^(e-1)*Q1)[1]; a3 := (2^(e-1)*P1 + 2^(e-1)*Q1)[1];
    b1 := (2^(e-1)*P2)[1]; b2 := (2^(e-1)*Q2)[1]; b3 := (2^(e-1)*P2 + 2^(e-1)*Q2)[1];
    M := Matrix(K,3,3,[[a1*b1,a1,b1],[a2*b2,a2,b2],[a3*b3,a3,b3]]);
    if Determinant(M) eq 0 then return <>; end if;              // split codomain
    vec := Vector(M^(-1)*Transpose(Matrix(K,[[1,1,1]])));
    s1 := -(a1-a2)*(a2-a3)*(a3-a1)/(Determinant(M)*vec[1]); s2 := -vec[3]/vec[1];
    t1 :=  (b1-b2)*(b2-b3)*(b3-b1)/(Determinant(M)*vec[1]); t2 := -vec[2]/vec[1];
    if a1 eq s2 or a2 eq s2 or a3 eq s2 then return <>; end if; // split codomain
    c1 := (a1-s2)/s1; c2 := (a2-s2)/s1; c3 := (a3-s2)/s1;
    f := s1*(x^2-c1)*(x^2-c2)*(x^2-c3); C := HyperellipticCurve(f); J := Jacobian(C);
    D1 := elt<J|s1*x^2-(P1[1]-s2),P1[2]/s1> + elt<J|(P2[1]-t2)*x^2-t1,P2[2]*x^3/t1>;
    D2 := elt<J|s1*x^2-(Q1[1]-s2),Q1[2]/s1> + elt<J|(Q2[1]-t2)*x^2-t1,Q2[2]*x^3/t1>;
    return <f,D1,D2>;
end function;
function richelot_correspondence(G1,G2,G3,H1,H2,H3)
    assert Coefficient(G1,2) eq 1 and Coefficient(G2,2) eq 1;
    R<x> := Parent(G3); H11 := H1*H1; H12 := H1*H2; H22 := H2*H2; H123 := H12*H3;
    richelot_map := function(D)
        U := D[1]/LeadingCoefficient(D[1]); V := D[2] mod U; 
        assert IsMonic(U) and Degree(V) le 1;
        u0 := Coefficient(U,0); u1 := Coefficient(U,1); v0 := Coefficient(V,0); v1 := Coefficient(V,1);
        g1red := G1 - U; g2red := G2 - U;
        assert Degree(g1red) le 1 and Degree(g2red) le 1;
        g10 := Coefficient(g1red,0); g11 := Coefficient(g1red,1); g20 := Coefficient(g2red,0); g21 := Coefficient(g2red,1);
        Px  := (g11*g11*u0 - g11*g10*u1 + g10*g10)*H11 + (2*g11*g21*u0 - (g11*g20+g21*g10)*u1 + 2*g10*g20)*H12 + (g21*g21*u0 - g21*g20*u1 + g20*g20)*H22; 
        Py2 := v1*v1*u0 - v1*v0*u1 + v0*v0;
        Py1 := (2*v1*g11*u0 - (v1*g10+v0*g11)*u1 + 2*v0*g10)*x + (v1*g11*u0*u1 - 2*v1*g10*u0 - v0*g11*(u1*u1-2*u0) + v0*g10*u1); Py1 *:= H1;
        Py0 := (g11*g11*u0 - g11*g10*u1 + g10*g10)*U*H11;
        _, Py1inv, _ := Xgcd(Py1,Px); Py := -Py1inv*(Py2*H123 + Py0) mod Px;
        assert Degree(Px) eq 4 and Degree(Py) le 3;
        return elt<Jacobian(HyperellipticCurve(H123))|Px,Py>;
    end function;
    return richelot_map;
end function;
function from_jac_to_jac(f,D1,D2,e,powers)
    R<x> := Parent(f); next_powers := []; G1 := (2^(e-1)*D1)[1]; G2 := (2^(e-1)*D2)[1];
    if IsEmpty(powers) then
        if e ge 16 then
            gap := Floor(Sqrt(e)); doubles := [<0,D1,D2>]; dbl1 := D1; dbl2 := D2;
            for i in [1..e-1] do dbl1 := 2*dbl1; dbl2 := 2*dbl2; doubles := Append(doubles,<i,dbl1,dbl2>); end for;
            G1 := doubles[e][2][1]; G2 := doubles[e][3][1]; next_powers := [doubles[e-2*gap],doubles[e-gap]];
        else G1 := (2^(e-1)*D1)[1]; G2 := (2^(e-1)*D2)[1]; end if;
    else
        l,dbl1,dbl2 := Explode(powers[#powers]);
        if e ge 16 then if l lt e-1 then next_powers := powers; else next_powers := powers[1..#powers-1]; end if; end if;
        G1 := (2^(e-l-1)*dbl1)[1]; G2 := (2^(e-l-1)*dbl2)[1];
    end if;
    G1 := G1/LeadingCoefficient(G1); G2 := G2/LeadingCoefficient(G2); G3,r3 := Quotrem(f,G1*G2);
    M := Matrix([[Coefficient(g,0),Coefficient(g,1),Coefficient(g,2)]: g in [G1,G2,G3]]);
    if r3 ne 0 or Determinant(M) eq 0 then return <>; end if;   // split codomain
    Minv := M^(-1); H1 := -Minv[1][1]*x^2 + 2*Minv[2][1]*x - Minv[3][1];
                    H2 := -Minv[1][2]*x^2 + 2*Minv[2][2]*x - Minv[3][2];
                    H3 := -Minv[1][3]*x^2 + 2*Minv[2][3]*x - Minv[3][3]; H123 := H1*H2*H3;
    if e eq 1 then J := Jacobian(HyperellipticCurve(H123)); return <H123,J!0,J!0,[]>;
    else
        richelot_map := richelot_correspondence(G1,G2,G3,H1,H2,H3);
        if next_powers ne [] then next_powers := [<next_power[1],richelot_map(next_power[2]),richelot_map(next_power[3])>: next_power in next_powers]; end if;
        return <H123,richelot_map(D1),richelot_map(D2),next_powers>;
    end if;
end function;
function from_jac_to_prd(G1,G2,G3)
    R<x> := Parent(G3); K := CoefficientRing(R); M := Matrix([[Coefficient(g,0),Coefficient(g,1),Coefficient(g,2)]: g in [G1,G2,G3]]);
    vec := Basis(NullspaceOfTranspose(M))[1]; u := vec[1]; v := vec[2]; w := vec[3];
    d := u/2; b,c := Explode([Roots(x^2-v*x+w*d/2)[i][1]: i in [1,2]]); a := c/d;
    H1 := Vector(M*Transpose(Matrix(K,[[1,a,a^2]]))); H0 := Vector(M*Transpose(Matrix(K,[[d^2,b*d,b^2]])));
    assert Evaluate(G1,(a*x+b)/(x+d))*(x+d)^2 eq H1[1]*x^2 + H0[1];
    n1 := (x+H0[1]*H1[2]*H1[3])*(x+H1[1]*H0[2]*H1[3])*(x+H1[1]*H1[2]*H0[3]); n2 := (x+H1[1]*H0[2]*H0[3])*(x+H0[1]*H1[2]*H0[3])*(x+H0[1]*H0[2]*H1[3]);
    E1 := EllipticCurve([0,Coefficient(n1,2),0,Coefficient(n1,1),Coefficient(n1,0)]); E2 := EllipticCurve([0,Coefficient(n2,2),0,Coefficient(n2,1),Coefficient(n2,0)]);
    return [E1,E2];
end function;
function richelot_codomain(E1,E2,P1,Q1,P2,Q2,e)
    next_powers := [];
    temp := from_prd_to_jac(E1,E2,P1,Q1,P2,Q2,e); if IsEmpty(temp) then return []; else f,D1,D2 := Explode(temp); end if;
    for i in [1..e-1] do
        temp := from_jac_to_jac(f,D1,D2,e-i,next_powers); if IsEmpty(temp) then return []; else f,D1,D2,next_powers := Explode(temp); end if;
    end for;
    return G2Invariants(HyperellipticCurve(f));
end function;
function richelot_tracking(E1,E2,P1,Q1,P2,Q2,e)
    next_powers := []; tracks := []; 
    f,D1,D2 := Explode(from_prd_to_jac(E1,E2,P1,Q1,P2,Q2,e)); tracks := Append(tracks,HyperellipticCurve(f));
    for i in [1..e-2] do
        f,D1,D2,next_powers := Explode(from_jac_to_jac(f,D1,D2,e-i,next_powers)); tracks := Append(tracks,HyperellipticCurve(f));
    end for;
    G1 := D1[1]; G2 := D2[1]; G3,r3 := Quotrem(f,G1*G2); M := Matrix([[Coefficient(g,0),Coefficient(g,1),Coefficient(g,2)]: g in [G1,G2,G3]]);
    assert r3 eq 0 and Determinant(M) eq 0;     // the last isogeny should have a split codomain
    return tracks,from_jac_to_prd(G1,G2,G3);
end function;

// The following code is a slightly modified version of Castryck-Decru-Smith's hash function.
function CDS(K,mbase8)
    fac := function(poly)
        ram := [rt[1]: rt in Factorization(poly)];
        if #ram eq 1 then Append(~ram,1); end if; return ram;
    end function;
    splits := [[{1,3},{2,5},{4,6}], [{1,3},{2,6},{4,5}],
               [{1,4},{2,5},{3,6}], [{1,4},{2,6},{3,5}],
               [{1,5},{2,3},{4,6}], [{1,5},{2,4},{3,6}],
               [{1,6},{2,3},{4,5}], [{1,6},{2,4},{3,5}]];
    R<x> := PolynomialRing(K); factors := [x-1,x+1,x,x-2,x-1/2,1];
    for i := 1 to #mbase8 do
        split := splits[mbase8[i]+1];
        G1 := &*[factors[j]: j in split[1]]; G2 := &*[factors[j]: j in split[2]]; G3 := &*[factors[j]: j in split[3]];
        h1 := Derivative(G2)*G3 - G2*Derivative(G3); r1 := fac(h1);
        h2 := Derivative(G3)*G1 - G3*Derivative(G1); r2 := fac(h2);
        if Rank(Matrix([[Coefficient(h1,j): j in [0..2]],[Coefficient(h2,j): j in [0..2]]])) eq 1 then
            print "No hash for this value possible."; return [];  // the codomain is a product of two elliptic curves
        end if;
        h3 := Derivative(G1)*G2 - G1*Derivative(G2); r3 := fac(h3); factors := r1 cat r2 cat r3;
    end for;
    return G2Invariants(HyperellipticCurve(&*factors));
end function;