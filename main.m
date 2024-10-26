load "functions.m";

// parameter setting
a := 86; b := 1; f := 6397*229172347; length := 10;
/* a := 150; b := 1; f := 5*19*199*45153169*639964709*49503663809; length := 10; */
p := 2^a*3^b*f - 1; printf "Field characteristic is set to p = 2^%o*3^%o*%o - 1.\n", a,b,f;
K<i> := ExtensionField<FiniteField(p),x|x^2+1>; omega := RootOfUnity(3,K); R<x> := PolynomialRing(K);
e := 1; repeat
    e +:= 1; n1 := 2^(e-1)+1; n2 := 2^(e-1)-1;
until n1*n2/Log(n1*n2) gt 15*8^length*p; printf "First of all, we choose n1 = %o and n2 = %o such that n1 + n2 = 2^%o.\n", n1,n2,e;

// pre-computation
mbase8 := []; target := [];
for i in [1..length+1] do target := Append(target,CDS(K,mbase8)); mbase8 := Append(mbase8,0); end for;
E0 := EllipticCurve(x^3+1); P0,Q0 := elltorsion_basis(E0,e); P := 2^(e-1)*P0; Q := 2^(e-1)*Q0; matrix_list := [];
for b11,b12,b21,b22 in [0,1] do
    codomain := richelot_codomain(E0,E0,n1*P,n1*Q,b11*P+b12*Q,b21*P+b22*Q,1);
    if codomain eq target[1] then matrix_list := Append(matrix_list,Matrix(Integers(2^(length+1)),[[b11,b12],[b21,b22]])); end if;
end for;
for step in [1..length] do
    P := 2^(e-step-1)*P0; Q := 2^(e-step-1)*Q0; temp_list := [];
    for matrix in matrix_list do
        for b11,b12,b21,b22 in [0,1] do
            temp := ChangeRing(matrix,Integers()) + 2^step*Matrix([[b11,b12],[b21,b22]]);
            codomain := richelot_codomain(E0,E0,n1*P,n1*Q,temp[1][1]*P+temp[1][2]*Q,temp[2][1]*P+temp[2][2]*Q,step+1);
            if codomain eq target[step+1] then temp_list := Append(temp_list,ChangeRing(temp,Integers(2^(length+1)))); end if;
        end for;
    end for;
    matrix_list := temp_list; 
end for;
m1 := IdentityMatrix(Integers(2^(length+1)),2);
m2 := bidiscrete_logarithm(P,Q,endomorphism([0,1,0,0],P,omega),endomorphism([0,1,0,0],Q,omega),length+1);
m3 := bidiscrete_logarithm(P,Q,endomorphism([0,0,1,0],P,omega),endomorphism([0,0,1,0],Q,omega),length+1);
m4 := bidiscrete_logarithm(P,Q,endomorphism([0,0,0,1],P,omega),endomorphism([0,0,0,1],Q,omega),length+1);
printf "From now on, we are going to find a desired alpha whose norm = n1*n2...\n\n";

// endomorphism search
num := 0; start := Realtime();
repeat
    alpha := represent_integer(p,n1,n2); a,b,c,d := Explode(alpha); M := a*m1 + b*m2 + c*m3 + d*m4;
    num +:= 1; if num mod 100 eq 0 then printf "This is the %oth challenge, and it has taken %3o seconds so far.\n", num,Realtime(start); end if;
until M in matrix_list;
printf "\nFinally, we found a desired alpha = %o!!\n", alpha;
printf "For this, we tried %o random endomorphisms, and it took %3o seconds in total.\n\n", num,Realtime(start);

// collision detection
Pa := endomorphism(alpha,P0,omega); Qa := endomorphism(alpha,Q0,omega); chain := richelot_tracking(E0,E0,n1*P0,n1*Q0,Pa,Qa,e);
msg1 := []; step := 1;
while step le #chain do
    inv := G2Invariants(chain[step]);
    for bit in [0..7] do if CDS(K,msg1 cat [bit]) eq inv then msg1 := msg1 cat [bit]; break; end if; end for;
    step := step + 1;
end while;
msg2 := msg1; msg1 := Prune(msg1);
for bit in [0..7] do if CDS(K,msg2 cat [bit]) eq G2Invariants(chain[#chain-1]) then msg2 := msg2 cat [bit]; break; end if; end for;
assert CDS(K,msg1) eq CDS(K,msg2);
integer1 := Integers()!(SequenceToInteger(msg1,8)/2^(3*length)); integer2 := Integers()!(SequenceToInteger(msg2,8)/2^(3*length));
message1 := IntegerToString(integer1,16); message2 := IntegerToString(integer2,16); 
printf "The following are messages which cause a collision of CDS hash function:\n";
printf "   message1 = %o,\n   message2 = %o.", message1,message2;
