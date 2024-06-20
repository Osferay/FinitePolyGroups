IsCentralPcp := function(G, pcp)

    local   M,
            N,
            gen,
            gens;
    
    M    := NumeratorOfPcp(pcp);
    N    := Subgroup(G, DenominatorOfPcp(pcp));

    gen  := Filtered( M, x -> not x in N )[1];
    gens := Filtered( Igs(G), x -> not x in N );

    if ForAll( gens, x -> Comm(x, gen) in N ) then
        return true;
    else
        return false;
    fi;

end ;

####################################################################
### Returns true if is less or equal in the order                ###
### 0 << 1 << ... << -1 << ...                                   ###
####################################################################

IntegerOrder := function(a,b)
    if a = 0 then
        return true;
    elif b = 0 then
        return false;
    elif a > 0 then
        if b < 0 then
            return true;
        else
            return a <= b;
        fi;
    else
        if b > 0 then
            return false;
        else
            return b <= a;
        fi;
    fi;
end;   

####################################################################
### Returns true if is less in the order                         ###
### 0 << 1 << ... << -1 << ...                                   ###
####################################################################

IntegerOrderStrict := function(a,b)
    if a = 0 then
        return true;
    elif b = 0 then
        return false;
    elif a > 0 then
        if b < 0 then
            return true;
        else
            return a < b;
        fi;
    else
        if b > 0 then
            return false;
        else
            return b < a;
        fi;
    fi;
end; 

####################################################################
### Returns true if is less or equal in the order                ###
### extended to the exponents of g and h                         ###
####################################################################

ExponentOrder := function(g,h)
    local   e1, #Exponents of g
            e2, #Exponents of h
            i;  #Bucle variable

    e1  := Exponents(g);
    e2  := Exponents(h);

    for i in [1..Length(e1)] do
        if e1[i] <> e2[i] then
            return IntegerOrder( e1[i], e2[i] );
        fi;
    od;
    return true;
end;

####################################################################
### Returns true if g <<= h                                      ###
####################################################################

InstallGlobalFunction( "ConjugacyOrder" , function(g,h) 

    local   fam,ord;

    fam := FamilyObj( g );
    ord := OrderingByLessThanFunctionNC(fam, ExponentOrder);

    return IsLessThanUnder(ord, g, h);

end );

####################################################################
### Sifting algorithm using a sequence                           ###
####################################################################

SiftingWithGens := function(arg)

    local   gen,    #Canonical generators of U
            g,      #Element to sift
            n,      #Number of generators
            d,      #List of depths of the generators
            exp,    #Exponents of the depths of the generators   
            y,      #Element to return such that gy^-1 is in the subgroup
            B,      #Exponent vector of xy^-1
            alp,    #Exponents of the element in each depth
            l,      #List of conditions
            i;      #Bucle variable

    gen := arg[1];
    g   := arg[2];

    if Length(arg) = 2 then  
        n   := Length(gen);
        d   := List( gen, Depth );
        exp := List( gen, Exponents );
        exp := List( [1..n], x -> exp[x][d[x]]);
    else
        n   := arg[3];
        d   := arg[4];
        exp := arg[5];
    fi;
    
    y   := g;
    B   := List( [1..n], x -> 0);
    alp := List( [1..n], x -> Exponents(y)[d[x]]);
    l   := List( [1..n], x -> IntegerOrderStrict( alp[x], exp[x]) );
    
    while not ForAll( l, x -> x = true ) do
        i    := PositionProperty(l, x -> x = false );
        B[i] := Int( alp[i] / exp[i] );
        y    := (gen[i] ^ -B[i]) * y;
        alp := List( [1..n], x -> Exponents(y)[d[x]]);
        l   := List( [1..n], x -> IntegerOrderStrict( alp[x], exp[x]) );
    od;

    return rec( y := y, B := B);

end ;

####################################################################
### Sifting algorithm using a subgroup                           ###
####################################################################

InstallGlobalFunction( "Sifting", function(U, g)

    local   gen,    #Canonical generators of U
            n,      #Number of generators
            d,      #List of depths of the generators
            exp;    #Exponents of the depths of the generators
            
    gen := Cgs(U);
    n   := Length(gen);
    d   := List( gen, Depth );
    exp := List( gen, Exponents );
    exp := List( [1..n], x -> exp[x][d[x]]);

    return SiftingWithGens(gen, g, n, d, exp);

end );

InstallGlobalFunction( "ExponentCyclicPcpFactor", function( pcp, g)

    local   N,      #Denominator of pcp
            M,      #Numerator of pcp
            gen,    #Length of the exponent vector
            exp,    #Exponent to return
            d,      #Depth of gen
            a,      #Exponent of gen
            b;      #Exponent of generator of N

    #trivial cases

    N := DenominatorOfPcp(pcp);
    M := NumeratorOfPcp(pcp);
    gen := M[1];
    d   := Depth(gen);
    exp := Exponents(g)[d];

    if Length(M) <> Length(N) and Length(N) <> 0 then
        exp := [ exp ];
    elif Length(N) = 0 then
        a   :=   Exponents( gen )[d];
        exp := [ exp / a ];
    else
        a :=   Exponents( gen )[d];
        b :=   Exponents(N[1])[d];
        exp := exp mod b;
        exp := [ exp / a ];
    fi;

    if IsInt( exp[1] ) then 
        return exp;
    else
        return false;
    fi;

end );