###########################################################################
## Local function to calculate the centralizer in a central factor       ##
###########################################################################

CentralizerCentralFactor := function(G, pcp, elms, C)

    local   N,      #Subgroup Gi
            M,      #Subgroup Gi+1
            fac,    #Factor group C/Gi in each step
            gens,   #Generators of gen
            rels,   #Relation matrix of Gi/G(i+1)
            elm,    #Single elements on elms
            matrix, #Matrix representing the image of the homomorphism f
            null,   #Kernel of f
            stb;    #Elements corresponding to the kernel

    N := SubgroupByIgs( G, NumeratorOfPcp(pcp) );
    fac := Pcp(C, N); 
    gens:= AsList(fac);

    rels := ExponentRelationMatrix( pcp );
    stb  := gens;

    for elm in elms do
        if Length( stb ) <> 0 then 

            # set up matrix
            matrix := List( stb, h -> ExponentCyclicPcpFactor( pcp, Comm(h,elm) ) );
            Append( matrix, rels );

            # get nullspace
            null := PcpNullspaceIntMat( matrix );
            null := null{[1..Length(null)]}{[1..Length(stb)]};
            # calculate elements corresponding to null
            stb  := List( null, x -> MappedVector( x, stb ) );
            stb  := Filtered( stb, x -> x <> x^0 );
        fi;
    od;

    stb := AddIgsToIgs( stb, Igs(N) );
    return SubgroupByIgs( G, stb );

end;

###########################################################################
## Local function to calculate the centralizer in a elementary abelian   ##
###########################################################################

CentralizerElementaryAbFactor := function(G, pcp, elms, C)

    local   p,      #Prime order of the pcp
            F,      #Finite field defined by the order p
            d,      #Rank of the pcp
            e,      #(0,...,0,1) vector
            M,      #Denominator of pcp
            fac,    #Group actiong on the pcp
            elm,    #Loop element
            act,    #Affine action of G on A determied by the element g
            stb;    #Stabilizer of act

    d := RelativeOrdersOfPcp( pcp );
    p := d[1];
    d := Length( d );
    F := GF(p);
    M := SubgroupByIgs( G, DenominatorOfPcp(pcp) );
    
    if d = 1 then 
        e := [0,1];
        for elm  in elms do
            fac := Pcp(C, M);
            act := AffineActionOnCyclicPcp(fac, pcp, elm);
            act := InducedByField( act, F );
            stb := PcpOrbitStabilizer( e*One(F), fac, act, OnRight );
            stb := AddIgsToIgs(stb.stab, Igs(M));
            C   := SubgroupByIgs(G, stb);
        od;
    
    else 
        e := ListWithIdenticalEntries(d, 0); Add(e, 1);
        for elm  in elms do
            fac := Pcp(C, M);
            act := AffineActionByElement(fac, pcp, elm);
            act := InducedByField( act, F );
            stb := PcpOrbitStabilizer( e*One(F), fac, act, OnRight );
            stb := AddIgsToIgs(stb.stab, Igs(M));
            C   := SubgroupByIgs(G, stb);
        od;
    
    fi;

    return C;

end;

###########################################################################
## Local function to calculate the centralizer of a set of elements in G ##
###########################################################################

CentralizerFinitePolyGroupSeries := function(G, elms, pcps)

    local   C,      #Centralizer of elms in G
            i,      #Bucle variable
            pcp,    #Factor on each step Gi/G(i+1)
            p,      #Order of the factor
            lin,
            GM;

    C := G;

    for i in [2..Length(pcps)] do

        pcp := pcps[i];

        if pcp!.ceacentralfactor then

            Info( InfoConjugacy, 1, StringFormatted("Layer {} is central.", i) );
            
            C := CentralizerCentralFactor(G, pcp, elms, C);

        else

            Info( InfoConjugacy, 1, StringFormatted("Layer {} is finite of order", i) );
            
            C := CentralizerElementaryAbFactor(G, pcp, elms, C);

        fi;

    od;
    return C;

end;

############################################################################
## Global function to calculate the centralizer of a set of elements in G ##
############################################################################

InstallGlobalFunction ( "CentralizerFinitePoly", function(G, elms)

    if not IsList(elms) then
        elms := [elms];
    fi;

    return CentralizerFinitePolyGroupSeries(G, elms, PcpsOfCeaSeries( G ));

end );

###########################################################################
##          Local function to check if two elements                      ##
##          are conjugated in a central factor                           ##
###########################################################################

ConjugacyCentralFactor := function(G, pcp, g, h, conj)

    local   c,
            N,
            fac,
            gens,
            exp,
            rels,
            matrix,
            solv,
            null;

    c    := g^conj.k;
    N    := SubgroupByIgs( G, NumeratorOfPcp( pcp ) );
    fac  := Pcp( conj.C, N );
    gens := AsList( fac );
    exp  := ExponentCyclicPcpFactor( pcp, c^-1 * h );

    rels := ExponentRelationMatrix( pcp );

    if Length( gens ) = 0 then

        if exp = 0*exp then
            solv := One(G);
        else
            return false;
        fi;
            
    else

        matrix := List( gens, x -> ExponentCyclicPcpFactor( pcp, Comm( x, c ) ) );
        Append( matrix, rels );

        solv   := PcpSolutionIntMat( matrix, -exp );
        if IsBool( solv ) then
            return false;
        else
            solv := solv{[1..Length(gens)]};
            solv := MappedVector( solv, gens );

            null := PcpNullspaceIntMat( matrix );
            null := null{[1..Length(null)]}{[1..Length(gens)]};

            gens := List( null, x -> MappedVector( x, gens ) );
            gens := Filtered( gens, x -> x <> x^0 );
        fi;
    fi;

    gens := AddIgsToIgs( gens, Igs(N) );

    return rec( C := SubgroupByIgs( G, gens ), k := conj.k * solv );

end ;

###########################################################################
##          Local function to check if two elements                      ##
##          are conjugated in a elementary abelian factor                ##
###########################################################################

ConjugacyElementaryAbFactor := function(G, pcp, g, h, conj)

    local   c,
            d,
            p,
            F,
            M,
            e,
            f,
            fac,
            act,
            stb,
            j,
            solv,
            C;

    c    := g^conj.k;
    d    := RelativeOrdersOfPcp( pcp );
    p    := d[1];
    d    := Length( d );
    F    := GF(p);
    M    := SubgroupByIgs( G, DenominatorOfPcp(pcp) );
    fac  := Pcp( conj.C, M );

    if d = 1 then
        e   := [0,1];
        f   := ExponentCyclicPcpFactor( pcp, c^-1 * h ); Add( f, 1 );
        act := AffineActionOnCyclicPcp( fac, pcp, c);
    else
        e   := ListWithIdenticalEntries(d, 0); Add(e, 1);
        f   := ExponentsByPcp( pcp, c^-1*h ); Add( f, 1 );
        act := AffineActionByElement( fac, pcp, c );
    fi;

    act  := InducedByField( act, F );
    stb  := PcpOrbitStabilizer( e*One(F), fac, act, OnRight );

    # extract results
    j    := Position( stb.orbit, f*One(F) );
    if IsBool(j) then return false; fi;
    solv := TransversalElement( j, stb, One(G) );
    stb  := AddIgsToIgs( stb.stab, Igs(M) );

    return rec( C := SubgroupByIgs( G, stb ), k := conj.k * solv);
    
end ;

###########################################################################
## Local function to check if two elements are conjugated in G           ##
###########################################################################

IsConjugateFinitePolySeries := function(G, g, h, pcps)

    local   conj,
            i,
            pcp,
            k;
            
    Info( InfoConjugacy, 1, StringFormatted( "The algorithm has to do {} layers", Length(pcps) ) );

    # the first layer
    if Exponents( g )[1] <> Exponents( h )[1] then 
        return false; 
    fi;

    conj := rec( C := G, k := One(G) );

    for i in [1..Length(pcps)] do

        pcp := pcps[i];

        if pcp!.ceacentralfactor then

            Info( InfoConjugacy, 1, StringFormatted("Layer {} is central.", i) );

            conj := ConjugacyCentralFactor(G, pcp, g, h, conj);

        else

            Info( InfoConjugacy, 1, StringFormatted("Layer {} is finite of order", i) );

            conj := ConjugacyElementaryAbFactor(G, pcp, g, h, conj);

        fi;
    od;

    return conj;

end;

###########################################################################
## Global function to check if two elements are conjugated in G          ##
###########################################################################

InstallGlobalFunction( "IsConjugateFinitePoly", function(G, g, h)

    return IsConjugateFinitePolySeries( G, g, h, PcpsOfCeaSeries(G) );

end );