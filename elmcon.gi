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
            Print( "Standard", List( stb, h -> ExponentsByPcp(pcp, Comm(h,elm))),"\n");
            Print(matrix, "\n");
            Print( List( stb, h -> Comm(h, elm) ) , "\n");
            
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

CentralizerElementaryAbFactor := function(G, pcp, elms, C, p)

    local   F,      #Finite field defined by the order p
            d,      #Rank of the pcp
            e,      #(0,...,0,1) vector
            M,      #Denominator of pcp
            fac,    #Group actiong on the pcp
            elm,    #Loop element
            act,    #Affine action of G on A determied by the element g
            stb;    #Stabilizer of act

    F := GF(p);
    M := SubgroupByIgs( G, DenominatorOfPcp(pcp) );
    d := Length( RelativeOrdersOfPcp( pcp ) );
    # Print(pcp, "\n");
    if d = 1 then 
        for elm  in elms do
            fac := Pcp(C, M);
            act := AffineActionOnCyclicPcp(fac, pcp, elm);
            act := InducedByField( act, F );
            stb := PcpOrbitStabilizer( [0,1]*One(F), fac, act, OnRight );
            # Print(stb, "\n");
            # for j in [1..Length(stb.orbit)] do 
            #     k := TransversalElement(j, stb, One(G));
            #     Print( k, Comm(elm,k), "\n");
            # od;
            stb := AddIgsToIgs(stb.stab, Igs(M));
            C   := SubgroupByIgs(G, stb);
        od;
    
    else 
        e := ListWithIdenticalEntries(d,0); Add(e,1);
        for elm  in elms do
            fac := Pcp(C, M);
            act := AffineActionByElement(fac, pcp, elm);
            act := InducedByField( act, F );
            stb := PcpOrbitStabilizer( e*One(F), fac, act, OnRight );
            # Print(stb, "\n");
            # for j in [1..Length(stb.orbit)] do 
            #     k := TransversalElement(j, stb, One(G));
            #     Print( k, Comm(elm,k), "\n");
            # od;
            stb := AddIgsToIgs(stb.stab, Igs(M));
            C   := SubgroupByIgs(G, stb);
        od;
    
    fi;

    return C;

end;

CentralizerPolyGroupSeries := function(G, elms, pcps)

    local   C,      #Centralizer of elms in G
            i,      #Bucle variable
            pcp,    #Factor on each step Gi/G(i+1)
            p,      #Order of the factor
            lin,
            GM;

    C := G;

    for i in [2..Length(pcps)] do

        pcp := pcps[i];
        p   := RelativeOrdersOfPcp( pcp )[1];

        M   := SubgroupByIgs( G, DenominatorOfPcp(pcp) );
        GM  := Pcp(G, M);
        lin := LinearActionOnCyclicPcp( GM, pcp );

        if lin = TrivialActionOnCyclicPcp( GM, pcp ) then

            Info( InfoConjugacy, 1, StringFormatted("Layer {} is central.", i) );
            
            C := CentralizerCentralFactor(G, pcp, elms, C);

        elif p > 0 then

            Info( InfoConjugacy, 1, StringFormatted("Layer {} is finite of order {}.", i, p) );

            C := CentralizerElementaryAbFactor(G, pcp, elms, C, p);

        else

            # C := CentralizerFreeAbFactor();

        fi;

        Print( List( Cgs(C), x -> ExponentsByPcp( GM, Comm(x,g) ) ), "\n" );

    od;

    return C;

end;

InstallGlobalFunction ( "CentralizerPolyGroup", function(G, elms)

    if not IsList(elms) then
        elms := [elms];
    fi;

    return CentralizerPolyGroupSeries(G, elms, PcpsOfEfaSeries( G ));

end );