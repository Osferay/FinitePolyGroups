RelsToString := function( rels )

    local   i,
            str;

    str := "";
    for i in [1..Length(rels)/2] do
        if i <> Length(rels)/2 then
            str := Concatenation(str, StringFormatted( "G.{}^{}*", rels[2*i-1], rels[2*i] ) );
        else
            str := Concatenation(str, StringFormatted( "G.{}^{}", rels[2*i-1], rels[2*i] ) );
        fi;
    od;

    return str;
end;

ExponentToString := function( exps )

    local   i,
            str;

    str := "";
    for i in [1..Length(exps)] do
        if exps[i] <> 0 then
            str := Concatenation(str, StringFormatted( "G.{}^{}*", i, exps[i] ) );
        fi;
    od;

    return str{[1..Length(str)-1]};
end;

IsConfluentDebug := function( coll )
    local   n,  k,  j,  i,  ev1,  w,  ev2, dbg;

    n := coll![ PC_NUMBER_OF_GENERATORS ];

    # k (j i) = (k j) i
    for k in [n,n-1..1] do
        for j in [k-1,k-2..1] do
            for i in [j-1,j-2..1] do
                InfoConsistency( "checking ", k, " ", j, " ", i, "\n" );
                ev1 := ListWithIdenticalEntries( n, 0 );
                CollectWordOrFail( coll, ev1, [j,1,i,1] );
                w := ObjByExponents( coll, ev1 );
                ev1 := ExponentsByObj( coll, [k,1] );
                CollectWordOrFail( coll, ev1, w );

                ev2 := ListWithIdenticalEntries( n, 0 );
                CollectWordOrFail( coll, ev2, [k,1,j,1,i,1] );

                if ev1 <> ev2 then
                    dbg := StringFormatted( "Inconsistency at G.{1}*(G.{2}*G.{3})=(G.{1}*G.{2})*G.{3}\n", k, j, i );
                    dbg := Concatenation( dbg, StringFormatted( "The left side of the equation gives {}\n", ExponentToString(ev1) ) );
                    dbg := Concatenation( dbg, StringFormatted( "The right side of the equation gives {}\n", ExponentToString(ev2) ) );
                    Error( dbg );
                    return false;
                fi;
            od;
        od;
    od;

    # j^m i = j^(m-1) (j i)
    for j in [n,n-1..1] do
        for i in [j-1,j-2..1] do
            if IsBound(coll![ PC_EXPONENTS ][j]) then
                InfoConsistency( "checking ", j, "^m ", i, "\n" );
                ev1 := ListWithIdenticalEntries( n, 0 );
                CollectWordOrFail( coll, ev1, [j, coll![ PC_EXPONENTS ][j]-1,
                                               j, 1, i,1] );

                ev2 := ListWithIdenticalEntries( n, 0 );
                CollectWordOrFail( coll, ev2, [j,1,i,1] );
                w := ObjByExponents( coll, ev2 );
                ev2 := ExponentsByObj( coll, [j,coll![ PC_EXPONENTS ][j]-1] );
                CollectWordOrFail( coll, ev2, w );

                if ev1 <> ev2 then
                    w := ListWithIdenticalEntries( n, 0 );
                    CollectWordOrFail( coll, w, [j, coll![ PC_EXPONENTS ][j] ]);
                    dbg := StringFormatted( "Inconsistency at G.{1}^{2}*G.{3}=G.{1}^({2}-1)*(G.{1}*G.{3})\n", j, coll![ PC_EXPONENTS ][j], i);
                    dbg := Concatenation( dbg, StringFormatted( "The left side of the equation gives {}\n", ExponentToString(ev2) ) );
                    dbg := Concatenation( dbg, StringFormatted( "The right side of the equation gives {}\n", ExponentToString(ev1) ) );
                    dbg := Concatenation( dbg, StringFormatted( "The exponent relation gives {}\n", ExponentToString(w) ) );
                    Error( dbg );
                fi;
            fi;
        od;
    od;

    # j * i^m = (j i) * i^(m-1)
    for i in [n,n-1..1] do
        if IsBound(coll![ PC_EXPONENTS ][i]) then
            for j in [n,n-1..i+1] do
                InfoConsistency( "checking ", j, " ", i, "^m\n" );
                ev1 := ExponentsByObj( coll, [j,1] );
                if IsBound( coll![ PC_POWERS ][i] ) then
                    CollectWordOrFail( coll, ev1, coll![ PC_POWERS ][i] );
                fi;

                ev2 := ListWithIdenticalEntries( n, 0 );
                CollectWordOrFail( coll, ev2,
                        [ j,1,i,coll![ PC_EXPONENTS ][i] ] );

                if ev1 <> ev2 then
                    w := ListWithIdenticalEntries( n, 0 );
                    CollectWordOrFail( coll, w, [i, coll![ PC_EXPONENTS ][i] ]);
                    dbg := StringFormatted( "Inconsistency at G.{1}*G.{2}^{3}=(G.{1}*G.{2})*G.{2}^({3}-1)\n", j, i, coll![ PC_EXPONENTS ][i] );
                    dbg := Concatenation( dbg, StringFormatted( "The left side of the equation gives {}\n", ExponentToString(ev1) ) );
                    dbg := Concatenation( dbg, StringFormatted( "The right side of the equation gives {}\n", ExponentToString(ev2) ) );
                    dbg := Concatenation( dbg, StringFormatted( "The exponent relation gives {}\n", ExponentToString(w) ) );
                    Error( dbg );
                fi;
            od;
        fi;
    od;

    # i^m i = i i^m
    for i in [n,n-1..1] do
        if IsBound( coll![ PC_EXPONENTS ][i] ) then
            ev1 := ListWithIdenticalEntries( n, 0 );
            CollectWordOrFail( coll, ev1, [ i,coll![ PC_EXPONENTS ][i]+1 ] );

            ev2 := ExponentsByObj( coll, [i,1] );
            if IsBound( coll![ PC_POWERS ][i] ) then
                CollectWordOrFail( coll, ev2, coll![ PC_POWERS ][i] );
            fi;

            if ev1 <> ev2 then
                w := ListWithIdenticalEntries( n, 0 );
                CollectWordOrFail( coll, w, [i, coll![ PC_EXPONENTS ][i] ]);
                dbg := StringFormatted( "Inconsistency at G.{1}^{2}*G.1=G.{1}*G.{1}^{2}\n", i, coll![ PC_EXPONENTS ][i] );
                dbg := Concatenation( dbg, StringFormatted( "The left side of the equation gives {}\n", ExponentToString(ev1) ) );
                dbg := Concatenation( dbg, StringFormatted( "The right side of the equation gives {}\n", ExponentToString(ev2) ) );
                dbg := Concatenation( dbg, StringFormatted( "The exponent relation gives {}\n", ExponentToString(w) ) );
                Error( dbg );
            fi;
        fi;
    od;

    # j = (j -i) i
    for i in [n,n-1..1] do
        if not IsBound( coll![ PC_EXPONENTS ][i] ) then
            for j in [i+1..n] do
                InfoConsistency( "checking ", j, " ", -i, " ", i, "\n" );
                ev1 := ListWithIdenticalEntries( n, 0 );
                CollectWordOrFail( coll, ev1, [j,1,i,-1,i,1] );
                ev1[j] := ev1[j] - 1;

                if ev1 <> ListWithIdenticalEntries( n, 0 ) then
                    w := ListWithIdenticalEntries( n, 0 );
                    CollectWordOrFail( coll, w, [j,1,i,-1,i,1] );
                    dbg := StringFormatted( "Inconsistency at G.{1}=(G.{1}*G.{2}^-1)*G.{2}\n", j, i );
                    dbg := Concatenation( dbg, StringFormatted( "The right side of the equation gives {}\n", ExponentToString(w) ) );
                    Error( dbg );
                fi;
            od;
        fi;
    od;

    # i = -j (j i)
    for j in [n,n-1..1] do
        if not IsBound( coll![ PC_EXPONENTS ][j] ) then
            for i in [j-1,j-2..1] do
                InfoConsistency( "checking ", -j, " ", j, " ", i, "\n" );
                ev1 := ListWithIdenticalEntries( n, 0 );
                CollectWordOrFail( coll, ev1, [ j,1,i,1 ] );
                w := ObjByExponents( coll, ev1 );
                ev1 := ExponentsByObj( coll, [j,-1] );
                CollectWordOrFail( coll, ev1, w );

                if ev1 <> ExponentsByObj( coll, [i,1] ) then
                    w := ListWithIdenticalEntries( n, 0 );
                    CollectWordOrFail( coll, w, [j,1,i,-1,i,1] );
                    dbg := StringFormatted( "Inconsistency at G.{1}=G.{2}^-1*(G.{2}*G.{1})\n", i, j );
                    dbg := Concatenation( dbg, StringFormatted( "The right side of the equation gives {}\n", ExponentToString(ev1) ) );
                    Error( dbg );
                fi;

                # -i = -j (j -i)
                if not IsBound( coll![ PC_EXPONENTS ][i] ) then
                    InfoConsistency( "checking ", -j, " ", j, " ", -i, "\n" );
                    ev1 := ListWithIdenticalEntries( n, 0 );
                    CollectWordOrFail( coll, ev1, [ j,1,i,-1 ] );
                    w := ObjByExponents( coll, ev1 );
                    ev1 := ExponentsByObj( coll, [j,-1] );
                    CollectWordOrFail( coll, ev1, w );

                    if ExponentsByObj( coll, [i,-1] ) <> ev1 then
                        w := ListWithIdenticalEntries( n, 0 );
                        CollectWordOrFail( coll, w, [j,1,i,-1,i,1] );
                        dbg := StringFormatted( "Inconsistency at G.{1}^-1=G.{2}^-1*(G.{2}*G.{1}^-1)\n", i, j );
                        dbg := Concatenation( dbg, StringFormatted( "The right side of the equation gives {}\n", ExponentToString(ev1) ) );
                        Error( dbg );
                    fi;
                fi;
            od;
        fi;
    od;

    return true;
end;

FromPcGroupToPcpGroup := function(G)

    local   gen,
            ftl,
            rel,
            i,j,k,
            pow,
            conj,
            d,
            l,
            grp,
            info;

    if not IsPcGroup(G) then
        Error( " G is not a pc-group." );
    fi;

    gen := Pcgs(G);
    rel := RelativeOrders( gen );
    
    ftl := FromTheLeftCollector( Length(gen) );

    for i in [1..Length(gen)] do

        pow := gen[i]^rel[i];
        d := DepthOfPcElement(gen, pow);
        SetRelativeOrder( ftl, i, rel[i] );
        
        #Power relations
        if d <> Length(gen)+1 then
            l := [];
            for k in [d..Length(gen)] do
                if ExponentOfPcElement(gen, pow, k) <> 0 then
                    Add(l, k);
                    Add(l, ExponentOfPcElement(gen, pow, k));
                fi;
            od;
            info := StringFormatted( "Power relation G.{}^{}={}", i , rel[i], RelsToString(l) );
            Info( InfoPcToPcpGroup, 1, info );
            SetPower( ftl, i, l);

        else
            info := StringFormatted( "Relative order G.{}^{}", i , rel[i] );
            Info( InfoPcToPcpGroup, 1, info );

        fi;

        #Conugation relations
        for j in [1..i-1] do
            conj := gen[i] ^ gen[j];

            if conj <> gen[i] then
                d := DepthOfPcElement(gen, conj);
                l := [];

                for k in [d..Length(gen)] do
                    if ExponentOfPcElement(gen, conj, k) <> 0 then
                        Add(l, k);
                        Add(l, ExponentOfPcElement(gen, conj, k));
                    fi;
                od;
                
                info := StringFormatted( "Conjugate relation G.{}^G.{} = {}", i , j , RelsToString(l) );
                Info( InfoPcToPcpGroup, 1, info );
                SetConjugate( ftl, i, j, l );   
            fi;
            
        od;
    od;

    UpdatePolycyclicCollector(ftl);
    IsConfluentDebug(ftl);
    grp := PcpGroupByCollectorNC( ftl );
    
    if IsBool(grp) then
        Error( "no group generated" );
    else
        return grp;
    fi;

end ;

SomePolyFiniteGroups := function( n )

    local   ftl,    #From the left collector
            H;      #Pc- group

    if n = 1 then 
        #D_4 sd S_3 sd_4 C2, order 414
        H := SmallGroup(414,9);
        return FromPcGroupToPcpGroup(H);
    
    elif n = 2 then
        #(D_5 x A_4) x F_5, order 8640
        H := DirectProduct( SmallGroup(120,39), SmallGroup(72,39));
        return FromPcGroupToPcpGroup(H);

    elif n = 3 then
        #(C_3 sd D_69) x (D_4 sd S_3 sd_4 C2), order 39744
        H := DirectProduct( SmallGroup(96,123), SmallGroup(414,9));
        return FromPcGroupToPcpGroup(H);

    elif n = 4 then 
        #D_181 x F_19, order 123804
        H := DirectProduct( SmallGroup(362,2), SmallGroup(342,7));
        return FromPcGroupToPcpGroup(H);
    
    else
        return fail;
    fi;
end;