LinearActionOnCyclicPcp := function(G, A)
    local act;

    act := List( G, x -> List( A, y -> ExponentCyclicPcpFactor( A, y ^ x ) ) );

    return act;
end;

TrivialActionOnCyclicPcp := function(G, A)
    local act;

    act := List( G, x -> List( A, y -> ExponentCyclicPcpFactor( A, y ) ) );

    return act;
end;

AffineActionOnCyclicPcp := function(G, A, g )

    local   act,
            i,j,
            c;

    act := LinearActionOnCyclicPcp(G, A);
    for i in [1..Length(G)] do 

        for j in [1..Length(act[i])] do
            Add( act[i][j], 0 );
        od;

        c := ExponentCyclicPcpFactor( A, Comm( g, G[i] ));
        Add( c, 1 );
        Add( act[i], c);
    od;

    return act;
end;