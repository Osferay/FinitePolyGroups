############################################################################
## Central-Elementary Abelian Series of G                                 ##
############################################################################

InstallMethod( CeaSeries, [IsPcpGroup], function( G )

    local   ser,
            cea,
            i,
            j,
            pcp,
            relo,
            gens,
            s,
            t,
            f,
            U;

    ser  := Filtered( PcpSeries(G), N -> IsNormal(G, N) );
    cea  := [];

    for i in [1..Length(ser)-1] do
        Add( cea, ser[i] );
        j := Length( cea );

        if not IsCentralFactor( G, ser[i], ser[i+1]) then

            pcp  := Pcp( ser[i], ser[i+1] );
            relo := RelativeOrdersOfPcp( pcp );
            gens := GeneratorsOfPcp( pcp );
            
            
            s := Factors( Lcm( relo ) );
            #If the group is already a p-group we can store the factor
            if Length(s) = 1 then
                cea[j]!.ceapcp := pcp;
                cea[j]!.ceacentralfactor := false;
            #If is not a p-group, refine the pcp    
            else
                f := ShallowCopy( gens );
                for t in [1..Length(s)-1] do
                    f := List( f, x -> x ^ s[t] );
                    f := AddToIgs( Igs( ser[i+1] ), f );
                    U := SubgroupByIgs( G, f );
                    Add( cea, U );

                    #If is central stop refining
                    if IsCentralFactor( G, U, ser[i+1]) then
                        cea[j+t]!.ceacentralfactor := true;
                        break;
                    fi;
                od;
            fi;
            
        else 
            cea[j]!.ceacentralfactor := true;
        fi;
    od;

    Add( cea, Subgroup( G, [] ) );

    return cea;

end );

InstallMethod( PcpsOfCeaSeries, [IsPcpGroup], function(G)

    local   pcps,
            pcp,
            ser,
            i;

    pcps := [];
    ser  := CeaSeries(G);

    for i in [1..Length(ser)-1] do

        if IsBound( ser[i]!.ceapcp ) then
            pcp := ser[i]!.ceapcp;
        
        else
            pcp := Pcp( ser[i], ser[i+1] );
        fi;

        if IsBound( ser[i]!.ceacentralfactor ) then
            pcp!.ceacentralfactor := ser[i]!.ceacentralfactor;
        
        else 
            pcp!.ceacentralfactor := IsCentralFactor(G, ser[i], ser[i+1]);
        fi;
        Add( pcps, pcp); 
    
    od;

    return pcps;

end );