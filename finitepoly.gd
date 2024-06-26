### info

DeclareInfoClass( "InfoPcToPcpGroup" );
DeclareInfoClass( "InfoConjugacy" );

### general.gi

DeclareGlobalFunction( "ConjugacyOrder" );
DeclareGlobalFunction( "Sifting" );
DeclareGlobalFunction( "ExponentCyclicPcpFactor");

### series.gi

DeclareAttribute( "CeaSeries", IsPcpGroup );
DeclareAttribute( "PcpsOfCeaSeries", IsPcpGroup );

### conjugacy.gi

DeclareGlobalFunction( "CentralizerFinitePoly" );
DeclareGlobalFunction( "IsConjugateFinitePoly" );

### exam.gi

DeclareGlobalFunction( "FromPcGroupToPcpGroup" );