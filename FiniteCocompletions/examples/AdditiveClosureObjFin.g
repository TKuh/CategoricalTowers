#! @BeginChunk AddClosureObjFinConstruction

#! @Example
LoadPackage( "FiniteCocompletions", false );
#! true
LoadPackage( "FunctorCategories", false );
#! true
q := FinQuiver( "q(a,b,c,d)[]" );
#! FinQuiver( "q(a,b,c,d)[]" )
P := PathCategory( q );
#! PathCategory( FinQuiver( "q(a,b,c,d)[]" ) )
Q := HomalgFieldOfRationals( );
#! Q
L := Q[P];
#! Q-LinearClosure( PathCategory( FinQuiver( "q(a,b,c,d)[]" ) ) )
A := AdditiveClosureOfObjectFiniteCategory( L );;
source := ObjectConstructor( A, [3,[2,1,0,0]] );;
target := ObjectConstructor( A, [2,[0,1,1,0]] );;
id_b := IdentityMorphism( P.b ) / L;;
zero_ab := ZeroMorphism( L, P.a / L, P.b / L );;
zero_ac := ZeroMorphism( L, P.a / L, P.c / L );;
zero_bc := ZeroMorphism( L, P.b / L, P.c / L );;
matrix := [ [ zero_ab, zero_ac ], [ zero_ab, zero_ac ], [ id_b, zero_bc] ];;
m := MorphismConstructor( A, source, matrix, target );;
IsWellDefinedForMorphisms( m );
#! true
#! @EndExample
#! @EndChunk

