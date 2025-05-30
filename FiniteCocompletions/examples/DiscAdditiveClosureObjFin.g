#! @BeginChunk DisconnectedAddClosureConstruction

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
A := DisconnectedAdditiveClosure( L );;
source := ObjectConstructor( A, [4,[2,1,1,0]] );;
target := ObjectConstructor( A, [3,[1,0,2,0]] );;
id_a := IdentityMorphism( P.a ) / L;;
id_c := IdentityMorphism( P.c ) / L;;
list_of_matrices := [ [[ id_a ], [ id_a ]], [[ ]], [[ id_c, id_c ]], [ ] ];;
m := MorphismConstructor( A, source, list_of_matrices, target );;
IsWellDefinedForMorphisms( m );
#! true
#! @EndExample
#! @EndChunk

