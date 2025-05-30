#! @BeginChunk DiscAddClosureDirectSum

#! @Example
LoadPackage( "FiniteCocompletions", false );
#! true
LoadPackage( "FunctorCategories", false );
#! true
q := FinQuiver( "q(a,b)[]" );
#! FinQuiver( "q(a,b)[]" )
P := PathCategory( q );
#! PathCategory( FinQuiver( "q(a,b)[]" ) )
Q := HomalgFieldOfRationals( );
#! Q
L := Q[P];
#! Q-LinearClosure( PathCategory( FinQuiver( "q(a,b)[]" ) ) )
A := DisconnectedAdditiveClosure( L );;
a := ObjectConstructor( A, [1,[1,0]] );;
b := ObjectConstructor( A, [1,[0,1]] );;
diag := [ b, a, b ];;
pr1 := ProjectionInFactorOfDirectSum( diag, 1 );;
pr2 := ProjectionInFactorOfDirectSum( diag, 2 );;
pr3 := ProjectionInFactorOfDirectSum( diag, 3 );;
u := UniversalMorphismIntoDirectSum( [ pr1, pr2, pr3 ] );;
IsOne( u );
#! true
#! @EndExample
#! @EndChunk
