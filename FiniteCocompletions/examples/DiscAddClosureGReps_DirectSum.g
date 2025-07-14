#! @BeginChunk DisconnectedAddClosureGRepsDirectSum

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
A := AdditiveClosureOfObjectFiniteDisconnectedCategoryGReps( L );;
a := ObjectConstructor( A, [ [ 1, L.a ], [ 0, L.b ] ] );;
b := ObjectConstructor( A, [ [ 0, L.a ], [ 1, L.b ] ] );;

ModelingObject( A, a );;

# diag := [ a, b, b ];;
# pr1 := ProjectionInFactorOfDirectSum( diag, 1 );;
# pr2 := ProjectionInFactorOfDirectSum( diag, 2 );;
# pr3 := ProjectionInFactorOfDirectSum( diag, 3 );;
# u := UniversalMorphismIntoDirectSum( [ pr1, pr2, pr3 ] );;
# IsOne( u );;
#! @EndExample
#! @EndChunk
