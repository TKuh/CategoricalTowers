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
A := AdditiveClosureOfObjectFiniteDisconnectedCategory( L );;
source := ObjectConstructor( A, [ 3, [ 2, 1, 0, 0 ] ] );;
Display( source );
#! A formal direct sum consisting of 3 objects:
#! 
#! 2 times: (a)
#! 1 times: (b)
#! 0 times: (c)
#! 0 times: (d)
target := ObjectConstructor( A, [ 2, [ 0, 1, 1, 0 ] ] );;
Display( target );
#! A formal direct sum consisting of 2 objects:
#! 
#! 0 times: (a)
#! 1 times: (b)
#! 1 times: (c)
#! 0 times: (d)
id_b := IdentityMorphism( P.b ) / L;;
matrix := [ [ [], [] ], [ [ id_b ] ], [ ], [ ] ];;
m := MorphismConstructor( A, source, matrix, target );;
Display( m );
#! A 2 x 0 matrix with entries in Q-LinearClosure( PathCategory( FinQuiver( "q(a,b,c,d)[]" ) ) )
#! 
#! A 1 x 1 matrix with entries in Q-LinearClosure( PathCategory( FinQuiver( "q(a,b,c,d)[]" ) ) )
#! 
#! [1,1]: 1*id(b):(b) -≻ (b)
#! 
#! A 0 x 1 matrix with entries in Q-LinearClosure( PathCategory( FinQuiver( "q(a,b,c,d)[]" ) ) )
#! 
#! A 0 x 0 matrix with entries in Q-LinearClosure( PathCategory( FinQuiver( "q(a,b,c,d)[]" ) ) )
#! 
#! @EndExample
#! @EndChunk

