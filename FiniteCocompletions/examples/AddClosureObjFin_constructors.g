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
source := AdditiveClosureObject( A, [3,[2,1,0,0]] );;
source = [ L.a, L.b, L.a ] / A;
#! true
Display( source );
#! A formal direct sum consisting of 3 objects:
#! 
#! 2 times: (a)
#! 1 times: (b)
#! 0 times: (c)
#! 0 times: (d)
target := AdditiveClosureObject( A, [2,[0,1,1,0]] );;
Display( target );
#! A formal direct sum consisting of 2 objects:
#! 
#! 0 times: (a)
#! 1 times: (b)
#! 1 times: (c)
#! 0 times: (d)
id_b := IdentityMorphism( P.b ) / L;;
zero_ab := ZeroMorphism( L, P.a / L, P.b / L );;
zero_ac := ZeroMorphism( L, P.a / L, P.c / L );;
zero_bc := ZeroMorphism( L, P.b / L, P.c / L );;
matrix := [ [ zero_ab, zero_ac ], [ zero_ab, zero_ac ], [ id_b, zero_bc] ];;
m := AdditiveClosureMorphism( A, source, matrix, target );;
m = matrix / A;
#! true
Display( m );
#! A 3 x 2 matrix with entries in Q-LinearClosure( PathCategory( FinQuiver( "q(a,b,c,d)[]" ) ) )
#! 
#! [1,1]: 0:(a) -≻ (b)
#! [1,2]: 0:(a) -≻ (c)
#! [2,1]: 0:(a) -≻ (b)
#! [2,2]: 0:(a) -≻ (c)
#! [3,1]: 1*id(b):(b) -≻ (b)
#! [3,2]: 0:(b) -≻ (c)
#! @EndExample
#! @EndChunk

