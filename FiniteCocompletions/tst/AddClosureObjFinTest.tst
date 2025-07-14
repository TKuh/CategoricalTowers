gap> START_TEST("AddClosureObjFinTest.tst");

gap> LoadPackage( "FiniteCocompletions", false );
true
gap> LoadPackage( "FunctorCategories", false );
true
gap> q := FinQuiver( "q(a,b)[]" );
FinQuiver( "q(a,b)[]" )
gap> P := PathCategory( q );
PathCategory( FinQuiver( "q(a,b)[]" ) )
gap> Q := HomalgFieldOfRationals( );
Q
gap> L := Q[P];
Q-LinearClosure( PathCategory( FinQuiver( "q(a,b)[]" ) ) )
gap> A := AdditiveClosureOfObjectFiniteCategory( L );;
gap> a := ObjectConstructor( A, [1,[1,0]] );;
gap> b := ObjectConstructor( A, [1,[0,1]] );;
gap> ObjectDatum( a );
[ 1, [ 1, 0 ] ]
gap> Display( b );
A formal direct sum consisting of 1 object:
0 times: (a)
1 times: (b)
gap> Display( ZeroObject( A ) );
A formal direct sum consisting of 0 objects:
0 times: (a)
0 times: (b)
gap> aab := AdditiveClosureObject( A, [3,[2,1]] );;
gap> aab = DirectSum( [ a, b, a ] );
true
gap> aab[1] = L.a;
true
gap> aab[2] = L.a;
true
gap> aab[3] = L.b;
true
gap> id_aab := IdentityMorphism( aab );;
gap> z := ZeroMorphism( aab, b );;
gap> MorphismDatum( z );
[ [ 0:(a) -≻ (b) ], [ 0:(a) -≻ (b) ], [ 0:(b) -≻ (b) ] ]
gap> Display( z );
A 3 x 1 matrix with entries in Q-LinearClosure( PathCategory( FinQuiver( "q(a,b)[]" ) ) )

[1,1]: 0:(a) -≻ (b)
[2,1]: 0:(a) -≻ (b)
[3,1]: 0:(b) -≻ (b)
gap> IsZeroForMorphisms( z );
true
gap> z_aab := ZeroMorphism( aab, aab );;
gap> IsEqualForMorphisms( id_aab, z_aab );
false
gap> IsEqualForMorphisms( id_aab, id_aab );
true
gap> IsCongruentForMorphisms( id_aab, z_aab );
false
gap> IsCongruentForMorphisms( id_aab, id_aab );
true
gap> PreCompose( id_aab, z_aab );
<A morphism in AdditiveClosureOfObjectFiniteCategory( Q-LinearClosure( PathCategory( FinQuiver( "q(a,b)[]" ) ) ) )
defined by a 3 x 3 matrix of underlying morphisms>
gap> Display( AdditionForMorphisms( id_aab, id_aab ) );
A 3 x 3 matrix with entries in Q-LinearClosure( PathCategory( FinQuiver( "q(a,b)[]" ) ) )

[1,1]: 2*id(a):(a) -≻ (a)
[1,2]: 0:(a) -≻ (a)
[1,3]: 0:(a) -≻ (b)
[2,1]: 0:(a) -≻ (a)
[2,2]: 2*id(a):(a) -≻ (a)
[2,3]: 0:(a) -≻ (b)
[3,1]: 0:(b) -≻ (a)
[3,2]: 0:(b) -≻ (a)
[3,3]: 2*id(b):(b) -≻ (b)
gap> Display( SumOfMorphisms( Source( id_aab ), [ id_aab, z_aab, id_aab ], Target( id_aab ) ) );
A 3 x 3 matrix with entries in Q-LinearClosure( PathCategory( FinQuiver( "q(a,b)[]" ) ) )

[1,1]: 2*id(a):(a) -≻ (a)
[1,2]: 0:(a) -≻ (a)
[1,3]: 0:(a) -≻ (b)
[2,1]: 0:(a) -≻ (a)
[2,2]: 2*id(a):(a) -≻ (a)
[2,3]: 0:(a) -≻ (b)
[3,1]: 0:(b) -≻ (a)
[3,2]: 0:(b) -≻ (a)
[3,3]: 2*id(b):(b) -≻ (b)
gap> Display( AdditiveInverseForMorphisms( id_aab ) );
A 3 x 3 matrix with entries in Q-LinearClosure( PathCategory( FinQuiver( "q(a,b)[]" ) ) )

[1,1]: -1*id(a):(a) -≻ (a)
[1,2]: 0:(a) -≻ (a)
[1,3]: 0:(a) -≻ (b)
[2,1]: 0:(a) -≻ (a)
[2,2]: -1*id(a):(a) -≻ (a)
[2,3]: 0:(a) -≻ (b)
[3,1]: 0:(b) -≻ (a)
[3,2]: 0:(b) -≻ (a)
[3,3]: -1*id(b):(b) -≻ (b)
gap> diag := [ a, a, b ];;
gap> pr1 := ProjectionInFactorOfDirectSum( diag, 1 );;
gap> pr2 := ProjectionInFactorOfDirectSum( diag, 2 );;
gap> pr3 := ProjectionInFactorOfDirectSum( diag, 3 );;
gap> u := UniversalMorphismIntoDirectSumWithGivenDirectSum( diag, [ pr1, pr2, pr3 ], aab );;
gap> IsWellDefinedForMorphisms( u );
true
gap> inj1 := InjectionOfCofactorOfDirectSum( diag, 1 );;
gap> inj2 := InjectionOfCofactorOfDirectSum( diag, 2 );;
gap> inj3 := InjectionOfCofactorOfDirectSum( diag, 3 );;
gap> u := UniversalMorphismFromDirectSumWithGivenDirectSum( diag, [ inj1, inj2, inj3 ], aab  );;
gap> IsWellDefinedForMorphisms( u );
true
gap> comp := ComponentOfMorphismIntoDirectSum( inj1, [ a, a, b ], 3 );;
gap> IsWellDefined( comp );
true
gap> Display( comp );
A 1 x 1 matrix with entries in Q-LinearClosure( PathCategory( FinQuiver( "q(a,b)[]" ) ) )

[1,1]: 0:(a) -≻ (b)
gap> comp := ComponentOfMorphismFromDirectSum( pr3, [ a, a, b ], 1 );;
gap> IsWellDefined( comp );
true
gap> Display( comp );
A 1 x 1 matrix with entries in Q-LinearClosure( PathCategory( FinQuiver( "q(a,b)[]" ) ) )

[1,1]: 0:(a) -≻ (b)
gap> Display( MultiplyWithElementOfCommutativeRingForMorphisms( 10 / Q, id_aab ) );;
A 3 x 3 matrix with entries in Q-LinearClosure( PathCategory( FinQuiver( "q(a,b)[]" ) ) )

[1,1]: 10*id(a):(a) -≻ (a)
[1,2]: 0:(a) -≻ (a)
[1,3]: 0:(a) -≻ (b)
[2,1]: 0:(a) -≻ (a)
[2,2]: 10*id(a):(a) -≻ (a)
[2,3]: 0:(a) -≻ (b)
[3,1]: 0:(b) -≻ (a)
[3,2]: 0:(b) -≻ (a)
[3,3]: 10*id(b):(b) -≻ (b)
gap> L.a / A;;
gap> IdentityMorphism( L.a ) / A;;
gap> [ L.a, L.b, L.a ] / A;;

#
gap> STOP_TEST("AddClosureObjFinTest.tst", 1);
