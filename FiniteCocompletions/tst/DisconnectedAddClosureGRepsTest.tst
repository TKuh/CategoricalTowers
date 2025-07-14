gap> START_TEST("DisconnectedAddClosureGRepsTest.tst");

gap> LoadPackage( "FiniteCocompletions", false );
true
gap> LoadPackage( "FunctorCategories", false );
true
gap> q := FinQuiver( "q(a,b,c)[aa:a->a,bb:b->b,cc:c->c]" );;
gap> P := PathCategory( q );;
gap> Q := HomalgFieldOfRationals( );;
gap> L := Q[P];;
gap> DAC_GReps := AdditiveClosureOfObjectFiniteDisconnectedCategoryGReps( L );;
gap> DAC := ModelingCategory( DAC_GReps );;
gap> a := L.a;;
gap> b := L.b;;
gap> c := L.c;;
gap> aa := L.aa;;
gap> bb := L.bb;;
gap> cc := L.cc;;
gap> id_a := IdentityMorphism( L, a );;
gap> id_b := IdentityMorphism( L, b );;
gap> #########################################
> # Objects
> #########################################
> 
> a1_reinterp := ObjectConstructor( DAC_GReps, [ [ 2, a ], [ 2, b ], [ 1, c ] ] );
<An object in AdditiveClosureOfObjectFiniteDisconnectedCategoryGReps( Q-LinearClosure( PathCategory( FinQuiver( "q(a,b,c)[aa:a-≻a,bb:b-≻b,cc:c-≻c]" ) ) ) ) defined by 5 underlying objects>
gap> Display( a1_reinterp );
A formal direct sum consisting of 5 objects:

2 times: (a)
2 times: (b)
1 times: (c)
gap> a2_reinterp := ObjectConstructor( DAC_GReps, [ [ 1, a ], [ 1, b ] ] );;
gap> Display( a2_reinterp );
A formal direct sum consisting of 2 objects:

1 times: (a)
1 times: (b)
0 times: (c)
gap> a1_model := ModelingObject( DAC_GReps, a1_reinterp );;
gap> a2_model := ModelingObject( DAC_GReps, a2_reinterp );;
gap> a1_reinterp = ReinterpretationOfObject( DAC_GReps, a1_model );
true
gap> a2_reinterp = ReinterpretationOfObject( DAC_GReps, a2_model );
true
gap> a1_model := ObjectConstructor( DAC, [ 5, [ 2, 2, 1 ] ] );;
gap> a2_model := ObjectConstructor( DAC, [ 2, [ 1, 1, 0 ] ] );;
gap> a1_model = ModelingObject( DAC_GReps, a1_reinterp );
true
gap> a2_model = ModelingObject( DAC_GReps, a2_reinterp );
true
gap> #########################################
> # Morphisms
> #########################################
> 
> matrix_a := [ [ aa ], [ id_a ] ];;
gap> matrix_b := [ [ bb ], [ id_b ] ];;
gap> matrix_c := [ [] ];;
gap> matrix := [ matrix_a, matrix_b, matrix_c ];;
gap> mor_reinterp := MorphismConstructor( DAC_GReps, a1_reinterp, matrix, a2_reinterp );
<A morphism in AdditiveClosureOfObjectFiniteDisconnectedCategoryGReps( Q-LinearClosure( PathCategory( FinQuiver( "q(a,b,c)[aa:a-≻a,bb:b-≻b,cc:c-≻c]" ) ) ) ) defined by a list of 3 matrices of underlying morphisms>
gap> Display( mor_reinterp );
A 2 x 1 matrix with entries in Q-LinearClosure( PathCategory( FinQuiver( "q(a,b,c)[aa:a-≻a,bb:b-≻b,cc:c-≻c]" ) ) )

[1,1]: 1*aa:(a) -≻ (a)
[2,1]: 1*id(a):(a) -≻ (a)

A 2 x 1 matrix with entries in Q-LinearClosure( PathCategory( FinQuiver( "q(a,b,c)[aa:a-≻a,bb:b-≻b,cc:c-≻c]" ) ) )

[1,1]: 1*bb:(b) -≻ (b)
[2,1]: 1*id(b):(b) -≻ (b)

A 1 x 0 matrix with entries in Q-LinearClosure( PathCategory( FinQuiver( "q(a,b,c)[aa:a-≻a,bb:b-≻b,cc:c-≻c]" ) ) )

gap> IsWellDefinedForMorphisms( mor_reinterp );
true
gap> mor_model := ModelingMorphism( DAC_GReps, mor_reinterp );;
gap> mor_reinterp = ReinterpretationOfMorphism( DAC_GReps, Source( mor_reinterp ), mor_model, Target( mor_reinterp ) );
true
gap> mor_model := ModelingTowerMorphismConstructor( DAC_GReps, a1_model, matrix, a2_model );;
gap> mor_reinterp := ReinterpretationOfMorphism( DAC_GReps, a1_reinterp, mor_model, a2_reinterp );;
gap> IsWellDefinedForMorphisms( mor_reinterp );
true
gap> mor_model = ModelingMorphism( DAC_GReps, mor_reinterp );
true
gap> IsWellDefinedForMorphisms( mor_model );
true
gap> #########################################
> # Attributes and Operators
> #########################################
> 
> UnderlyingObjectList( a1_reinterp );
[ (a), (a), (b), (b), (c) ]
gap> a1_reinterp[4];
(b)
gap> mor_reinterp[2];
[ [ 1*bb:(b) -≻ (b) ], [ 1*id(b):(b) -≻ (b) ] ]
gap> L.a / DAC_GReps;;
gap> id_a / DAC_GReps;;
gap> [ L.a, L.b, L.a ] / DAC_GReps;;
gap> [ matrix_a, matrix_b, matrix_c ] / DAC_GReps;;
gap> Support( Source( id_a ) );
[ [ (a) ] ]

#
gap> STOP_TEST("DisconnectedAddClosureGRepsTest.tst", 1);
