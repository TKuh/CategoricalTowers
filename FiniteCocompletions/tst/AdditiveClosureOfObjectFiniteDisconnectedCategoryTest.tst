
gap> START_TEST("AdditiveClosureOfObjectFiniteDisconnectedCategoryTest");

gap> LoadPackage( "FiniteCocompletions", false );
true
gap> LoadPackage( "FunctorCategories", false );
true
gap> q := FinQuiver( "q(a,b,c)[aa:a->a,bb:b->b,cc:c->c]" );;
gap> P := PathCategory( q );;
gap> Q := HomalgFieldOfRationals( );;
gap> L := Q[P];;
gap> DAC := AdditiveClosureOfObjectFiniteDisconnectedCategory( L );;
gap> AC := ModelingCategory( DAC );;
gap> a := P.a / L;;
gap> b := P.b / L;;
gap> c := P.c / L;;
gap> aa := P.aa / L;;
gap> bb := P.bb / L;;
gap> cc := P.cc / L;;
gap> id_a := IdentityMorphism( L, a );;
gap> id_b := IdentityMorphism( L, b );;
gap> #########################################
> # Objects
> #########################################
> 
> a1_reinterp := ObjectConstructor( DAC, [ 5, [ 2, 2, 1 ] ] );
<An object in AdditiveClosureOfObjectFiniteDisconnectedCategory( Q-LinearClosure( PathCategory( FinQuiver( "q(a,b,c)[aa:a-≻a,bb:b-≻b,cc:c-≻c]" ) ) ) ) defined by 5 underlying objects>
gap> Display( a1_reinterp );
A formal direct sum consisting of 5 objects:

2 times: (a)
2 times: (b)
1 times: (c)
gap> a2_reinterp := ObjectConstructor( DAC, [ 2, [ 1, 1, 0 ] ] );;
gap> Display( a2_reinterp );
A formal direct sum consisting of 2 objects:

1 times: (a)
1 times: (b)
0 times: (c)
gap> a1_model := ModelingObject( DAC, a1_reinterp );;
gap> a2_model := ModelingObject( DAC, a2_reinterp );;
gap> a1_reinterp = ReinterpretationOfObject( DAC, a1_model );
true
gap> a2_reinterp = ReinterpretationOfObject( DAC, a2_model );
true
gap> a1_model := ObjectConstructor( AC, [ 5, [ 2, 2, 1 ] ] );;
gap> a2_model := ObjectConstructor( AC, [ 2, [ 1, 1, 0 ] ] );;
gap> a1_model = ModelingObject( DAC, a1_reinterp );
true
gap> a2_model = ModelingObject( DAC, a2_reinterp );
true
gap> #########################################
> # Morphisms
> #########################################
> 
> matrix_a := [ [ aa ], [ id_a ] ];;
gap> matrix_b := [ [ bb ], [ id_b ] ];;
gap> matrix_c := [ [] ];;
gap> matrix := [ matrix_a, matrix_b, matrix_c ];;
gap> mor_reinterp := MorphismConstructor( DAC, a1_reinterp, matrix, a2_reinterp );
<A morphism in AdditiveClosureOfObjectFiniteDisconnectedCategory( Q-LinearClosure( PathCategory( FinQuiver( "q(a,b,c)[aa:a-≻a,bb:b-≻b,cc:c-≻c]" ) ) ) ) defined by a list of 3 matrices of underlying morphisms>
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
gap> mor_model := ModelingMorphism( DAC, mor_reinterp );;
gap> mor_reinterp = ReinterpretationOfMorphism( DAC, Source( mor_reinterp ), mor_model, Target( mor_reinterp ) );
true
gap> mor_model := ModelingTowerMorphismConstructor( DAC, a1_model, matrix, a2_model );;
gap> mor_reinterp := ReinterpretationOfMorphism( DAC, a1_reinterp, mor_model, a2_reinterp );;
gap> IsWellDefinedForMorphisms( mor_reinterp );
true
gap> mor_model = ModelingMorphism( DAC, mor_reinterp );
true
gap> IsWellDefinedForMorphisms( mor_model );
true
gap> ##################################################################################
> # Check some corner cases
> ##################################################################################
> 
> zero := ObjectConstructor( DAC, [0,[0,0,0]] );
<An object in AdditiveClosureOfObjectFiniteDisconnectedCategory( Q-LinearClosure( PathCategory( FinQuiver( "q(a,b,c)[aa:a-≻a,bb:b-≻b,cc:c-≻c]" ) ) ) ) defined by 0 underlying objects>
gap> list_of_matrices := [ [], [], [] ];;
gap> zero_mor := MorphismConstructor( DAC, zero, list_of_matrices, zero );
<A morphism in AdditiveClosureOfObjectFiniteDisconnectedCategory( Q-LinearClosure( PathCategory( FinQuiver( "q(a,b,c)[aa:a-≻a,bb:b-≻b,cc:c-≻c]" ) ) ) ) defined by a list of 3 matrices of underlying morphisms>
gap> IsWellDefined( zero_mor );
true
gap> zero_mor_model := ModelingMorphism( DAC, zero_mor );
<A morphism in AdditiveClosureOfObjectFiniteCategory( Q-LinearClosure( PathCategory( FinQuiver( "q(a,b,c)[aa:a-≻a,bb:b-≻b,cc:c-≻c]" ) ) ) ) defined by a 0 x 0 matrix of underlying morphisms>
gap> IsEmpty( MorphismMatrix( zero_mor_model ) );
true
gap> zero_mor = ZeroMorphism( DAC, zero, zero );
true
gap> zero_mor_reinterp := ReinterpretationOfMorphism( DAC, zero, zero_mor_model, zero );
<A morphism in AdditiveClosureOfObjectFiniteDisconnectedCategory( Q-LinearClosure( PathCategory( FinQuiver( "q(a,b,c)[aa:a-≻a,bb:b-≻b,cc:c-≻c]" ) ) ) ) defined by a list of 3 matrices of underlying morphisms>
gap> list_of_matrices = ListOfMatrices( zero_mor_reinterp );
true
gap> source := ObjectConstructor( DAC, [2,[0,2,0]] );
<An object in AdditiveClosureOfObjectFiniteDisconnectedCategory( Q-LinearClosure( PathCategory( FinQuiver( "q(a,b,c)[aa:a-≻a,bb:b-≻b,cc:c-≻c]" ) ) ) ) defined by 2 underlying objects>
gap> list_of_matrices := [ [], [ [], [] ], [] ];;
gap> mor := MorphismConstructor( DAC, source, list_of_matrices, zero );
<A morphism in AdditiveClosureOfObjectFiniteDisconnectedCategory( Q-LinearClosure( PathCategory( FinQuiver( "q(a,b,c)[aa:a-≻a,bb:b-≻b,cc:c-≻c]" ) ) ) ) defined by a list of 3 matrices of underlying morphisms>
gap> IsWellDefinedForMorphisms( mor );
true
gap> mor_model := ModelingMorphism( DAC, mor );
<A morphism in AdditiveClosureOfObjectFiniteCategory( Q-LinearClosure( PathCategory( FinQuiver( "q(a,b,c)[aa:a-≻a,bb:b-≻b,cc:c-≻c]" ) ) ) ) defined by a 2 x 0 matrix of underlying morphisms>
gap> MorphismMatrix( mor_model ) = [ [], [] ];
true
gap> mor_reinterp := ReinterpretationOfMorphism( DAC, source, mor_model, zero );
<A morphism in AdditiveClosureOfObjectFiniteDisconnectedCategory( Q-LinearClosure( PathCategory( FinQuiver( "q(a,b,c)[aa:a-≻a,bb:b-≻b,cc:c-≻c]" ) ) ) ) defined by a list of 3 matrices of underlying morphisms>
gap> list_of_matrices = ListOfMatrices( mor_reinterp );
true
gap> target := ObjectConstructor( DAC, [2,[0,2,0]] );
<An object in AdditiveClosureOfObjectFiniteDisconnectedCategory( Q-LinearClosure( PathCategory( FinQuiver( "q(a,b,c)[aa:a-≻a,bb:b-≻b,cc:c-≻c]" ) ) ) ) defined by 2 underlying objects>
gap> list_of_matrices := [ [], [], [] ];;
gap> mor := MorphismConstructor( DAC, zero, list_of_matrices, target );
<A morphism in AdditiveClosureOfObjectFiniteDisconnectedCategory( Q-LinearClosure( PathCategory( FinQuiver( "q(a,b,c)[aa:a-≻a,bb:b-≻b,cc:c-≻c]" ) ) ) ) defined by a list of 3 matrices of underlying morphisms>
gap> IsWellDefinedForMorphisms( mor );
true
gap> mor_model := ModelingMorphism( DAC, mor );
<A morphism in AdditiveClosureOfObjectFiniteCategory( Q-LinearClosure( PathCategory( FinQuiver( "q(a,b,c)[aa:a-≻a,bb:b-≻b,cc:c-≻c]" ) ) ) ) defined by a 0 x 2 matrix of underlying morphisms>
gap> MorphismMatrix( mor_model ) = [ ];
true
gap> mor_reinterp := ReinterpretationOfMorphism( DAC, zero, mor_model, target );
<A morphism in AdditiveClosureOfObjectFiniteDisconnectedCategory( Q-LinearClosure( PathCategory( FinQuiver( "q(a,b,c)[aa:a-≻a,bb:b-≻b,cc:c-≻c]" ) ) ) ) defined by a list of 3 matrices of underlying morphisms>
gap> list_of_matrices = ListOfMatrices( mor_reinterp );
true
gap> source := ObjectConstructor( DAC, [1,[0,1,0]] );
<An object in AdditiveClosureOfObjectFiniteDisconnectedCategory( Q-LinearClosure( PathCategory( FinQuiver( "q(a,b,c)[aa:a-≻a,bb:b-≻b,cc:c-≻c]" ) ) ) ) defined by 1 underlying object>
gap> target := ObjectConstructor( DAC, [2,[1,1,0]] );
<An object in AdditiveClosureOfObjectFiniteDisconnectedCategory( Q-LinearClosure( PathCategory( FinQuiver( "q(a,b,c)[aa:a-≻a,bb:b-≻b,cc:c-≻c]" ) ) ) ) defined by 2 underlying objects>
gap> list_of_matrices := [ [], [ [ bb ] ], [] ];;
gap> mor := MorphismConstructor( DAC, source, list_of_matrices, target );
<A morphism in AdditiveClosureOfObjectFiniteDisconnectedCategory( Q-LinearClosure( PathCategory( FinQuiver( "q(a,b,c)[aa:a-≻a,bb:b-≻b,cc:c-≻c]" ) ) ) ) defined by a list of 3 matrices of underlying morphisms>
gap> IsWellDefinedForMorphisms( mor );
true
gap> mor_model := ModelingMorphism( DAC, mor );
<A morphism in AdditiveClosureOfObjectFiniteCategory( Q-LinearClosure( PathCategory( FinQuiver( "q(a,b,c)[aa:a-≻a,bb:b-≻b,cc:c-≻c]" ) ) ) ) defined by a 1 x 2 matrix of underlying morphisms>
gap> zero_mor := ZeroMorphism( L, b, a );
0:(b) -≻ (a)
gap> MorphismMatrix( mor_model ) = [ [ zero_mor, bb ] ];
true
gap> mor_reinterp := ReinterpretationOfMorphism( DAC, source, mor_model, target );
<A morphism in AdditiveClosureOfObjectFiniteDisconnectedCategory( Q-LinearClosure( PathCategory( FinQuiver( "q(a,b,c)[aa:a-≻a,bb:b-≻b,cc:c-≻c]" ) ) ) ) defined by a list of 3 matrices of underlying morphisms>
gap> list_of_matrices = ListOfMatrices( mor_reinterp );
true
gap> source := ObjectConstructor( DAC, [2,[1,1,0]] );
<An object in AdditiveClosureOfObjectFiniteDisconnectedCategory( Q-LinearClosure( PathCategory( FinQuiver( "q(a,b,c)[aa:a-≻a,bb:b-≻b,cc:c-≻c]" ) ) ) ) defined by 2 underlying objects>
gap> target := ObjectConstructor( DAC, [2,[0,2,0]] );
<An object in AdditiveClosureOfObjectFiniteDisconnectedCategory( Q-LinearClosure( PathCategory( FinQuiver( "q(a,b,c)[aa:a-≻a,bb:b-≻b,cc:c-≻c]" ) ) ) ) defined by 2 underlying objects>
gap> list_of_matrices := [ [ [] ], [ [ bb, bb ] ], [] ];;
gap> mor := MorphismConstructor( DAC, source, list_of_matrices, target );
<A morphism in AdditiveClosureOfObjectFiniteDisconnectedCategory( Q-LinearClosure( PathCategory( FinQuiver( "q(a,b,c)[aa:a-≻a,bb:b-≻b,cc:c-≻c]" ) ) ) ) defined by a list of 3 matrices of underlying morphisms>
gap> IsWellDefinedForMorphisms( mor );
true
gap> mor_model := ModelingMorphism( DAC, mor );
<A morphism in AdditiveClosureOfObjectFiniteCategory( Q-LinearClosure( PathCategory( FinQuiver( "q(a,b,c)[aa:a-≻a,bb:b-≻b,cc:c-≻c]" ) ) ) ) defined by a 2 x 2 matrix of underlying morphisms>
gap> zero_mor := ZeroMorphism( L, a, b );
0:(a) -≻ (b)
gap> MorphismMatrix( mor_model ) = [ [ zero_mor, zero_mor ], [ bb, bb ] ];
true
gap> mor_reinterp := ReinterpretationOfMorphism( DAC, source, mor_model, target );
<A morphism in AdditiveClosureOfObjectFiniteDisconnectedCategory( Q-LinearClosure( PathCategory( FinQuiver( "q(a,b,c)[aa:a-≻a,bb:b-≻b,cc:c-≻c]" ) ) ) ) defined by a list of 3 matrices of underlying morphisms>
gap> list_of_matrices = ListOfMatrices( mor_reinterp );
true
gap> source := ObjectConstructor( DAC, [1,[0,1,0]] );
<An object in AdditiveClosureOfObjectFiniteDisconnectedCategory( Q-LinearClosure( PathCategory( FinQuiver( "q(a,b,c)[aa:a-≻a,bb:b-≻b,cc:c-≻c]" ) ) ) ) defined by 1 underlying object>
gap> target := ObjectConstructor( DAC, [1,[1,0,0]] );
<An object in AdditiveClosureOfObjectFiniteDisconnectedCategory( Q-LinearClosure( PathCategory( FinQuiver( "q(a,b,c)[aa:a-≻a,bb:b-≻b,cc:c-≻c]" ) ) ) ) defined by 1 underlying object>
gap> list_of_matrices := [ [], [ [] ], [] ];;
gap> mor := MorphismConstructor( DAC, source, list_of_matrices, target );
<A morphism in AdditiveClosureOfObjectFiniteDisconnectedCategory( Q-LinearClosure( PathCategory( FinQuiver( "q(a,b,c)[aa:a-≻a,bb:b-≻b,cc:c-≻c]" ) ) ) ) defined by a list of 3 matrices of underlying morphisms>
gap> IsWellDefinedForMorphisms( mor );
true
gap> mor_model := ModelingMorphism( DAC, mor );
<A morphism in AdditiveClosureOfObjectFiniteCategory( Q-LinearClosure( PathCategory( FinQuiver( "q(a,b,c)[aa:a-≻a,bb:b-≻b,cc:c-≻c]" ) ) ) ) defined by a 1 x 1 matrix of underlying morphisms>
gap> zero_mor := ZeroMorphism( L, b, a );
0:(b) -≻ (a)
gap> MorphismMatrix( mor_model ) = [ [ zero_mor] ];
true
gap> mor_reinterp := ReinterpretationOfMorphism( DAC, source, mor_model, target );
<A morphism in AdditiveClosureOfObjectFiniteDisconnectedCategory( Q-LinearClosure( PathCategory( FinQuiver( "q(a,b,c)[aa:a-≻a,bb:b-≻b,cc:c-≻c]" ) ) ) ) defined by a list of 3 matrices of underlying morphisms>
gap> list_of_matrices = ListOfMatrices( mor_reinterp );
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
[ [ ] ]
gap> L.a / DAC;;
gap> id_a / DAC;;
gap> [ L.a, L.b, L.a ] / DAC;;
gap> [ matrix_a, matrix_b, matrix_c ] / DAC;;

#
gap> STOP_TEST("AdditiveClosureOfObjectFiniteDisconnectedCategoryTest", 1);
