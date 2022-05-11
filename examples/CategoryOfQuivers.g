#! @BeginChunk CategoryOfQuivers

LoadPackage( "FunctorCategories" );

#! In the following we construct the category of quivers:

#! @Example
Quivers;
#! CategoryOfQuiversEnrichedOver( SkeletalFinSets )
V := Quivers.V;
#! <A projective object in CategoryOfQuiversEnrichedOver( SkeletalFinSets )>
Display( V );
#! Image of <(V)>:
#! 1
#! 
#! Image of <(A)>:
#! 0
#! 
#! Image of (A)-[(s)]->(V):
#! [ 0, [  ], 1 ]
#! 
#! Image of (A)-[(t)]->(V):
#! [ 0, [  ], 1 ]
#! 
#! An object in FunctorCategory( Category freely generated by
#! the right quiver q_op(V,A)[s:A->V,t:A->V] -> SkeletalFinSets )
#! given by the above data
#! 
#! An object in CategoryOfQuiversEnrichedOver( SkeletalFinSets )
#! given by the above data
A := Quivers.A;
#! <A projective object in CategoryOfQuiversEnrichedOver( SkeletalFinSets )>
Display( A );
#! Image of <(V)>:
#! 2
#! 
#! Image of <(A)>:
#! 1
#! 
#! Image of (A)-[(s)]->(V):
#! [ 1, [ 0 ], 2 ]
#! 
#! Image of (A)-[(t)]->(V):
#! [ 1, [ 1 ], 2 ]
#! 
#! An object in FunctorCategory( Category freely generated by
#! the right quiver q_op(V,A)[s:A->V,t:A->V] -> SkeletalFinSets )
#! given by the above data
#! 
#! An object in CategoryOfQuiversEnrichedOver( SkeletalFinSets )
#! given by the above data
T := TerminalObject( Quivers );
#! <An object in CategoryOfQuiversEnrichedOver( SkeletalFinSets )>
Display( T );
#! Image of <(V)>:
#! 1
#! 
#! Image of <(A)>:
#! 1
#! 
#! Image of (A)-[(s)]->(V):
#! [ 1, [ 0 ], 1 ]
#! 
#! Image of (A)-[(t)]->(V):
#! [ 1, [ 0 ], 1 ]
#! 
#! An object in FunctorCategory( Category freely generated by
#! the right quiver q_op(V,A)[s:A->V,t:A->V] -> SkeletalFinSets )
#! given by the above data
#! 
#! An object in CategoryOfQuiversEnrichedOver( SkeletalFinSets )
#! given by the above data
G := CreateQuiver( 3, [ 0,1, 0,1, 1,2, 2,1, 2,2 ] );
#! <An object in CategoryOfQuiversEnrichedOver( SkeletalFinSets )>
Display( G );
#! Image of <(V)>:
#! 3
#! 
#! Image of <(A)>:
#! 5
#! 
#! Image of (A)-[(s)]->(V):
#! [ 5, [ 0, 0, 1, 2, 2 ], 3 ]
#! 
#! Image of (A)-[(t)]->(V):
#! [ 5, [ 1, 1, 2, 1, 2 ], 3 ]
#! 
#! An object in FunctorCategory( Category freely generated by
#! the right quiver q_op(V,A)[s:A->V,t:A->V] -> SkeletalFinSets )
#! given by the above data
#! 
#! An object in CategoryOfQuiversEnrichedOver( SkeletalFinSets )
#! given by the above data
global_G := HomStructure( T, G );
#! <An object in SkeletalFinSets>
Display( global_G );
#! 1
discrete := DirectProduct( G, V );
#! <An object in CategoryOfQuiversEnrichedOver( SkeletalFinSets )>
Display( discrete );
#! Image of <(V)>:
#! 3
#! 
#! Image of <(A)>:
#! 0
#! 
#! Image of (A)-[(s)]->(V):
#! [ 0, [ ], 3 ]
#! 
#! Image of (A)-[(t)]->(V):
#! [ 0, [ ], 3 ]
#! 
#! An object in FunctorCategory( Category freely generated by
#! the right quiver q_op(V,A)[s:A->V,t:A->V] -> SkeletalFinSets )
#! given by the above data
#! 
#! An object in CategoryOfQuiversEnrichedOver( SkeletalFinSets )
#! given by the above data
global_discrete := HomStructure( T, discrete );
#! <An object in SkeletalFinSets>
Display( global_discrete );
#! 0
complete := Exponential( V, G );
#! <An object in CategoryOfQuiversEnrichedOver( SkeletalFinSets )>
Display( complete );
#! Image of <(V)>:
#! 3
#! 
#! Image of <(A)>:
#! 9
#! 
#! Image of (A)-[(s)]->(V):
#! [ 9, [ 0, 0, 0, 1, 1, 1, 2, 2, 2 ], 3 ]
#! 
#! Image of (A)-[(t)]->(V):
#! [ 9, [ 0, 1, 2, 0, 1, 2, 0, 1, 2 ], 3 ]
#! 
#! An object in FunctorCategory( Category freely generated by
#! the right quiver q_op(V,A)[s:A->V,t:A->V] -> SkeletalFinSets )
#! given by the above data
#! 
#! An object in CategoryOfQuiversEnrichedOver( SkeletalFinSets )
#! given by the above data
global_complete := HomStructure( T, complete );
#! <An object in SkeletalFinSets>
Display( global_complete );
#! 3
GA := DirectProduct( G, A );
#! <An object in CategoryOfQuiversEnrichedOver( SkeletalFinSets )>
Display( GA );
#! Image of <(V)>:
#! 6
#! 
#! Image of <(A)>:
#! 5
#! 
#! Image of (A)-[(s)]->(V):
#! [ 5, [ 0, 0, 2, 4, 4 ], 6 ]
#! 
#! Image of (A)-[(t)]->(V):
#! [ 5, [ 3, 3, 5, 3, 5 ], 6 ]
#! 
#! An object in FunctorCategory( Category freely generated by
#! the right quiver q_op(V,A)[s:A->V,t:A->V] -> SkeletalFinSets )
#! given by the above data
#! 
#! An object in CategoryOfQuiversEnrichedOver( SkeletalFinSets )
#! given by the above data
homAG := HomStructure( A, G );
#! <An object in SkeletalFinSets>
Display( homAG );
#! 5
arrows := Exponential( A, G );
#! <An object in CategoryOfQuiversEnrichedOver( SkeletalFinSets )>
Display( arrows );
#! Image of <(V)>:
#! 9
#! 
#! Image of <(A)>:
#! 45
#! 
#! Image of (A)-[(s)]->(V):
#! [ 45, [ 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 2, 2, 2,
#!         2, 2, 2, 3, 3, 3, 4, 4, 4, 5, 5, 5, 6, 6, 6,
#!         6, 6, 6, 7, 7, 7, 7, 7, 7, 8, 8, 8, 8, 8, 8 ], 9 ]
#! 
#! Image of (A)-[(t)]->(V):
#! [ 45, [ 1, 1, 4, 4, 7, 7, 1, 1, 4, 4, 7, 7, 1, 1, 4,
#!         4, 7, 7, 2, 5, 8, 2, 5, 8, 2, 5, 8, 1, 2, 4,
#!         5, 7, 8, 1, 2, 4, 5, 7, 8, 1, 2, 4, 5, 7, 8 ], 9 ]
#! 
#! An object in FunctorCategory( Category freely generated by
#! the right quiver q_op(V,A)[s:A->V,t:A->V] -> SkeletalFinSets )
#! given by the above data
#! 
#! An object in CategoryOfQuiversEnrichedOver( SkeletalFinSets )
#! given by the above data
global_arrows := HomStructure( T, arrows );
#! <An object in SkeletalFinSets>
Display( global_arrows );
#! 5
prjG := ProjectionInFactorOfDirectProduct( [ G, V ], 1 );
#! <A morphism in CategoryOfQuiversEnrichedOver( SkeletalFinSets )>
Display( prjG );
#! Image of <(V)>:
#! [ 3, [ 0, 1, 2 ], 3 ]
#! 
#! Image of <(A)>:
#! [ 0, [  ], 5 ]
#! 
#! A morphism in FunctorCategory( Category freely generated by
#! the right quiver q_op(V,A)[s:A->V,t:A->V] -> SkeletalFinSets )
#! given by the above data
#! 
#! A morphism in CategoryOfQuiversEnrichedOver( SkeletalFinSets )
#! given by the above data
IsEpimorphism( prjG );
#! false
prj_discrete := ProjectionInFactorOfDirectProduct( [ discrete, V ], 1 );
#! <A morphism in CategoryOfQuiversEnrichedOver( SkeletalFinSets )>
Display( prj_discrete );
#! Image of <(V)>:
#! [ 3, [ 0, 1, 2 ], 3 ]
#! 
#! Image of <(A)>:
#! [ 0, [  ], 0 ]
#! 
#! A morphism in FunctorCategory( Category freely generated by
#! the right quiver q_op(V,A)[s:A->V,t:A->V] -> SkeletalFinSets )
#! given by the above data
#! 
#! A morphism in CategoryOfQuiversEnrichedOver( SkeletalFinSets )
#! given by the above data
IsEpimorphism( prj_discrete );
#! true
Display( Exponential( T, G ) );
#! Image of <(V)>:
#! 3
#! 
#! Image of <(A)>:
#! 5
#! 
#! Image of (A)-[(s)]->(V):
#! [ 5, [ 0, 0, 1, 2, 2 ], 3 ]
#! 
#! Image of (A)-[(t)]->(V):
#! [ 5, [ 1, 1, 2, 1, 2 ], 3 ]
#! 
#! An object in FunctorCategory( Category freely generated by
#! the right quiver q_op(V,A)[s:A->V,t:A->V] -> SkeletalFinSets )
#! given by the above data
#! 
#! An object in CategoryOfQuiversEnrichedOver( SkeletalFinSets )
#! given by the above data
t := UniversalMorphismIntoTerminalObject( V );
#! <A morphism in CategoryOfQuiversEnrichedOver( SkeletalFinSets )>
Display( t );
#! Image of <(V)>:
#! [ 1, [ 0 ], 1 ]
#! 
#! Image of <(A)>:
#! [ 0, [  ], 1 ]
#! 
#! A morphism in FunctorCategory( Category freely generated by
#! the right quiver q_op(V,A)[s:A->V,t:A->V] -> SkeletalFinSets )
#! given by the above data
#! 
#! A morphism in CategoryOfQuiversEnrichedOver( SkeletalFinSets )
#! given by the above data
embG := Exponential( t, G );
#! <A morphism in CategoryOfQuiversEnrichedOver( SkeletalFinSets )>
Display( embG );
#! Image of <(V)>:
#! [ 3, [ 0, 1, 2 ], 3 ]
#! 
#! Image of <(A)>:
#! [ 5, [ 1, 1, 5, 7, 8 ], 9 ]
#! 
#! A morphism in FunctorCategory( Category freely generated by
#! the right quiver q_op(V,A)[s:A->V,t:A->V] -> SkeletalFinSets )
#! given by the above data
#! 
#! A morphism in CategoryOfQuiversEnrichedOver( SkeletalFinSets )
#! given by the above data
IsEpimorphism( embG );
#! false
emb_complete := Exponential( t, complete );
#! <A morphism in CategoryOfQuiversEnrichedOver( SkeletalFinSets )>
Display( emb_complete );
#! Image of <(V)>:
#! [ 3, [ 0, 1, 2 ], 3 ]
#! 
#! Image of <(A)>:
#! [ 9, [ 0, 1, 2, 3, 4, 5, 6, 7, 8 ], 9 ]
#! 
#! A morphism in FunctorCategory( Category freely generated by
#! the right quiver q_op(V,A)[s:A->V,t:A->V] -> SkeletalFinSets )
#! given by the above data
#! 
#! A morphism in CategoryOfQuiversEnrichedOver( SkeletalFinSets )
#! given by the above data
IsEpimorphism( emb_complete );
#! true
s := Quivers.s;
#! <A morphism in CategoryOfQuiversEnrichedOver( SkeletalFinSets )>
Display( s );
#! Image of <(V)>:
#! [ 1, [ 0 ], 2 ]
#! 
#! Image of <(A)>:
#! [ 0, [  ], 1 ]
#! 
#! A morphism in FunctorCategory( Category freely generated by
#! the right quiver q_op(V,A)[s:A->V,t:A->V] -> SkeletalFinSets )
#! given by the above data
#! 
#! A morphism in CategoryOfQuiversEnrichedOver( SkeletalFinSets )
#! given by the above data
t := Quivers.t;
#! <A morphism in CategoryOfQuiversEnrichedOver( SkeletalFinSets )>
Display( t );
#! Image of <(V)>:
#! [ 1, [ 1 ], 2 ]
#! 
#! Image of <(A)>:
#! [ 0, [  ], 1 ]
#! 
#! A morphism in FunctorCategory( Category freely generated by
#! the right quiver q_op(V,A)[s:A->V,t:A->V] -> SkeletalFinSets )
#! given by the above data
#! 
#! A morphism in CategoryOfQuiversEnrichedOver( SkeletalFinSets )
#! given by the above data
omega := SubobjectClassifier( Quivers );
#! <An object in CategoryOfQuiversEnrichedOver( SkeletalFinSets )>
Display( omega );
#! Image of <(V)>:
#! 2
#! 
#! Image of <(A)>:
#! 5
#! 
#! Image of (A)-[(s)]->(V):
#! [ 5, [ 0, 0, 1, 1, 1 ], 2 ]
#! 
#! Image of (A)-[(t)]->(V):
#! [ 5, [ 0, 1, 0, 1, 1 ], 2 ]
#! 
#! An object in FunctorCategory( Category freely generated by
#! the right quiver q_op(V,A)[s:A->V,t:A->V] -> SkeletalFinSets )
#! given by the above data
#! 
#! An object in CategoryOfQuiversEnrichedOver( SkeletalFinSets )
#! given by the above data
#! @EndExample
#! @EndChunk
