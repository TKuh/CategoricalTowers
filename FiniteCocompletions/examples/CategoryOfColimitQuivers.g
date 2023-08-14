#! @BeginChunk CategoryOfColimitQuivers

#! @Example
LoadPackage( "FunctorCategories" );
#! true
FinBouquets;
#! FinBouquets
Chat := ModelingCategory( FinBouquets );
#! FiniteCocompletion( FreeCategory( RightQuiver( "q(P,L)[b:P->L]" ) ) )
Ccqv := CategoryOfColimitQuivers(
                 UnderlyingCategory( FinBouquets ) );
#! CategoryOfColimitQuivers(
#! FreeCategory( RightQuiver( "q(P,L)[b:P->L]" ) ) )
P := Ccqv.P;
#! <A projective object in CategoryOfColimitQuivers(
#!  FreeCategory( RightQuiver( "q(P,L)[b:P->L]" ) ) )>
Display( P );
#! [ [ <(P)> ], [  ] ]
#! 
#! An object in CategoryOfColimitQuivers(
#! FreeCategory( RightQuiver( "q(P,L)[b:P->L]" ) ) ) given by the above data
L := Ccqv.L;
#! <A projective object in CategoryOfColimitQuivers(
#!  FreeCategory( RightQuiver( "q(P,L)[b:P->L]" ) ) )>
Display( L );
#! [ [ <(L)> ], [  ] ]
#! 
#! An object in CategoryOfColimitQuivers(
#! FreeCategory( RightQuiver( "q(P,L)[b:P->L]" ) ) ) given by the above data
b := Ccqv.b;
#! <A morphism in CategoryOfColimitQuivers(
#!  FreeCategory( RightQuiver( "q(P,L)[b:P->L]" ) ) )>
Display( b );
#! Source: [ [ <(P)> ], [  ] ]
#! 
#! An object in CategoryOfColimitQuivers(
#! FreeCategory( RightQuiver( "q(P,L)[b:P->L]" ) ) ) given by the above data
#! 
#! Datum:  [ [ [ 0 ], [ (P)-[(b)]->(L) ] ], [  ] ]
#! 
#! Range:  [ [ <(L)> ], [  ] ]
#! 
#! An object in CategoryOfColimitQuivers(
#! FreeCategory( RightQuiver( "q(P,L)[b:P->L]" ) ) ) given by the above data
#! 
#! A morphism in CategoryOfColimitQuivers(
#! FreeCategory( RightQuiver( "q(P,L)[b:P->L]" ) ) ) given by the above data
F := CreateBouquet( 3, [ 0, 0, 0, 2 ] );
#! <An object in FinBouquets>
Display( F );
#! ( { 0, 1, 2 }, { 0 ↦ 0, 1 ↦ 0, 2 ↦ 0, 3 ↦ 2 } )
F_as_presheaf := ModelingObject( Chat, ModelingObject( FinBouquets, F ) );
#! <An object in PreSheaves( FreeCategory( RightQuiver( "q(P,L)[b:P->L]" ) ),
#!  SkeletalFinSets )>
F_as_coequalizer_pair := CoYonedaLemmaOnObjects( F_as_presheaf );
#! <An object in PairOfParallelArrowsCategory( FiniteStrictCoproductCocompletion(
#! FreeCategory( RightQuiver( "q(P,L)[b:P->L]" ) ) ) )>
Display( F_as_coequalizer_pair );
#! Image of <(V)>:
#! [ 7, [ <(P)>, <(P)>, <(P)>, <(L)>, <(L)>, <(L)>, <(L)> ] ]
#! 
#! An object in FiniteStrictCoproductCocompletion( FreeCategory(
#! RightQuiver( "q(P,L)[b:P->L]" ) ) ) given by the above data
#! 
#! Image of <(A)>:
#! [ 4, [ <(P)>, <(P)>, <(P)>, <(P)> ] ]
#! 
#! An object in FiniteStrictCoproductCocompletion( FreeCategory(
#! RightQuiver( "q(P,L)[b:P->L]" ) ) ) given by the above data
#! 
#! Image of (V)-[(s)]->(A):
#! { 0,..., 3 } ⱶ[ 0, 0, 0, 2 ]→ { 0,..., 6 }
#! 
#! [ (P)-[(P)]->(P), (P)-[(P)]->(P), (P)-[(P)]->(P), (P)-[(P)]->(P) ]
#! 
#! A morphism in FiniteStrictCoproductCocompletion( FreeCategory(
#! RightQuiver( "q(P,L)[b:P->L]" ) ) ) given by the above data
#! 
#! Image of (V)-[(t)]->(A):
#! { 0,..., 3 } ⱶ[ 3, 4, 5, 6 ]→ { 0,..., 6 }
#! 
#! [ (P)-[(b)]->(L), (P)-[(b)]->(L), (P)-[(b)]->(L), (P)-[(b)]->(L) ]
#! 
#! A morphism in FiniteStrictCoproductCocompletion( FreeCategory(
#! RightQuiver( "q(P,L)[b:P->L]" ) ) ) given by the above data
#! 
#! An object in PreSheaves( FreeCategory( RightQuiver( "q(V,A)[s:V->A,t:V->A]" ) ),
#! FiniteStrictCoproductCocompletion(
#! FreeCategory( RightQuiver( "q(P,L)[b:P->L]" ) ) ) ) given by the above data
#! 
#! An object in PairOfParallelArrowsCategory( FiniteStrictCoproductCocompletion(
#! FreeCategory( RightQuiver( "q(P,L)[b:P->L]" ) ) ) ) given by the above data
F_as_colimit_quiver := ReinterpretationOfObject( Ccqv, F_as_coequalizer_pair );
#! <An object in CategoryOfColimitQuivers(
#!  FreeCategory( RightQuiver( "q(P,L)[b:P->L]" ) ) )>
Display( F_as_colimit_quiver );
#! [ [ <(P)>, <(P)>, <(P)>, <(L)>, <(L)>, <(L)>, <(L)> ],
#!   [ [ 0, (P)-[(b)]->(L), 3 ], [ 0, (P)-[(b)]->(L), 4 ],
#!     [ 0, (P)-[(b)]->(L), 5 ], [ 2, (P)-[(b)]->(L), 6 ] ] ]
#! 
#! An object in CategoryOfColimitQuivers(
#! FreeCategory( RightQuiver( "q(P,L)[b:P->L]" ) ) ) given by the above data
#! @EndExample
#! @EndChunk