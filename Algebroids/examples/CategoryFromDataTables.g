#! @BeginChunk CategoryFromDataTables

#! @Example
LoadPackage( "Algebroids", false );
#! true
Delta1 := SimplicialCategoryTruncatedInDegree( 1 );
#! FreeCategory( RightQuiver( "Delta(C0,C1)[id:C1->C0,s:C0->C1,t:C0->C1]" ) )
#! / [ s*id = C0, t*id = C0 ]
Size( Delta1 );
#! 7
mors := SetOfMorphisms( Delta1 );
#! [ (C0)-[(C0)]->(C0), (C1)-[(id)]->(C0), (C0)-[(s)]->(C1), (C0)-[(t)]->(C1),
#!   (C1)-[(C1)]->(C1), (C1)-[(id*s)]->(C1), (C1)-[(id*t)]->(C1) ]
List( mors, DecompositionOfMorphismInCategory );
#! [ [  ], [ (C1)-[(id)]->(C0) ], [ (C0)-[(s)]->(C1) ], [ (C0)-[(t)]->(C1) ],
#!   [  ], [ (C1)-[(id)]->(C0), (C0)-[(s)]->(C1) ],
#!   [ (C1)-[(id)]->(C0), (C0)-[(t)]->(C1) ] ]
C := CategoryFromDataTables( Delta1 );
#! FreeCategory( RightQuiver( "Delta(C0,C1)[id:C1->C0,s:C0->C1,t:C0->C1]" ) )
#! / [ s*id = C0, t*id = C0 ]
Size( C );
#! 7
morsC := SetOfMorphisms( C );
#! [ (C0)-[(C0)]->(C0), (C1)-[(id)]->(C0), (C0)-[(s)]->(C1), (C0)-[(t)]->(C1),
#!   (C1)-[(C1)]->(C1), (C1)-[(id*s)]->(C1), (C1)-[(id*t)]->(C1) ]
List( morsC, DecompositionOfMorphismInCategory );
#! [ [  ], [ (C1)-[(id)]->(C0) ], [ (C0)-[(s)]->(C1) ], [ (C0)-[(t)]->(C1) ],
#!   [  ], [ (C1)-[(id)]->(C0), (C0)-[(s)]->(C1) ],
#!   [ (C1)-[(id)]->(C0), (C0)-[(t)]->(C1) ] ]
NerveTruncatedInDegree2Data( C ) = NerveTruncatedInDegree2Data( Delta1 );
#! true
IndicesOfGeneratingMorphisms( C );
#! [ 1, 2, 3 ]
SetOfGeneratingMorphisms( C );
#! [ (C1)-[(id)]->(C0), (C0)-[(s)]->(C1), (C0)-[(t)]->(C1) ]
Display( C );
#! A CAP category with name
#! FreeCategory( RightQuiver( "Delta(C0,C1)[id:C1->C0,s:C0->C1,t:C0->C1]" ) )
#! / [ s*id = C0, t*id = C0 ]:
#! 
#! 19 primitive operations were used to derive 57 operations for this category
#! which algorithmically
#! * IsFiniteCategory
#! * IsFinitelyPresentedCategory
#! * IsEquippedWithHomomorphismStructure
C0 := CreateObject( C, 0 );
#! <(C0)>
IsWellDefined( C0 );
#! true
C1 := 1 / C;
#! <(C1)>
IsWellDefined( C1 );
#! true
IsWellDefined( 2 / C );
#! false
idC0 := CreateMorphism( C0, 0, C0 );
#! (C0)-[(C0)]->(C0)
CreateMorphism( C, 0 ) = idC0;
#! true
IsOne( idC0 );
#! true
id := CreateMorphism( C, 1 );
#! (C1)-[(id)]->(C0)
s := CreateMorphism( C, 2 );
#! (C0)-[(s)]->(C1)
t := CreateMorphism( C, 3 );
#! (C0)-[(t)]->(C1)
IsSplitMonomorphism( s );
#! true
IsSplitMonomorphism( t );
#! true
IsEpimorphism( s );
#! false
IsEpimorphism( t );
#! false
IsSplitEpimorphism( id );
#! true
IsMonomorphism( id );
#! false
idC1 := CreateMorphism( C, 4 );
#! (C1)-[(C1)]->(C1)
IsOne( idC1 );
#! true
sigma := CreateMorphism( C, 5 );
#! (C1)-[(id*s)]->(C1)
tau := CreateMorphism( C, 6 );
#! (C1)-[(id*t)]->(C1)
IsEndomorphism( sigma );
#! true
IsMonomorphism( sigma );
#! false
IsEpimorphism( sigma );
#! false
IsEndomorphism( tau );
#! true
IsMonomorphism( tau );
#! false
IsEpimorphism( tau );
#! false
IsOne( tau );
#! false
IsWellDefined( CreateMorphism( C1, 7, C1 ) );
#! false
PreCompose( s, id ) = idC0;
#! true
PreCompose( t, id ) = idC0;
#! true
PreCompose( id, s ) = sigma;
#! true
PreCompose( id, t ) = tau;
#! true
HomStructure( C0, C0 );
#! |1|
HomStructure( C1, C1 );
#! |3|
HomStructure( C0, C1 );
#! |2|
HomStructure( C1, C0 );
#! |1|
Display( HomStructure( s ) );
#! { 0 } ⱶ[ 0 ]→ { 0, 1 }
Display( HomStructure( t ) );
#! { 0 } ⱶ[ 1 ]→ { 0, 1 }
HomStructure( Source( s ), Target( s ), HomStructure( s ) ) = s;
#! true
HomStructure( Source( t ), Target( t ), HomStructure( t ) ) = t;
#! true
Display( HomStructure( s, t ) );
#! { 0 } ⱶ[ 1 ]→ { 0, 1 }
Display( HomStructure( t, s ) );
#! { 0 } ⱶ[ 0 ]→ { 0, 1 }
Display( HomStructure( sigma, tau ) );
#! { 0, 1, 2 } ⱶ[ 2, 2, 2 ]→ { 0, 1, 2 }
Display( HomStructure(
        PreCompose( Delta1.id, Delta1.s ),
        PreCompose( Delta1.id, Delta1.t ) ) );
#! { 0, 1, 2 } ⱶ[ 2, 2, 2 ]→ { 0, 1, 2 }
Display( HomStructure( tau, sigma ) );
#! { 0, 1, 2 } ⱶ[ 1, 1, 1 ]→ { 0, 1, 2 }
Display( HomStructure(
        PreCompose( Delta1.id, Delta1.t ),
        PreCompose( Delta1.id, Delta1.s ) ) );
#! { 0, 1, 2 } ⱶ[ 1, 1, 1 ]→ { 0, 1, 2 }
Display( HomStructure( tau, idC1 ) );
#! { 0, 1, 2 } ⱶ[ 2, 1, 2 ]→ { 0, 1, 2 }
Display( HomStructure( idC1, idC1 ) );
#! { 0, 1, 2 } ⱶ[ 0, 1, 2 ]→ { 0, 1, 2 }
mors := SetOfMorphisms( C );
#! [ (C0)-[(C0)]->(C0), (C1)-[(id)]->(C0), (C0)-[(s)]->(C1), (C0)-[(t)]->(C1),
#!   (C1)-[(C1)]->(C1), (C1)-[(id*s)]->(C1), (C1)-[(id*t)]->(C1) ]
List( mors, OppositeMorphismInOppositeCategoryFromDataTables );
#! [ (C0)-[(C0)]->(C0), (C0)-[(id)]->(C1), (C1)-[(s)]->(C0), (C1)-[(t)]->(C0),
#! (C1)-[(C1)]->(C1), (C1)-[(s*id)]->(C1), (C1)-[(t*id)]->(C1) ]
mors;
#! [ (C0)-[(C0)]->(C0), (C1)-[(id)]->(C0), (C0)-[(s)]->(C1), (C0)-[(t)]->(C1),
#!   (C1)-[(C1)]->(C1), (C1)-[(id*s)]->(C1), (C1)-[(id*t)]->(C1) ]
List( mors, DecompositionOfMorphismInCategory );
#! [ [  ], [ (C1)-[(id)]->(C0) ], [ (C0)-[(s)]->(C1) ], [ (C0)-[(t)]->(C1) ],
#!   [  ], [ (C1)-[(id)]->(C0), (C0)-[(s)]->(C1) ],
#!   [ (C1)-[(id)]->(C0), (C0)-[(t)]->(C1) ] ]
C_op := OppositeCategoryFromDataTables( C );
#! Opposite(
#! FreeCategory( RightQuiver( "Delta(C0,C1)[id:C1->C0,s:C0->C1,t:C0->C1]" ) )
#! / [ s*id = C0, t*id = C0 ] )
IsIdenticalObj( OppositeCategoryFromDataTables( C_op ), C );
#! true
IndicesOfGeneratingMorphisms( C_op );
#! [ 3, 1, 2 ]
SetOfGeneratingMorphisms( C_op );
#! [ (C0)-[(id)]->(C1), (C1)-[(s)]->(C0), (C1)-[(t)]->(C0) ]
mors_op := SetOfMorphisms( C_op );
#! [ (C0)-[(C0)]->(C0), (C1)-[(s)]->(C0), (C1)-[(t)]->(C0), (C0)-[(id)]->(C1),
#!   (C1)-[(C1)]->(C1), (C1)-[(s*id)]->(C1), (C1)-[(t*id)]->(C1) ]
List( mors_op, DecompositionOfMorphismInCategory );
#! [ [  ], [ (C1)-[(s)]->(C0) ], [ (C1)-[(t)]->(C0) ], [ (C0)-[(id)]->(C1) ],
#!   [  ], [ (C1)-[(s)]->(C0), (C0)-[(id)]->(C1) ],
#!   [ (C1)-[(t)]->(C0), (C0)-[(id)]->(C1) ] ]
#! @EndExample
#! @EndChunk
