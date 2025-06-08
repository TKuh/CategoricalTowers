gap> START_TEST("AdditiveClosureOfObjectFiniteCategory_Reinterpreted.tst");
gap> 
gap> LoadPackage( "FiniteCocompletions", false );
true
gap> LoadPackage( "FunctorCategories", false );
true
gap> 
gap> q := FinQuiver( "q(a,b,c)[ab:a->b,ba:b->a,ca:c->a,cb:c->b]" );;
gap> P := PathCategory( q );;
gap> Q := HomalgFieldOfRationals( );;
gap> L := Q[P];;
gap> AC_fin := AdditiveClosureOfObjectFiniteCategory_Reinterpreted( L );;
gap> AC := ModelingCategory( AC_fin );;
gap> 
gap> a := P.a / L;;
gap> b := P.b / L;;
gap> c := P.c / L;;
gap> ab := P.ab / L;;
gap> ba := P.ba / L;;
gap> ca := P.ca / L;;
gap> cb := P.cb / L;;
gap> id_a := IdentityMorphism( L, a );;
gap> id_b := IdentityMorphism( L, b );;
gap> 
gap> #########################################
gap> # Objects
gap> #########################################
gap> 
gap> # Taking the model and then the reinterpretation on objects is the identity: (AC_fin -AC -AC_fin) = id
gap> a1_reinterp := ObjectConstructor( AC_fin, [5,[2,2,1]] );;
gap> a2_reinterp := ObjectConstructor( AC_fin, [2,[1,1,0]] );;
gap> a1_model := ModelingTowerObjectConstructor( AC_fin, ObjectDatum( a1_reinterp ) );;
gap> a2_model := ModelingTowerObjectConstructor( AC_fin, ObjectDatum( a2_reinterp ) );;
gap> a1_reinterp = ObjectConstructor( AC_fin, ModelingTowerObjectDatum( AC_fin, a1_model ) );
true
gap> a2_reinterp = ObjectConstructor( AC_fin, ModelingTowerObjectDatum( AC_fin, a2_model ) );
true
gap> # Taking the reinterpretation and then the model on objects is only an isomorphism and not the identity: (AC -AC_fin -AC) =/= id.
gap> # This is due to the sorting/reordering in the reinterpretation.
gap> 
gap> a1_model := ObjectConstructor( AC, [ b, a, b, c, a ] );;
gap> a2_model := ObjectConstructor( AC, [ b, a ] );;
gap> 
gap> # The objectlists of AC and those of AC_fin will be ordered differently, hence can not be equal.
gap> a1_model = ModelingTowerObjectConstructor( AC_fin, ObjectDatum( a1_reinterp ) );
false
gap> a2_model = ModelingTowerObjectConstructor( AC_fin, ObjectDatum( a2_reinterp ) );
false
gap> 
gap> #########################################
gap> # Morphisms
gap> #########################################
gap> 
gap> # Taking the model and then the reinterpretation on morphism is the identity: AC_fin -AC -AC_fin = id.
gap> # First construct a morphism in AC_fin.
gap> 
gap> matrix := [ [id_a, ab], [id_a, ab], [ba, id_b], [ba, id_b], [ca, cb] ];;
gap> mor_reinterp := MorphismConstructor( AC_fin, a1_reinterp, matrix, a2_reinterp );;
gap> IsWellDefinedForMorphisms( mor_reinterp );
true
gap> # Take the model of the morphism.
gap> source := ModelingTowerObjectConstructor( AC_fin, ObjectDatum( Source( mor_reinterp ) ) );;
gap> target := ModelingTowerObjectConstructor( AC_fin, ObjectDatum( Target( mor_reinterp ) ) );;
gap> mor_model := ModelingTowerMorphismConstructor( AC_fin, source, MorphismDatum( mor_reinterp ), target );;
gap> 
gap> # Check that mor_reinterp = Reinterpretation( Model( mor_reinterp ) ).
gap> mor_reinterp = MorphismConstructor( AC_fin, Source(mor_reinterp), ModelingTowerMorphismDatum( AC_fin, mor_model ), Target( mor_reinterp) );
true
gap> # Taking the reinterpretation and then the model on morphisms does not give the identity: AC -AC_fin -AC
gap> # First construct a morphism in the model AC.
gap> 
gap> source := ObjectConstructor( AC, [ c, a, b, b, a ] );;
gap> target := ObjectConstructor( AC, [ b, a ] );;
gap> matrix := [ [cb, ca], [ab, id_a], [id_b, ba], [id_b, ba], [ab, id_a] ];;
gap> mor_model := ModelingTowerMorphismConstructor( AC_fin, source, matrix, target );;
gap> 
gap> # Take the reinterpretation of mor_model.
gap> source_reinterp := ObjectConstructor( AC_fin, ModelingTowerObjectDatum( AC_fin, source ) );;
gap> target_reinterp := ObjectConstructor( AC_fin, ModelingTowerObjectDatum( AC_fin, target ) );;
gap> matrix_sorted := ModelingTowerMorphismDatum( AC_fin, mor_model );;
gap> mor_reinterp := MorphismConstructor( AC_fin, source_reinterp, matrix_sorted, target_reinterp );;
gap> IsWellDefinedForMorphisms( mor_reinterp );
true
gap> # Take the model of mor_reinterp and compare it with mor_model.
gap> # They are not equal due to the reordering of the matrix in the reinterpretation.
gap> source := ModelingTowerObjectConstructor( AC_fin, ObjectDatum( AC_fin, Source( mor_reinterp ) ) );;
gap> target := ModelingTowerObjectConstructor( AC_fin, ObjectDatum( AC_fin, Target( mor_reinterp ) ) );;
gap> mor_model = ModelingTowerMorphismConstructor( AC_fin, source, MorphismDatum( AC_fin, mor_reinterp ), target );
false
gap> 
gap> STOP_TEST("AdditiveClosureOfObjectFiniteCategory_Reinterpreted.tst", 1);
