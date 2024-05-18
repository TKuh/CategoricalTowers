# SPDX-License-Identifier: GPL-2.0-or-later
# Locales: Locales, frames, coframes, meet semi-lattices of locally closed subsets, and Boolean algebras of constructible sets
#
# Implementations
#

##
InstallValue( CAP_INTERNAL_METHOD_NAME_LIST_FOR_PREORDERED_SET_OF_CATEGORY,
  [
   # create_func_bool and create_func_object can only deal with operations which do
   # not get morphisms as arguments, because they access `UnderlyingCell` which is
   # not set for morphisms
   "IsWellDefinedForObjects",
   "IsHomSetInhabited",
   "TensorUnit",
   "TensorProductOnObjects",
   "InternalHomOnObjects",
   #"InternalHomOnMorphismsWithGivenInternalHoms",
   "InternalCoHomOnObjects",
   #"InternalCoHomOnMorphismsWithGivenInternalCoHoms",
   # P admits the same (co)limits as C,
   # in fact, a weak (co)limit in C becomes a (co)limit in P.
   # However, we must not automatically detect these (co)limits via `universal_type`,
   # because `universal_type` is sometimes set for technical instead of mathematical reasons.
   # Additionally, we must be careful with the restrictions of create_func_bool and create_func_object
   # mentioned above.
   # DirectProduct
   "DirectProduct",
   #"ProjectionInFactorOfDirectProductWithGivenDirectProduct",
   #"UniversalMorphismIntoDirectProductWithGivenDirectProduct",
   # Coproduct
   "Coproduct",
   #"InjectionOfCofactorOfCoproductWithGivenCoproduct",
   #"UniversalMorphismFromCoproductWithGivenCoproduct",
   # DirectSum
   "DirectSum",
   #"ProjectionInFactorOfDirectSumWithGivenDirectSum",
   #"InjectionOfCofactorOfDirectSumWithGivenDirectSum",
   #"UniversalMorphismIntoDirectSumWithGivenDirectSum",
   #"UniversalMorphismFromDirectSumWithGivenDirectSum",
   # TerminalObject
   "TerminalObject",
   #"UniversalMorphismIntoTerminalObjectWithGivenTerminalObject",
   # InitialObject
   "InitialObject",
   #"UniversalMorphismFromInitialObjectWithGivenInitialObject",
   # ZeroObject
   "ZeroObject",
   #"UniversalMorphismIntoZeroObjectWithGivenZeroObject",
   #"UniversalMorphismFromZeroObjectWithGivenZeroObject",
   ] );

##
InstallMethod( AsCellOfProset,
        "for a CAP object",
        [ IsCapCategoryObject ],
        
  function( object )
    local P;
    
    P := ProsetOfCategory( CapCategory( object ) );
    
    return ObjectConstructor( P, object );
    
end );

##
InstallMethod( AsCellOfStableProset,
        "for a CAP object",
        [ IsCapCategoryObject ],
        
  function( object )
    local P;
    
    P := StableProsetOfCategory( CapCategory( object ) );
    
    return ObjectConstructor( P, object );
    
end );

##
InstallMethod( AsCellOfProset,
        "for a CAP morphism",
        [ IsCapCategoryMorphism ],
        
  function( morphism )
    local P;
    
    P := ProsetOfCategory( CapCategory( morphism ) );
    
    return MorphismConstructor(
        P,
        ObjectConstructor( P, Source( morphism ) ),
        morphism,
        ObjectConstructor( P, Target( morphism ) )
    );
    
end );

##
InstallMethod( AsCellOfStableProset,
        "for a CAP morphism",
        [ IsCapCategoryMorphism ],
        
  function( morphism )
    local P;
    
    P := StableProsetOfCategory( CapCategory( morphism ) );
    
    return MorphismConstructor(
        P,
        ObjectConstructor( P, Source( morphism ) ),
        morphism,
        ObjectConstructor( P, Target( morphism ) )
    );
    
end );

##
InstallMethod( AsCellOfPoset,
        "for a CAP object",
        [ IsCapCategoryObject ],
        
  function( object )
    local P;
    
    P := PosetOfCategory( CapCategory( object ) );
    
    return ObjectConstructor( P, object );
    
end );

##
InstallMethod( AsCellOfStablePoset,
        "for a CAP object",
        [ IsCapCategoryObject ],
        
  function( object )
    local P;
    
    P := StablePosetOfCategory( CapCategory( object ) );
    
    return ObjectConstructor( P, object );
    
end );

##
InstallMethod( AsCellOfPoset,
        "for a CAP morphism",
        [ IsCapCategoryMorphism ],
        
  function( morphism )
    local P;
    
    P := PosetOfCategory( CapCategory( morphism ) );
    
    return MorphismConstructor(
        P,
        ObjectConstructor( P, Source( morphism ) ),
        morphism,
        ObjectConstructor( P, Target( morphism ) )
    );
    
end );

##
InstallMethod( AsCellOfStablePoset,
        "for a CAP morphism",
        [ IsCapCategoryMorphism ],
        
  function( morphism )
    local P;
    
    P := StablePosetOfCategory( CapCategory( morphism ) );
    
    return MorphismConstructor(
        P,
        ObjectConstructor( P, Source( morphism ) ),
        morphism,
        ObjectConstructor( P, Target( morphism ) )
    );
    
end );

##
InstallOtherMethod( \/,
        "for a CAP morphism and a proset or poset of a CAP category",
        [ IsCapCategoryMorphism, IsProsetOrPosetOfCapCategory ],
        
  function( morphism, P )
    
    return MorphismConstructor(
        P,
        ObjectConstructor( P, Source( morphism ) ),
        morphism,
        ObjectConstructor( P, Target( morphism ) )
    );
    
end );

##
InstallMethod( CreateProsetOrPosetOfCategory,
        "for a CAP category",
        [ IsCapCategory ],
        
  function( C )
    local skeletal, stable, category_filter, category_object_filter, category_morphism_filter,
          name, create_func_morphism,
          list_of_operations_to_install, skip, func, pos,
          properties, P, object_constructor, object_datum, morphism_constructor, morphism_datum,
          find_meets_and_joins, objects_of_poset, obj1, obj2;
    
    skeletal := CAP_INTERNAL_RETURN_OPTION_OR_DEFAULT( "skeletal", false );
    
    if IsIdenticalObj( skeletal, true ) then
        name := "PosetOfCategory";
        category_filter := IsPosetOfCapCategory;
        category_object_filter := IsObjectInPosetOfCategory;
        category_morphism_filter := IsMorphismInPosetOfCategory;
    else
        name := "ProsetOfCategory";
        category_filter := IsProsetOfCapCategory;
        category_object_filter := IsObjectInProsetOfCategory;
        category_morphism_filter := IsMorphismInProsetOfCategory;
    fi;
    
    stable := CAP_INTERNAL_RETURN_OPTION_OR_DEFAULT( "stable", false );
    
    if IsIdenticalObj( stable, true ) then
        
        if not (HasIsThinCategory( C ) and IsThinCategory( C )) then
            Error( "only compatible (co)closed monoidal structures of (co)cartesian *thin* categories can be stabilized\n" );
        fi;
        
        name := Concatenation( "Stable", name );
        category_object_filter := category_object_filter and IsCellInStableProsetOrPosetOfCategory;
        category_morphism_filter := category_morphism_filter and IsCellInStableProsetOrPosetOfCategory;
    fi;
    
    name := Concatenation( name, "( ", Name( C ), " )" );
    
    ## e.g., IdentityMorphism, PreCompose
    create_func_morphism :=
        function( name, P )
            
            return """
                function( input_arguments... )
                    
                    return UniqueMorphism( cat, top_source, top_range );
                    
                end
            """;
            
        end;
    
    list_of_operations_to_install := Intersection(
        CAP_INTERNAL_METHOD_NAME_LIST_FOR_PREORDERED_SET_OF_CATEGORY,
        ListInstalledOperationsOfCategory( C )
    );
    
    skip := [ 
              ];
    
    if IsIdenticalObj( stable, true ) then
        
        Append( list_of_operations_to_install, [ "IsTerminal" ] ); ## do not add "IsInitial"
        
        Append( skip,
                [ "IsHomSetInhabited",
                  "InternalHomOnObjects",
                  "InternalCoHomOnObjects",
                  "AreIsomorphicForObjectsIfIsHomSetInhabited",
                  ] );
    fi;
    
    for func in skip do
        
        pos := Position( list_of_operations_to_install, func );
        if not pos = fail then
            Remove( list_of_operations_to_install, pos );
        fi;
        
    od;
    
    properties := [ #"IsEnrichedOverCommutativeRegularSemigroup",
                    #"IsAbCategory",
                    "IsAdditiveCategory",
                    "IsPreAbelianCategory",
                    "IsAbelianCategory",
                    "IsMonoidalCategory",
                    "IsStrictMonoidalCategory",
                    "IsBraidedMonoidalCategory",
                    "IsSymmetricMonoidalCategory",
                    "IsClosedMonoidalCategory",
                    "IsCoclosedMonoidalCategory",
                    "IsSymmetricClosedMonoidalCategory",
                    "IsSymmetricCoclosedMonoidalCategory",
                    "IsCartesianCategory",
                    "IsStrictCartesianCategory",
                    "IsCartesianClosedCategory",
                    "IsCocartesianCategory",
                    "IsStrictCocartesianCategory",
                    "IsCocartesianCoclosedCategory",
                    ];
    
    properties := Intersection( ListKnownCategoricalProperties( C ), properties );
    
    properties := Filtered( properties, p -> ValueGlobal( p )( C ) );
    
    Add( properties, "IsThinCategory" );
    
    if IsIdenticalObj( stable, true ) then
        Add( properties, "IsStableProset" );
        if CanCompute( C, "InternalHomOnObjects" ) then
            Add( properties, "IsCartesianClosedCategory" );
        fi;
        if CanCompute( C, "InternalCoHomOnObjects" ) then
            Add( properties, "IsCocartesianCoclosedCategory" );
        fi;
    fi;
    
    if IsIdenticalObj( skeletal, true ) then
        
        Add( properties, "IsSkeletalCategory" );
        
        if HasIsCartesianCategory( C ) and IsCartesianCategory( C ) then
            Add( properties, "IsStrictCartesianCategory" );
        fi;
        
        if HasIsCocartesianCategory( C ) and IsCocartesianCategory( C ) then
            Add( properties, "IsStrictCocartesianCategory" );
        fi;
        
    else
        
        if HasIsCartesianCategory( C ) and IsCartesianCategory( C ) then
            Add( properties, "IsCartesianCategory" );
        fi;
        
        if HasIsCocartesianCategory( C ) and IsCocartesianCategory( C ) then
            Add( properties, "IsCocartesianCategory" );
        fi;
        
    fi;
    
    ##
    object_constructor := function( cat, underlying_object )
        
        #% CAP_JIT_DROP_NEXT_STATEMENT
        CAP_INTERNAL_ASSERT_IS_OBJECT_OF_CATEGORY( underlying_object, AmbientCategory( cat ), [ "the object datum given to the object constructor of <cat>" ] );
        
        return CreateCapCategoryObjectWithAttributes( cat, UnderlyingCell, underlying_object );
        
    end;
    
    object_datum := { cat, object } -> UnderlyingCell( object );
    
    morphism_constructor := function( cat, source, underlying_morphism, range )
        
        #% CAP_JIT_DROP_NEXT_STATEMENT
        CAP_INTERNAL_ASSERT_IS_MORPHISM_OF_CATEGORY( underlying_morphism, AmbientCategory( cat ), [ "the morphism datum given to the morphism constructor of <cat>" ] );
        
        if IsEqualForObjects( AmbientCategory( cat ), Source( underlying_morphism ), UnderlyingCell( source ) ) = false then
            
            Error( "the source of the morphism datum must be equal to <UnderlyingCell( source )>" );
            
        fi;
        
        if IsEqualForObjects( AmbientCategory( cat ), Target( underlying_morphism ), UnderlyingCell( range ) ) = false then
            
            Error( "the range of the morphism datum must be equal to <UnderlyingCell( range )>" );
            
        fi;
        
        return CreateCapCategoryMorphismWithAttributes( cat, source, range, UnderlyingCell, underlying_morphism );
        
    end;
    
    morphism_datum := { cat, morphism } -> UnderlyingCell( morphism );
    
    P := CategoryConstructor( rec(
                 name := name,
                 category_filter := category_filter,
                 category_object_filter := category_object_filter,
                 category_morphism_filter := category_morphism_filter,
                 properties := properties,
                 object_constructor := object_constructor,
                 object_datum := object_datum,
                 morphism_constructor := morphism_constructor,
                 morphism_datum := morphism_datum,
                 list_of_operations_to_install := list_of_operations_to_install,
                 underlying_category_getter_string := "AmbientCategory",
                 underlying_object_getter_string := "ObjectDatum",
                 underlying_morphism_getter_string := "MorphismDatum",
                 top_object_getter_string := "ObjectConstructor",
                 top_morphism_getter_string := "MorphismConstructor",
                 create_func_bool := "default",
                 create_func_object := "default",
                 create_func_morphism := create_func_morphism,
                 create_func_morphism_or_fail := "default"
                 ) );
    
    if ( HasIsObjectFiniteCategory and IsObjectFiniteCategory )( C ) then
        SetIsFiniteCategory( P, true );
    fi;
    
    ADD_COMMON_METHODS_FOR_PREORDERED_SETS( P );
    
    P!.compiler_hints.category_attribute_names := [
        "AmbientCategory",
        "ExistingMeets",
        "ExistingJoins",
        "BottomElement",
        "TopElement"
    ];
    
    SetAmbientCategory( P, C );
    
    if not skeletal and CanCompute( C, "IsEqualForObjects" ) then
        
        AddIsEqualForObjects( P,
          function( P, S, T )
            
            return IsEqualForObjects( AmbientCategory( P ), UnderlyingCell( S ), UnderlyingCell( T ) );
            
        end );
        
    fi;
    
    if skeletal and CanCompute( C, "IsHomSetInhabited" ) then
        
        AddIsEqualForObjects( P,
          function( P, S, T )
            
            return IsHomSetInhabited( AmbientCategory( P ), UnderlyingCell( S ), UnderlyingCell( T ) ) and IsHomSetInhabited( AmbientCategory( P ), UnderlyingCell( T ), UnderlyingCell( S ) );
            
        end );
        
        AddAreIsomorphicForObjectsIfIsHomSetInhabited( P,
          function( P, S, T )
            
            return IsHomSetInhabited( AmbientCategory( P ), UnderlyingCell( T ), UnderlyingCell( S ) );
            
        end );
        
    fi;
    
    if CanCompute( C, "SetOfObjectsOfCategory" ) then
        
        if skeletal then
            
            AddSetOfObjectsOfCategory( P,
              function( P )
                
                return DuplicateFreeList( List( SetOfObjects( AmbientCategory( P ) ), o -> ObjectConstructor( P, o ) ) );
                
            end );
            
        else
            
            AddSetOfObjectsOfCategory( P,
              function( P )
                
                return List( SetOfObjects( AmbientCategory( P ) ), o -> ObjectConstructor( P, o ) );
                
            end );
            
        fi;
        
    fi;
    
    find_meets_and_joins := CAP_INTERNAL_RETURN_OPTION_OR_DEFAULT( "find_meets_and_joins", false );
    
    if IsIdenticalObj( find_meets_and_joins, true ) then
        
        if not IsFiniteCategory( P ) then
            
            Error( "Can only compute meets and joins in finite posets." );
            
        fi;
        
        if not CanCompute( P, "IsHomSetInhabited" ) then
            
            Error( "Can not compute the preorder." );
            
        fi;
        
        FIND_EXISTING_MEETS_OF_FINITE_POSET( P );
        
        FIND_EXISTING_JOINS_OF_FINITE_POSET( P );
        
    fi;
    
    if HasIsMeetSemiLattice( P ) and IsMeetSemiLattice( P ) then
        
        AddDirectProduct( P,
          function( Poset, l )
            local existing_meets;
            
            existing_meets := ExistingMeets( Poset );
            
            return Iterated( l, { A, B } -> LookupDictionary( existing_meets, [ A, B ] ) );
            
        end );
        
        AddProjectionInFactorOfDirectProductWithGivenDirectProduct( P,
          function( Poset, D, k, P )
            
            return UniqueMorphism( Poset, P, D[k] );
            
        end );
        
        AddUniversalMorphismIntoDirectProductWithGivenDirectProduct( P,
          function( Poset, D, T, tau, P )
            
            return UniqueMorphism( Poset, T, P);
            
        end );
        
        # The empty meet
        AddTerminalObject( P,
          function( Poset )
            
            return TopElement( Poset );
            
        end );
        
    fi;
        
    if HasIsJoinSemiLattice( P ) and IsJoinSemiLattice( P ) then
        
        AddCoproduct( P,
          function( Poset, l )
            local existing_joins;
            
            existing_joins := ExistingJoins( Poset );
            
            return Iterated( l, { A, B } -> LookupDictionary( existing_joins, [ A, B ] ) );
            
        end );
        
        AddInjectionOfCofactorOfCoproductWithGivenCoproduct( P,
          function( Poset, D, k, I )
            
            return UniqueMorphism( Poset, D[k], I);
            
        end );
        
        AddUniversalMorphismFromCoproductWithGivenCoproduct( P,
          function( Poset, D, T, tau, I )
            
            return UniqueMorphism( Poset, I, T );
            
        end );
        
        # The empty join
        AddInitialObject( P,
          function( Poset )
            
            return BottomElement( Poset );
            
        end );
        
    fi;
    
    if CAP_INTERNAL_RETURN_OPTION_OR_DEFAULT( "check_distributivity", false ) then
    
        if ( HasIsMeetSemiLattice( P ) and IsMeetSemiLattice( P ) ) and
           ( HasIsJoinSemiLattice( P ) and IsJoinSemiLattice( P ) ) then
            
            SetIsLattice( P, true );
            
            CHECK_IF_LATTICE_IS_DISTRIBUTIVE( P );
            
        fi;
        
    fi;
    
    if CanCompute( C, "MorphismsOfExternalHom" ) then
        
        ##
        AddMorphismsOfExternalHom( P,
          function( P, S, T )
            local mors;
            
            mors := MorphismsOfExternalHom( AmbientCategory( P ),
                            UnderlyingCell( S ),
                            UnderlyingCell( T ) );
            
            ## a trick to avoid an if/else statement (see ?CompilerForCAP:Requirements):
            mors := mors{[ 1 .. 1 - 0 ^ Length( mors ) ]};
            
            return List( mors, mor ->
                         MorphismConstructor( P,
                                 S,
                                 mor,
                                 T ) );
            
        end );
        
    fi;
    
    if not skeletal and CanCompute( C, "SetOfGeneratingMorphismsOfCategory" ) then
        
        AddSetOfGeneratingMorphismsOfCategory( P,
          function( P )
            
            return List( SetOfGeneratingMorphisms( AmbientCategory( P ) ), m ->
                         MorphismConstructor( P,
                                 ObjectConstructor( P, Source( m ) ),
                                 m,
                                 ObjectConstructor( P, Target( m ) ) ) );
            
        end );
        
    fi;
    
    if CanCompute( C, "IsWeakTerminal" ) then
        
        AddIsTerminal( P,
          function( P, S )
            
            return IsWeakTerminal( AmbientCategory( P ), UnderlyingCell( S ) );
            
        end );
        
    fi;
    
    if CanCompute( C, "IsWeakInitial" ) then
        
        AddIsInitial( P,
          function( P, S )
            
            return IsWeakInitial( AmbientCategory( P ), UnderlyingCell( S ) );
            
        end );
        
    fi;
    
    if IsIdenticalObj( stable, true ) then
        if CanCompute( C, "InternalHomOnObjects" ) then
            
            if IsIdenticalObj( skeletal, true ) then
                SetIsHeytingAlgebra( P, true );
            else
                SetIsHeytingAlgebroid( P, true );
            fi;
            
            ##
            AddInternalHomOnObjects( P,
              function( P, S, T )
                
                return ObjectConstructor( P, StableInternalHom( AmbientCategory( P ), UnderlyingCell( S ), UnderlyingCell( T ) ) );
                
            end );
            
            ## InternalHomOnMorphismsWithGivenInternalHoms is passed from the ambient Heyting algebra,
            ## its source are and target are not identical but equal to above (altered) internal Hom
            
            ##
            AddExponentialOnObjects( P,
              { P, S, T } -> InternalHomOnObjects( P, S, T ) );
            
        fi;
        
        if CanCompute( C, "InternalCoHomOnObjects" ) then
            
            if IsIdenticalObj( skeletal, true ) then
                SetIsCoHeytingAlgebra( P, true );
            else
                SetIsCoHeytingAlgebra( P, true );
            fi;
            
            ##
            AddInternalCoHomOnObjects( P,
              function( P, S, T )
                
                return ObjectConstructor( P, StableInternalCoHom( AmbientCategory( P ), UnderlyingCell( S ), UnderlyingCell( T ) ) );
                
            end );
            
            ## InternalCoHomOnMorphismsWithGivenInternalCoHoms is passed from the ambient co-Heyting algebra,
            ## its source are and target are not identical but equal to above (altered) internal CoHom
            
            ##
            AddCoexponentialOnObjects( P,
              { P, S, T } -> InternalCoHomOnObjects( P, S, T ) );
            
        fi;
        
    fi;
    
    Finalize( P );
    
    return P;
    
end );

##
InstallMethod( FIND_EXISTING_MEETS_OF_FINITE_POSET,
        "for a finite poset",
        [ IsPosetCategory and IsFiniteCategory ],
        
  function( P )
    local objects, obj, obj1, obj2, subset, possible_meets, confirmed_meets, meet, P_has_all_meets, P_has_a_top;
    
    objects := SetOfObjectsOfCategory( P );
    
    possible_meets := [];
    confirmed_meets := NewDictionary( IsList, true );
    
    P_has_all_meets := true;
    
    for subset in IteratorOfCombinations( objects ) do
        
        # Find all elements below subset; these are the possible meets.
        for obj in objects do
            
            if ForAll( subset, s -> IsHomSetInhabited( P, obj, s ) ) then
                
                Add( possible_meets, obj );
                
            fi;
            
        od;
        
        if possible_meets = [] then
            # No candidates for a meet were found
            
            P_has_all_meets := false;
            
            continue;
            
        fi;
        
        # Find the greatest element among all possible meets
        for meet in possible_meets do
            
            if ForAll( possible_meets, m -> IsHomSetInhabited( P, m, meet ) ) then
                
                for obj in Arrangements( subset, Length( subset ) ) do
                    
                    AddDictionary( confirmed_meets, obj, meet );
                    
                od;
                
                break;
                
            fi;
            
        od;
        
        if LookupDictionary( confirmed_meets, subset ) = fail then
            # No greatest meet was found
            
            P_has_all_meets := false;
            
        fi;
        
        possible_meets := [];
        
    od;
    
    # Add the meets: A x A = A
    # for obj in objects do
        
    #     AddDictionary( confirmed_meets, [ obj, obj ], obj );
        
    # od;
    
    SetExistingMeets( P, confirmed_meets );
    
    # Find the top element (= empty meet)
    
    P_has_a_top := false;
    
    for obj1 in objects do
        
        if ForAll( objects, obj2 -> IsHomSetInhabited( P, obj2, obj1 ) ) then
            
            SetTopElement( P, obj1 );
            
            P_has_a_top := true;
            
            break;
            
        fi;
        
    od;
    
    if P_has_all_meets and P_has_a_top then
        
        SetIsMeetSemiLattice( P, true );
        
    fi;
end );

##
InstallMethod( FIND_EXISTING_JOINS_OF_FINITE_POSET,
        "for a finite poset",
        [ IsPosetCategory and IsFiniteCategory ],
        
  function( P )
    local objects, obj, obj1, obj2, subset, possible_joins, confirmed_joins, join, P_has_all_joins, P_has_a_bottom ;
    
    objects := SetOfObjectsOfCategory( P );
    
    possible_joins := [];
    confirmed_joins := NewDictionary( IsList, true );
    
    P_has_all_joins := true;
    
    for subset in IteratorOfCombinations( objects ) do
        
        # Find all elements above subset; these are the possible joins.
        for obj in objects do
            
            if ForAll( subset, s -> IsHomSetInhabited( P, s, obj ) ) then
                
                Add( possible_joins, obj );
                
            fi;
            
        od;
        
        if possible_joins = [] then
          # No candidates for a join were found
          
          P_has_all_joins := false;
          
          continue;
          
        fi;
        
        # Find the smallest element among all possible joins
        for join in possible_joins do
            
            if ForAll( possible_joins, m -> IsHomSetInhabited( P, join, m ) ) then
                
                for obj in Arrangements( subset, Length( subset ) ) do
                    
                    AddDictionary( confirmed_joins, obj, join );
                    
                od;
                
                break;
                
            fi;
            
        od;
        
        if LookupDictionary( confirmed_joins, subset ) = fail then
          # No smallest join was found
          
          P_has_all_joins := false;
          
        fi;
        
        possible_joins := [];
        
    od;
    
    # Add the joins: A + A = A
    # for obj in objects do
        
    #     AddDictionary( confirmed_joins, [ obj, obj ], obj );
        
    # od;
    
    SetExistingJoins( P, confirmed_joins );
    
    # Find the bottom element (= empty join)
    
    P_has_a_bottom := false;
    
    for obj1 in objects do
        
        if ForAll( objects, obj2 -> IsHomSetInhabited( P, obj1, obj2 ) ) then
            
            SetBottomElement( P, obj1 );
            
            P_has_a_bottom := true;
            
            break;
            
        fi;
        
    od;
    
    if P_has_all_joins and P_has_a_bottom then
        
        SetIsJoinSemiLattice( P, true );
        
    fi;
    
end );

##
InstallMethod( CHECK_IF_LATTICE_IS_DISTRIBUTIVE,
        "for a finite lattice",
        [ IsLattice and IsFiniteCategory ],
        
  function( P )
    local is_distributive, subset, lhs, rhs;
    
    is_distributive := true;
        
    for subset in Arrangements( SetOfObjectsOfCategory( P ), 3 ) do
        
        # lhs := a ∧ (b ∨ c)
        lhs := DirectProduct( P, [ subset[1], Coproduct( P, [ subset[2], subset[3] ] ) ] );
        
        # rhs := (a ∧ b) ∨ (a ∧ c)
        rhs := Coproduct( P, [ DirectProduct( P, [ subset[1], subset[2] ] ), DirectProduct( P, [ subset[1], subset[3] ] ) ] );
        
        if not IsEqualForObjects( P, lhs, rhs ) then
            
            is_distributive := false;
            
            # Display( "Not a distributive lattice because of i.e.: ");
            # Display( subset );
            
            break;
            
        fi;
        
    od;
    
    if is_distributive then
        
        SetIsDistributiveLattice( P, true );
        
    fi;
    
end );

##
InstallMethod( ProsetOfCategory,
        "for a CAP category",
        [ IsCapCategory ],
        
  CreateProsetOrPosetOfCategory );

##
InstallMethod( PosetOfCategory,
        "for a CAP category",
        [ IsCapCategory ],
        
  function( C )
    
    return CreateProsetOrPosetOfCategory( C : skeletal := true );
    
end );

##
InstallMethod( StableProsetOfCategory,
        "for a CAP category",
        [ IsCapCategory ],
        
  function( C )
    
    return ProsetOfCategory( C : stable := true );
    
end );

##
InstallMethod( StablePosetOfCategory,
        "for a CAP category",
        [ IsCapCategory ],
        
  function( C )
    
    return PosetOfCategory( C : stable := true );
    
end );

##
InstallMethodForCompilerForCAP( SetOfObjects,
        "for a proset or poset of a CAP category",
        [ IsProsetOrPosetOfCapCategory ],
        
  function( cat )
    
    return SetOfObjectsOfCategory( cat );
    
end );

##
InstallMethodForCompilerForCAP( SetOfGeneratingMorphisms,
        "for a proset or poset of a CAP category",
        [ IsProsetOrPosetOfCapCategory ],
        
  function( cat )
    
    return SetOfGeneratingMorphismsOfCategory( cat );
    
end );

##
InstallMethod( \.,
        "for a proset or poset of a CAP category and a positive integer",
        [ IsProsetOrPosetOfCapCategory, IsPosInt ],
        
  function( P, string_as_int )
    local name, C, cell;
    
    name := NameRNam( string_as_int );
    
    C := AmbientCategory( P );
    
    cell := C.(name);
    
    if IsCapCategoryObject( cell ) then
        
        return ObjectConstructor( P, cell );
        
    elif IsCapCategoryMorphism( cell ) then
        
        return MorphismConstructor( P,
                       ObjectConstructor( P, Source( cell ) ),
                       cell,
                       ObjectConstructor( P, Target( cell ) ) );
        
    fi;
    
    Error( "<cell> is neither an object nor a morphism in the ambient category <C>" );
    
end );

##
InstallMethod( DefiningTripleOfUnderlyingQuiver,
        "for a proset or poset of a CAP category",
        [ IsProsetOrPosetOfCapCategory ],
        
  function( P )
    
    return DefiningTripleOfUnderlyingQuiver( AmbientCategory( P ) );
    
end );

##################################
##
## View & Display
##
##################################

##
InstallMethod( ViewString,
        [ IsObjectInProsetOfCategory ],
        
  function( a )
    
    return Concatenation( "An object in the proset given by: ",
                   StringView( UnderlyingCell( a ) ) );
    
end );

##
InstallMethod( PrintString,
        [ IsObjectInProsetOfCategory ],
        
  StringView );

##
InstallMethod( ViewString,
        [ IsMorphismInProsetOfCategory and HasUnderlyingCell ],
        
  function( mor )
    
    return Concatenation( "A morphism in the proset given by: ",
                   StringView( UnderlyingCell( mor ) ) );
    
end );

##
InstallMethod( PrintString,
        [ IsMorphismInProsetOfCategory ],
        
  StringView );

##
InstallMethod( ViewString,
        [ IsObjectInProsetOfCategory and IsCellInStableProsetOrPosetOfCategory ],
        
  function( a )
    
    return Concatenation( "An object in the stable proset given by: ",
                   StringView( UnderlyingCell( a ) ) );
    
end );

##
InstallMethod( ViewString,
        [ IsMorphismInProsetOfCategory and IsCellInStableProsetOrPosetOfCategory and HasUnderlyingCell ],
        
  function( mor )
    
    return Concatenation( "A morphism in the stable proset given by: ",
                   StringView( UnderlyingCell( mor ) ) );
    
end );

##
InstallMethod( DisplayString,
        [ IsObjectInProsetOfCategory ],
        
  function( a )
    
    return Concatenation( StringDisplay( UnderlyingCell( a ) ),
                   "\nAn object in the proset given by the above data" );
    
end );

##
InstallMethod( DisplayString,
        [ IsObjectInProsetOfCategory and IsCellInStableProsetOrPosetOfCategory ],
        
  function( a )
    
    return Concatenation( StringDisplay( UnderlyingCell( a ) ),
                   "\nAn object in the stable proset given by the above data" );
    
end );

##
InstallMethod( ViewString,
        [ IsObjectInPosetOfCategory ],
        
  function( a )
    
    return Concatenation( "An object in the poset given by: ",
                   StringView( UnderlyingCell( a ) ) );
    
end );

##
InstallMethod( PrintString,
        [ IsObjectInPosetOfCategory ],
        
  StringView );

##
InstallMethod( ViewString,
        [ IsMorphismInPosetOfCategory and HasUnderlyingCell ],
        
  function( mor )
    
    return Concatenation( "A morphism in the poset given by: ",
                   StringView( UnderlyingCell( mor ) ) );
    
end );

##
InstallMethod( PrintString,
        [ IsMorphismInPosetOfCategory ],
        
  StringView );

##
InstallMethod( ViewString,
        [ IsObjectInPosetOfCategory and IsCellInStableProsetOrPosetOfCategory ],
        
  function( a )
    
    return Concatenation( "An object in the stable poset given by: ",
                   StringView( UnderlyingCell( a ) ) );
    
end );

##
InstallMethod( ViewString,
        [ IsMorphismInPosetOfCategory and IsCellInStableProsetOrPosetOfCategory and HasUnderlyingCell ],
        
  function( mor )
    
    return Concatenation( "A morphism in the stable poset given by: ",
                   StringView( UnderlyingCell( mor ) ) );
    
end );

##
InstallMethod( DisplayString,
        [ IsObjectInPosetOfCategory ],
        
  function( a )
    
    return Concatenation( StringDisplay( UnderlyingCell( a ) ),
                   "\nAn object in the poset given by the above data" );
    
end );

##
InstallMethod( DisplayString,
        [ IsObjectInPosetOfCategory and IsCellInStableProsetOrPosetOfCategory ],
        
  function( a )
    
    return Concatenation( StringDisplay( UnderlyingCell( a ) ),
                   "\nAn object in the stable poset given by the above data" );
    
end );
