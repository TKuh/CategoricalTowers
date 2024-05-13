LoadPackage( "SubcategoriesForCap", false );;
LoadPackage( "Locales", false );;

DeclareAttribute( "AddPossibleLatticeOperations",
        IsPosetOfCapCategory and IsFiniteCategory );

InstallMethod( AddPossibleLatticeOperations,
        "for a poset",
        [ IsPosetOfCapCategory and IsFiniteCategory ],
        
  function ( P )
    local L, objects, obj, subset, possible_meets, confirmed_meets, meet, L_is_a_meet_semilattice,
          possible_joins, confirmed_joins, join, L_is_a_join_semilattice, bottom, top, A, lhs, rhs, L_is_distributive;
    
    L := Subcategory( P, Concatenation( "LatticeOperations( ", Name( P ), " )" ) : is_full := true, FinalizeCategory := false );
    
    L!.ObjectMembershipFunction := ReturnTrue;
    
    objects := SetOfObjectsOfCategory( P );
    
    #######################################
    #
    # Find all existing meets (= products)
    #
    #######################################
    
    possible_meets := [];
    confirmed_meets := NewDictionary( IsList, true );
    L_is_a_meet_semilattice := true;
    
    SetIsPosetCategory( L, true );
    
    for subset in Tuples( objects, 2 ) do
        
        # Find all elements below subset[1] and subset[2], these are the possible joins.
        for obj in objects do
            
            if IsHomSetInhabited( P, obj, subset[1] ) and IsHomSetInhabited( P, obj, subset[2] ) then
                
                Add( possible_meets, obj );
                
            fi;
            
        od;
        
        if possible_meets = [] then
            # No candidates for a meet were found
            
            L_is_a_meet_semilattice := false;
            
            break;
            
        fi;
        
        subset := List( subset, a -> AsSubcategoryCell( L, a ) );
        
        # Find the greatest element among all possible meets
        for meet in possible_meets do
            
            if ForAll( possible_meets, m -> IsHomSetInhabited( P, m, meet ) ) then
                
                AddDictionary( confirmed_meets, subset, AsSubcategoryCell( L, meet ) );
                
                break;
                
            fi;
            
        od;
        
        if LookupDictionary( confirmed_meets, subset ) = false then
            # No greatest meet was found
            
            L_is_a_meet_semilattice := false;
            
            break;
            
        fi;
        
        possible_meets := [];
        
    od;
    
    # Find all existing joins (= coproducts)
    
    possible_joins := [];
    confirmed_joins := NewDictionary( IsList, true );
    L_is_a_join_semilattice := true;
    
    for subset in Tuples( objects, 2 ) do
        
        # Find all elements below subset[1] and subset[2], these are the possible joins.
        for obj in objects do
            
            if IsHomSetInhabited( P, subset[1], obj ) and IsHomSetInhabited( P, subset[2], obj ) then
                
                Add( possible_joins, obj );
                
            fi;
            
        od;
        
        if possible_joins = [] then
          # No candidates for a join were found
          
          L_is_a_join_semilattice := false;
          
          break;
          
        fi;
        
        subset := List( subset, a -> AsSubcategoryCell( L, a ) );
        
        # Find the smallest element among all possible joins
        for join in possible_joins do
            
            if ForAll( possible_joins, m -> IsHomSetInhabited( P, join, m ) ) then
                
                AddDictionary( confirmed_joins, subset, AsSubcategoryCell( L, join ) );
                
                break;
                
            fi;
            
        od;
        
        if LookupDictionary( confirmed_joins, subset ) = false then
          # No smallest join was found
          
          L_is_a_join_semilattice := false;
          
          break;
          
        fi;
        
        possible_joins := [];
        
    od;
    
    if L_is_a_meet_semilattice then
        
        SetIsMeetSemiLattice( L, true );
        
    fi;
    
    if L_is_a_join_semilattice then
        
        SetIsJoinSemiLattice( L, true );
        
    fi;
    
    if L_is_a_meet_semilattice and L_is_a_join_semilattice then
        
        SetIsLattice( L, true );
        
        # Check if L is also distributive
        L_is_distributive := true;
        
        for subset in Tuples( objects, 3 ) do
            
            subset := List( subset, a -> AsSubcategoryCell( L, a ) );
            
            lhs := LookupDictionary( confirmed_meets, [ subset[1], LookupDictionary( confirmed_joins, [ subset[2], subset[3] ] ) ] );
            rhs := LookupDictionary( confirmed_joins, [ LookupDictionary( confirmed_meets, [ subset[1], subset[2] ] ),
                                                        LookupDictionary( confirmed_meets, [ subset[1], subset[3] ] ) ] );
            
            if not IsEqualForObjects( P, UnderlyingCell( lhs ), UnderlyingCell( rhs ) ) then
                
                L_is_distributive := false;
                
                Display( "Not a distributive lattice because of i.e.: ");
                Display( subset );
                
                break;
                
            fi;
            
        od;
        
        if L_is_distributive then
            
            SetIsDistributiveLattice( L, true );
            
        fi;
        
    fi;
     
    ########################################
    #
    # Add methods
    #
    ########################################
    
    AddIsHomSetInhabited( L,
      { Poset, A, B } -> IsHomSetInhabited( AmbientCategory( Poset ), UnderlyingCell( A ), UnderlyingCell( B ) ) );
    
    # Search for a bottom element (= initial object)
    
    for obj in objects do
        
        if ForAll( objects, a -> IsHomSetInhabited( P, obj, a) ) then
            
            bottom := obj;
            
            AddInitialObject( L,
              function( Poset )
                  
                  return AsSubcategoryCell( Poset, bottom );
                  
            end );
            
            break;
            
        fi;
        
    od;
    
    # Search for a top element (= terminal object)
    
    for obj in objects do
        
        if ForAll( objects, a -> IsHomSetInhabited( P, a, obj ) ) then
            
            top := obj;
            
            AddTerminalObject( L,
              function( Poset )
                  
                  return AsSubcategoryCell( Poset, top );
                  
            end );
            
            break;
            
        fi;
        
    od;
    
    # Add meets (= products)
    
    if L_is_a_meet_semilattice then
        
        # Add the meets: A x A = A
        for A in objects do
            
            AddDictionary( confirmed_meets,
                           [ AsSubcategoryCell( L, A ), AsSubcategoryCell( L, A ) ],
                           AsSubcategoryCell( L, A ) );
            
        od;
        
        AddDirectProduct( L,
          function( Poset, l )
              
              return Iterated( l, { A, B } -> LookupDictionary( confirmed_meets, [ A, B ] ) );
              
        end );
        
        AddProjectionInFactorOfDirectProductWithGivenDirectProduct( L,
          function( Poset, D, k, P )
            
              return UniqueMorphism( Poset, P, D[k] );
            
        end );

        AddUniversalMorphismIntoDirectProductWithGivenDirectProduct( L,
         
          function( Poset, D, T, tau, P )
            
              return UniqueMorphism( Poset, T, P);
            
        end );
        
    fi;
    
    # Add joins (= coproducts)
    
    if L_is_a_join_semilattice then
        
        # Add the joins: A + A = A
        for A in objects do
            
            AddDictionary( confirmed_joins,
                           [ AsSubcategoryCell( L, A ), AsSubcategoryCell( L, A ) ],
                           AsSubcategoryCell( L, A ) );
            
        od;
        
        AddCoproduct( L,
          function( Poset, l )
              
              return Iterated( l, { A, B } -> LookupDictionary( confirmed_joins, [ A, B ] ) );
              
        end );
        
        AddInjectionOfCofactorOfCoproductWithGivenCoproduct( L,
          function( Poset, D, k, I )
            
              return UniqueMorphism( Poset, D[k], I);
            
        end );

        AddUniversalMorphismFromCoproductWithGivenCoproduct( L,
         
          function( Poset, D, T, tau, I )
            
              return UniqueMorphism( Poset, I, T );
            
        end );
        
    fi;
    
    Finalize( L );
    
    return L;
    
end );

