# SPDX-License-Identifier: GPL-2.0-or-later
# Locales: Locales, frames, coframes, meet semi-lattices of locally closed subsets, and Boolean algebras of constructible sets
#
# Implementations
#

InstallTrueMethod( IsPosetCategory, IsThinCategory and IsSkeletalCategory );
InstallTrueMethod( IsThinCategory, IsPosetCategory );
InstallTrueMethod( IsSkeletalCategory, IsPosetCategory );

InstallTrueMethod( IsPosetCategory, IsTotalOrderCategory );

InstallTrueMethod( IsMonoidalPoset, IsPosetCategory and IsStrictMonoidalCategory );
InstallTrueMethod( IsPosetCategory, IsMonoidalPoset );
InstallTrueMethod( IsStrictMonoidalCategory, IsMonoidalPoset );

InstallTrueMethod( IsClosedMonoidalPoset, IsMonoidalPoset and IsClosedMonoidalCategory );
InstallTrueMethod( IsMonoidalPoset, IsClosedMonoidalPoset );
InstallTrueMethod( IsClosedMonoidalCategory, IsClosedMonoidalPoset );

InstallTrueMethod( IsCoclosedMonoidalPoset, IsMonoidalPoset and IsCoclosedMonoidalCategory );
InstallTrueMethod( IsMonoidalPoset, IsCoclosedMonoidalPoset );
InstallTrueMethod( IsCoclosedMonoidalCategory, IsCoclosedMonoidalPoset );

InstallTrueMethod( IsSymmetricMonoidalPoset, IsPosetCategory and IsStrictMonoidalCategory and IsSymmetricMonoidalCategory );
InstallTrueMethod( IsPosetCategory, IsSymmetricMonoidalPoset );
InstallTrueMethod( IsStrictMonoidalCategory, IsSymmetricMonoidalPoset );
InstallTrueMethod( IsSymmetricMonoidalCategory, IsSymmetricMonoidalPoset );

InstallTrueMethod( IsSymmetricClosedMonoidalPoset, IsSymmetricMonoidalPoset and IsSymmetricClosedMonoidalCategory );
InstallTrueMethod( IsSymmetricMonoidalPoset, IsSymmetricClosedMonoidalPoset );
InstallTrueMethod( IsSymmetricClosedMonoidalCategory, IsSymmetricClosedMonoidalPoset );

InstallTrueMethod( IsSymmetricCoclosedMonoidalPoset, IsSymmetricMonoidalPoset and IsSymmetricCoclosedMonoidalCategory );
InstallTrueMethod( IsSymmetricMonoidalPoset, IsSymmetricCoclosedMonoidalPoset );
InstallTrueMethod( IsSymmetricCoclosedMonoidalCategory, IsSymmetricCoclosedMonoidalPoset );

##
InstallMethod( \<,
        "for two objects in a thin category",
        [ IsObjectInThinCategory, IsObjectInThinCategory ],
        
  function( A, B )
    local C;
    
    C := CapCategory( A );
    
    if not ( HasIsSkeletalCategory( C ) and IsSkeletalCategory( C ) ) then
        TryNextMethod( );
    elif not IsIdenticalObj( C, CapCategory( B ) ) then
        TryNextMethod( );
    fi;
    
    return IsHomSetInhabited( A, B ) and not AreIsomorphicForObjectsIfIsHomSetInhabited( A, B );
    
end );

InstallMethod( RelativeMeet,
        "for a finite poset",
        [ IsPosetCategory and IsFiniteCategory, IsList, IsList ],
        
  function( P, l, excluded_meets )
    local existing_meets;
    
    if l in excluded_meets then
        
        return fail;
        
    fi;
    
    existing_meets := ExistingMeets( P );
    
    return LookupDictionary( existing_meets, l );
    
end );

InstallMethod( RelativeJoin,
        "for a finite poset",
        [ IsPosetCategory and IsFiniteCategory, IsList, IsList ],
        
  function( P, l, excluded_joins )
    local existing_joins;
    
    if l in excluded_joins then
        
        return fail;
        
    fi;
    
    existing_joins := ExistingJoins( P );
    
    return LookupDictionary( existing_joins, l );
    
end );

InstallMethod( UpSets,
        "for a finite poset",
        [ IsPosetCategory and IsFiniteCategory ],
        
  function( P )
    local poset, confirmed_upsets, subset, upsets_of_elements;
    
    poset := SetOfObjectsOfCategory( P );
    confirmed_upsets := [];
    
    for subset in IteratorOfCombinations( poset ) do
        
        if IsEmpty( subset ) then continue; fi;
        
        upsets_of_elements := List( subset, i -> Filtered( poset, a -> IsHomSetInhabited( P, i, a ) ) );
        
        if ForAll( upsets_of_elements, up -> ForAll( up, a -> a in subset ) ) then
            
            Add( confirmed_upsets, subset );
            
        fi;
        
    od;
    
    return confirmed_upsets;
    
end );

InstallOtherMethod( UpSetsAsDistributiveExtension,
        "for a finite list",
        [ IsList ],
        
  function( relative_prime_filters )
    local poset, confirmed_upsets, contains, subset_of_relative_prime_filters, upsets_of_elements;
    
    confirmed_upsets := [];
    
    contains := { filter1, filter2 } -> ForAll( filter1, element -> element in filter2 );;
    
    for subset_of_relative_prime_filters in IteratorOfCombinations( relative_prime_filters ) do
        
        # if IsEmpty( subset_of_relative_prime_filters ) then continue; fi;
        
        upsets_of_elements := List( subset_of_relative_prime_filters, i -> Filtered( relative_prime_filters, a -> contains( i, a ) ) ); # i ⊂ a
        
        if ForAll( upsets_of_elements, up -> ForAll( up, a -> a in subset_of_relative_prime_filters ) ) then
            
            Add( confirmed_upsets, subset_of_relative_prime_filters );
            
        fi;
        
    od;
    
    return confirmed_upsets;
    
end );

InstallMethod( EmbeddingInDistributiveExtension,
        "for a finite list, an element and a comparison function",
        [ IsList, IsObject ],
        
  function( filters, object )
    local upset;
    
    upset := Filtered( filters, filter -> object in filter );
    
    return upset;
    
end );

InstallMethod( DownSets,
        "for a finite poset",
        [ IsPosetCategory and IsFiniteCategory ],
        
  function( P )
    local poset, confirmed_downsets, subset, downsets_of_elements;
    
    poset := SetOfObjectsOfCategory( P );
    confirmed_downsets := [];
    
    for subset in IteratorOfCombinations( poset ) do
        
        if IsEmpty( subset ) then continue; fi;
        
        downsets_of_elements := List( subset, i -> Filtered( poset, a -> IsHomSetInhabited( P, a, i ) ) );
        
        if ForAll( downsets_of_elements, down -> ForAll( down, a -> a in subset ) ) then
            
            Add( confirmed_downsets, subset );
            
        fi;
        
    od;
    
    return confirmed_downsets;
    
end );

InstallMethod( RelativeFiltersOfPoset,
        "for a finite poset",
        [ IsPosetCategory and IsFiniteCategory, IsList ],
        
  function( P, excluded_meets )
    local upsets, filters;
    
    upsets := UpSets( P );
    
    filters := Filtered( upsets, up -> ForAll( Combinations( up, 2 ), c -> RelativeMeet( P, c, excluded_meets ) = fail or RelativeMeet( P, c, excluded_meets ) in up ) );
    
    return filters;
    
end );

InstallMethod( RelativeIdealsOfPoset,
        "for a finite poset",
        [ IsPosetCategory and IsFiniteCategory, IsList ],
        
  function( P, excluded_joins )
    local downsets, filters;
    
    downsets := DownSets( P );
    
    filters := Filtered( downsets, down -> ForAll( Combinations( down, 2 ), c -> RelativeJoin( P, c, excluded_joins ) = fail or RelativeJoin( P, c, excluded_joins ) in down ) );
    
    return filters;
    
end );

InstallMethod( RelativePrimeFiltersOfPoset,
        "for a finite poset",
        [ IsPosetCategory and IsFiniteCategory, IsList, IsList ],
        
  function( P, excluded_meets, excluded_joins )
    local poset, relative_filters, relative_ideals, complement, contains, relative_primes_filters;
    
    poset := SetOfObjects( P );
    
    relative_filters := RelativeFiltersOfPoset( P, excluded_meets );
    relative_ideals := RelativeIdealsOfPoset( P, excluded_joins );
    
    complement := { set, subset } -> Filtered( set, a -> not ( a in subset ) );
    
    contains := { set_of_sets, set1 } -> ForAny( set_of_sets, set2 -> ForAll( set2, el -> el in set1 ) and
                                                                      ForAll( set1, el -> el in set2 ) );
    
    # A filter is prime iff its complement is an ideal.
    relative_primes_filters := Filtered( relative_filters,
                                         filter -> contains( relative_ideals, complement( poset, filter ) ) );
    
    return relative_primes_filters;
    
end );
