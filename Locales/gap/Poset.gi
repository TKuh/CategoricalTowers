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
        [ IsPosetCategory and IsFiniteCategory, IsList, IsDictionary ],
        
  function( P, meet, excluded_meets )
    local contains, existing_meets;
    
    if Length( meet ) < 2 then return fail; fi;
    
    # contains := { list_of_meets, meet } -> ForAny( list_of_meets,
    #                                                meet2 -> ForAll( meet2, m -> m in meet ) and ForAll( meet, m -> m in meet2 ) ); # meet2 ⊂ meet and meet ⊂ meet2
    
    # if contains( excluded_meets, meet ) then
        
    #     return fail;
        
    # fi;
    
    if KnowsDictionary( excluded_meets, meet ) = true then
        
        return fail;
        
    fi;
    
    existing_meets := ExistingMeets( P );
    
    return LookupDictionary( existing_meets, meet );
    
    # return Iterated( meet, { A, B } -> LookupDictionary( existing_meets, [ A, B ] ) );
    
    # return DirectProduct( P, meet ); # The poset is not neccesarily a meet-semilattice and DirectProduct might not be installed
    
end );

InstallMethod( RelativeJoin,
        "for a finite poset",
        [ IsPosetCategory and IsFiniteCategory, IsList, IsDictionary ],
        
  function( P, join, excluded_joins )
    local contains, existing_joins;
    
    if Length( join ) < 2 then return fail; fi;
    
    # contains := { list_of_joins, join } -> ForAny( list_of_joins,
    #                                                join2 -> ForAll( join2, j -> j in join ) and ForAll( join, j -> j in join2 ) ); # join2 ⊂ join and join ⊂ join2
    
    # if contains( excluded_joins, join ) then
        
    #     return fail;
        
    # fi;
    
    if KnowsDictionary( excluded_joins, join ) = true then
        
        return fail;
        
    fi;
    
    existing_joins := ExistingJoins( P );
    
    return LookupDictionary( existing_joins, join );
    
    # return Iterated( join, { A, B } -> LookupDictionary( existing_joins, [ A, B ] ) );
    
    # return Coproduct( P, join ); # The poset is not neccesarily a join-semilattice and DirectProduct might not be installed
    
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
        "for a finite list and an element ",
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
        [ IsPosetCategory and IsFiniteCategory, IsDictionary ],
        
  function( P, excluded_meets )
    local upsets, filters;
    
    upsets := UpSets( P );
    
    filters := Filtered( upsets, up -> ForAll( Combinations( up ),
                                               c -> RelativeMeet( P, c, excluded_meets ) = fail or
                                                    RelativeMeet( P, c, excluded_meets ) in up ) );
    
    return filters;
    
end );

InstallMethod( RelativeIdealsOfPoset,
        "for a finite poset",
        [ IsPosetCategory and IsFiniteCategory, IsDictionary ],
        
  function( P, excluded_joins )
    local downsets, filters;
    
    downsets := DownSets( P );
    
    filters := Filtered( downsets, down -> ForAll( Combinations( down ),
                                                   c -> RelativeJoin( P, c, excluded_joins ) = fail or
                                                        RelativeJoin( P, c, excluded_joins ) in down ) );
    
    return filters;
    
end );

InstallMethod( RelativePrimeFiltersOfPoset,
        "for a finite poset",
        [ IsPosetCategory and IsFiniteCategory, IsDictionary, IsDictionary ],
        
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
