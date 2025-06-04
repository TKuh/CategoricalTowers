# SPDX-License-Identifier: GPL-2.0-or-later
# FreydCategoriesForCAP: Freyd categories - Formal (co)kernels for additive categories
#
# Implementations
#

##
InstallMethod( AdditiveClosureOfObjectFiniteCategory,
               [ IsCapCategory ],
               ADDITIVE_CLOSURE_Of_OBJECT_FINITE_CATEGORY
);

##
InstallMethod( ADDITIVE_CLOSURE_Of_OBJECT_FINITE_CATEGORY,
               [ IsCapCategory ],
        
  FunctionWithNamedArguments(
  [
    [ "FinalizeCategory", true ],
  ],
  function( CAP_NAMED_ARGUMENTS, C )
    local object_datum_type, object_constructor, object_datum,
          morphism_datum_type, morphism_constructor, morphism_datum,
          AC,
          modeling_tower_object_constructor, modeling_tower_object_datum,
          modeling_tower_morphism_constructor, modeling_tower_morphism_datum,
          AC_objfin;
    
    Assert( 0, HasIsObjectFiniteCategory( C ) and IsObjectFiniteCategory( C ) and CanCompute( C, "SetOfObjectsOfCategory" ) );
    
    Assert( 0, HasIsAbCategory( C ) and IsAbCategory( C ) );
    
    ##
    object_datum_type := CapJitDataTypeOfNTupleOf( 2,
                                IsBigInt,
                                CapJitDataTypeOfListOf( IsBigInt ) );
    
    ##
    object_constructor :=
      function( AC_objfin, checksum_and_multiplicities )
        
        #% CAP_JIT_DROP_NEXT_STATEMENT
        Assert( 0,
                IsList( checksum_and_multiplicities ) and
                Length( checksum_and_multiplicities ) = 2 and
                IsList( checksum_and_multiplicities[2] ) );
        
        if checksum_and_multiplicities[1] <> Sum( checksum_and_multiplicities[2] ) then
            
            Error( "the first entry has to be the sum of all multiplicities" );
            
        fi;
        
        if Length( checksum_and_multiplicities[2] ) <> Length( SetOfObjectsOfCategory( C ) ) then
            
            Error( "the length of the multiplicities list has to be equal to the number of objects in the underlying category." );
            
        fi;
        
        return CreateCapCategoryObjectWithAttributes( AC_objfin,
                       ChecksumAndMultiplicities, checksum_and_multiplicities );
        
    end;
    
    ##
    object_datum := { AC_objfin, obj } -> ChecksumAndMultiplicities( obj );
    
    ##
    morphism_datum_type := CapJitDataTypeOfListOf(
                                  CapJitDataTypeOfListOf(
                                          CapJitDataTypeOfMorphismOfCategory( C ) ) );
   
    ##
    morphism_constructor :=
      function ( AC_objfin, S, morphism_matrix, T )
        
        #% CAP_JIT_DROP_NEXT_STATEMENT
        Assert( 0,
                IsList( morphism_matrix ) and
                Length( morphism_matrix ) = ChecksumAndMultiplicities( S )[1] and
                ForAll( morphism_matrix, row -> IsList( row ) and
                                                Length( row ) = ChecksumAndMultiplicities( T )[1] ) );
        
        return CreateCapCategoryMorphismWithAttributes( AC_objfin,
                       S,
                       T,
                       MorphismMatrix, morphism_matrix );
        
    end;
    
    ##
    morphism_datum := { AC_objfin, phi } -> MorphismMatrix( phi );
    
    ## Building the categorical tower:
    
    AC := AdditiveClosure( C : FinalizeCategory := true );
    
    ## From the raw object data to the object in the modeling category
    modeling_tower_object_constructor :=
      function( AC_objfin, checksum_and_multiplicities )
        local AC, objects, l, multiplicities;
        
        #% CAP_JIT_DROP_NEXT_STATEMENT
        Assert( 0,
                IsList( checksum_and_multiplicities ) and
                Length( checksum_and_multiplicities ) = 2 and
                IsList( checksum_and_multiplicities[2] ) );
        
        if checksum_and_multiplicities[1] <> Sum( checksum_and_multiplicities[2] ) then
            
            Error( "the first entry has to be the sum of all multiplicities" );
            
        fi;
        
        if Length( checksum_and_multiplicities[2] ) <> Length( SetOfObjectsOfCategory( C ) ) then
            
            Error( "the length of the multiplicities list has to be equal to the number of objects in the underlying category." );
            
        fi;
        
        AC := ModelingCategory( AC_objfin );
        
        objects := SetOfObjectsOfCategory( UnderlyingCategory( AC_objfin ) );
        
        l := NumberOfObjectsOfUnderlyingCategory( AC_objfin );
        
        multiplicities := checksum_and_multiplicities[2];
        
        return ObjectConstructor( AC,
                       Concatenation( List( [ 1 .. l ], i ->
                               ListWithIdenticalEntries( multiplicities[i], objects[i] ) ) ) );
        
    end;
    
    ## From the object in the modeling category to the raw object data
    modeling_tower_object_datum :=
      function( AC_objfin, objAC )
        local AC, C, objects, l, list_of_objects;
        
        AC := ModelingCategory( AC_objfin );
        
        C := UnderlyingCategory( AC_objfin );
        
        objects := SetOfObjectsOfCategory( C );
        
        l := NumberOfObjectsOfUnderlyingCategory( AC_objfin );
        
        list_of_objects := ObjectDatum( AC, objAC );
        
        return Pair( Length( list_of_objects ),
                     List( [ 1 .. l ], i ->
                           Length( PositionsProperty( list_of_objects, obj ->
                                   IsEqualForObjects( C, obj, objects[i] ) ) ) ) );
        
    end;
    
    ## From the raw morphism data to the morphism in the modeling category
    modeling_tower_morphism_constructor :=
      function( AC_objfin, source, morphism_matrix, target )
        local AC;
        
        # The dimensions of the matrix are checked in AC
        
        AC := ModelingCategory( AC_objfin );
        
        return MorphismConstructor( AC,
                       source,
                       morphism_matrix,
                       target );
        
    end;
    
    ## From the morphism in the modeling category to the raw morphism data
    modeling_tower_morphism_datum :=
      function( AC_objfin, phi )
        local AC, C, objects, morphism_list, nr_rows, nr_cols, column_offset, morphism_matrix;
        
        AC := ModelingCategory( AC_objfin );
        
        C := UnderlyingCategory( AC_objfin );
        
        objects := SetOfObjectsOfCategory( C );
        
        morphism_matrix := MorphismMatrix( phi );
        morphism_list := Concatenation( morphism_matrix );
        
        # Here is an example how the sorting works.
        #
        #  |   1      2      3
        # -|--------------------
        # 1| (3,2)  (2,1)  (1,2)
        # 2| (2,3)  (3,3)  (1,3)
        # 3| (2,2)  (3,1)  (1,1)
        #
        # Concatenating the rows:
        # [3,2],  [2,1],  [1,2],  [2,3],  [3,3],  [1,3],  [2,2],  [3,1],  [1,1]
        #
        # Stable sorting by the first value:
        # [1,2], [1,3], [1,1]  |  [2,1], [2,3], [2,2]  |  [3,2], [3,3], [3,1]
        #
        # Stable sorting by the second value:
        # [1,1], [2,1], [3,1]  |  [1,2], [2,2], [3,2]  |  [1,3], [2,3], [3,3]
        #
        # This list is the concatenation of the columns vectors of the matrix we need.
        #
        #      1      2      3
        # -----------------------
        # 1| (1,1)  (1,2)  (1,3)
        # 2| (2,1)  (2,2)  (2,3)
        # 3| (3,1)  (3,2)  (3,3)
        
        # Sort by source
        StableSortBy( morphism_list, { mor } -> Position( objects, Source( mor ) ) );
        
        # Sort by target
        StableSortBy( morphism_list, { mor } -> Position( objects, Target( mor ) ) );
        
        # The resulting list of the two sorts gives a concatenation of columns of our desired matrix.
        # The following reconstructs the matrix form.
        nr_rows := NrRows( phi );
        nr_cols := NrCols( phi );

        column_offset := List( [ 1 .. nr_cols ], col_i -> 1 + (col_i - 1)*nr_rows );
        morphism_matrix := List( [ 0 .. nr_rows - 1 ], row -> morphism_list{ column_offset + row } );
        
        return morphism_matrix;
        
    end;
    
    ##
    AC_objfin :=
      ReinterpretationOfCategory( AC,
              rec( name := Concatenation( "AdditiveClosureOfObjectFiniteCategory( ", Name( C ), " )" ),
                   category_filter := IsAdditiveClosureOfObjectFiniteCategory,
                   category_object_filter := IsObjectInAdditiveClosureOfObjectFiniteCategory,
                   category_morphism_filter := IsMorphismInAdditiveClosureOfObjectFiniteCategory,
                   object_datum_type := object_datum_type,
                   morphism_datum_type := morphism_datum_type,
                   object_constructor := object_constructor,
                   object_datum := object_datum,
                   morphism_constructor := morphism_constructor,
                   morphism_datum := morphism_datum,
                   modeling_tower_object_constructor := modeling_tower_object_constructor,
                   modeling_tower_object_datum := modeling_tower_object_datum,
                   modeling_tower_morphism_constructor := modeling_tower_morphism_constructor,
                   modeling_tower_morphism_datum := modeling_tower_morphism_datum,
                   only_primitive_operations := true )
              : FinalizeCategory := false );
    
    SetUnderlyingCategory( AC_objfin, C );
    SetNumberOfObjectsOfUnderlyingCategory( AC_objfin, Length( SetOfObjectsOfCategory( C ) ) );
    
    if HasIsSkeletalCategory( C ) and IsSkeletalCategory( C ) then
        SetIsSkeletalCategory( AC_objfin, true );
    fi;
    
    
    Append( AC_objfin!.compiler_hints.category_attribute_names,
            [ "UnderlyingCategory",
              "NumberOfObjectsOfUnderlyingCategory" ] );
    
    if CAP_NAMED_ARGUMENTS.FinalizeCategory then
        
        Finalize( AC_objfin );
        
    fi;
    
    return AC_objfin;
    
end ) );

####################################
##
## Operations
##
####################################

##
InstallOtherMethod( \/,
               [ IsList, IsAdditiveClosureOfObjectFiniteCategory ],
               
  function( listlist, AC_objfin )
    local AC, C, obj_ac,  source_ac, source, target_ac, target, mor;
    
    AC := ModelingCategory( AC_objfin );
    C := UnderlyingCategory( AC_objfin );
    
    if ForAll( listlist, obj -> IsCapCategoryObject( obj ) and
                                IsIdenticalObj( CapCategory( obj ), C ) ) then
        
        # It's a list of objets in the underlying category

        obj_ac := AdditiveClosureObject( AC, listlist );
        
        Assert( 0, IsWellDefinedForObjects( AC, obj_ac ) );
        
        return ReinterpretationOfObject( AC_objfin, obj_ac );
        
    else
        
        # Assume its a matrix of morphisms in C
        
        source_ac := AdditiveClosureObject( AC, List( listlist, row -> Source( row[1] ) ) );
        source := ReinterpretationOfObject( AC_objfin, source_ac );
        
        target_ac := AdditiveClosureObject( AC, List( listlist[1], col -> Target( col ) ) );
        target := ReinterpretationOfObject( AC_objfin, target_ac );
        
        mor := AdditiveClosureMorphism( AC, source_ac, listlist, target_ac );
        
        return ReinterpretationOfMorphism( AC_objfin, source, mor, target );
        
    fi;
    
end );

##
ObjectToMultiplicityList :=
  function( obj, set_of_objects )
    
    local pos, positions;
    
    pos := Position( set_of_objects, obj );
    
    positions := ListWithIdenticalEntries( Length( set_of_objects ), 0 );
    
    positions[pos] := 1;
    
    return positions;
    
end;

##
InstallOtherMethod( \/,
               [ IsCapCategoryObject, IsAdditiveClosureOfObjectFiniteCategory ],
               
  function( obj, AC_objfin )
    local set_of_objects, pos, positions;
    
    Assert( 0, IsIdenticalObj( UnderlyingCategory( AC_objfin ), CapCategory( obj ) ) );
    
    set_of_objects := SetOfObjectsOfCategory( UnderlyingCategory( AC_objfin ) );
    
    positions := ObjectToMultiplicityList( obj, set_of_objects );
    
    return ObjectConstructor( AC_objfin, [ 1, positions ] );
    
end );

##
InstallOtherMethod( \/,
               [ IsCapCategoryMorphism, IsAdditiveClosureOfObjectFiniteCategory ],
               
  function( alpha, AC_objfin )
    local set_of_objects, source, target;
    
    Assert( 0, IsIdenticalObj( UnderlyingCategory( AC_objfin ), CapCategory( alpha ) ) );
    
    set_of_objects := SetOfObjectsOfCategory( UnderlyingCategory( AC_objfin ) );
    
    source := ObjectConstructor( AC_objfin, [ 1, ObjectToMultiplicityList( Source( alpha ), set_of_objects ) ] );
    target := ObjectConstructor( AC_objfin, [ 1, ObjectToMultiplicityList( Target( alpha ), set_of_objects ) ] );
    
    return MorphismConstructor( AC_objfin, source, [ [ alpha ] ], target );
    
end );

##
InstallMethodForCompilerForCAP( \[\,\],
               [ IsMorphismInAdditiveClosureOfObjectFiniteCategory, IsInt, IsInt ],
               
  function( morphism, i, j )
    
    if not ( i < ChecksumAndMultiplicities( Source( morphism ) )[1] and
             j < ChecksumAndMultiplicities( Target( morphism ) )[1] ) then
        
        Error( "out of bounds index [", String(i), ",", String(j),
               "] for the morphism matrix.\n" );
        
    fi;
    
    return MorphismMatrix( morphism )[i][j];
    
end );

####################################
##
## View
##
####################################

##
InstallMethod( ViewString,
               [ IsObjectInAdditiveClosureOfObjectFiniteCategory ],
               
  function( object )
    return Concatenation(
                "<An object in ", Name( CapCategory( object ) ),
                " defined by ", String( ChecksumAndMultiplicities( object )[1] ) , " underlying objects>" );
end );

##
InstallMethod( ViewString,
               [ IsMorphismInAdditiveClosureOfObjectFiniteCategory ],
               
  function( morphism )
    return Concatenation(
                "<A morphism in ", Name( CapCategory( morphism ) ),
                " defined by a ",
                String( ChecksumAndMultiplicities( Source( morphism ) )[1] ),
                " x ",
                String( ChecksumAndMultiplicities( Target( morphism ) )[1] ),
                " matrix of underlying morphisms>" );
end );

##
InstallMethod( DisplayString,
               [ IsObjectInAdditiveClosureOfObjectFiniteCategory ],
               
  function( object )
    local AC, C, objects_of_underlying_category, nr_objects_of_underlying_category,
          nr_objects, multiplicities, string, obj;
    
    AC := CapCategory( object );
    C := UnderlyingCategory( AC );
    objects_of_underlying_category := SetOfObjectsOfCategory( C );
    nr_objects_of_underlying_category := NumberOfObjectsOfUnderlyingCategory( AC );
    nr_objects := ChecksumAndMultiplicities( object )[1];
    multiplicities := ChecksumAndMultiplicities( object )[2];
    
    if nr_objects = 1 then
      
      string := Concatenation( "A formal direct sum consisting of ", String( nr_objects ), " object.\n" );
      
    else
      
      string := Concatenation( "A formal direct sum consisting of ", String( nr_objects ), " objects.\n" );
      
    fi;
    
    for obj in [ 1 .. nr_objects_of_underlying_category  ] do
        
        string := Concatenation( string, String( multiplicities[ obj ] ), " times: " );
        
        string := Concatenation( string, ViewString( objects_of_underlying_category[ obj ] ), "\n" );
        
    od;
    
    return string;
    
end );

##
InstallMethod( DisplayString,
               [ IsMorphismInAdditiveClosureOfObjectFiniteCategory ],
               
  function( morphism )
    local nr_rows, nr_cols, string, i, j;
    
    nr_rows := ChecksumAndMultiplicities( Source( morphism ) )[1];
    nr_cols := ChecksumAndMultiplicities( Target( morphism ) )[1];
    
    string := Concatenation( "A ", String( nr_rows ), " x ", String( nr_cols ),
                             " matrix with entries in ",
                             Name( UnderlyingCategory( CapCategory( morphism ) ) ), "\n" );
    
    for i in [ 1 .. nr_rows ] do
        
        for j in [ 1 .. nr_cols ] do
            
            string := Concatenation( string, Concatenation( "\n[", String(i), ",", String(j), "]: " ) );
            
            string := Concatenation( string, ViewString( morphism[i, j] ) );
            
        od;
        
    od;
    
    string := Concatenation( string, "\n" );
    
    return string;
    
end );

