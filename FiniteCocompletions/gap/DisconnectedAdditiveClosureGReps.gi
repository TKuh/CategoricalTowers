# SPDX-License-Identifier: GPL-2.0-or-later
# FiniteCocompletions: Finite (co)product/(co)limit (co)completions
#
# Implementations
#

####################################
##
## Constructors
##
####################################

##
InstallMethod( AdditiveClosureOfObjectFiniteDisconnectedCategoryGReps,
               [ IsCapCategory ],
               DISCONNECTED_ADDITIVE_CLOSURE_GREPS
);

##
InstallMethod( DISCONNECTED_ADDITIVE_CLOSURE_GREPS,
               [ IsCapCategory ],
               
  FunctionWithNamedArguments(
  [
    [ "FinalizeCategory", true ],
  ],
  function( CAP_NAMED_ARGUMENTS, underlying_category )
    local object_datum_type, object_constructor, object_datum,
          morphism_datum_type, morphism_constructor, morphism_datum,
          AC_objfin,
          modeling_tower_object_constructor, modeling_tower_object_datum,
          modeling_tower_morphism_constructor, modeling_tower_morphism_datum,
          DAC_GReps;
    
    if not ( HasIsAbCategory( underlying_category ) and IsAbCategory( underlying_category ) ) then
        
        # COVERAGE_IGNORE_NEXT_LINE
        Error( "the underlying category has to be a pre-additive category\n" );
        
    fi;
    
    if not ( HasIsObjectFiniteCategory( underlying_category ) and IsObjectFiniteCategory( underlying_category ) ) then
        
        # COVERAGE_IGNORE_NEXT_LINE
        Error( "the underlying category has to be an object finite category\n" );
        
    fi;
    
    ##
    object_datum_type := CapJitDataTypeOfListOf(
                            CapJitDataTypeOfNTupleOf( 2,
                                IsBigInt,
                                CapJitDataTypeOfObjectOfCategory( underlying_category ) ) );
    
    ##
    object_constructor :=
      function( DAC_GReps, multiplicities_and_objects )
        local tuple, set_of_objects, tuple_1, tuple_2, i;
        
        #% CAP_JIT_DROP_NEXT_STATEMENT
        Assert( 0,
                IsList( multiplicities_and_objects ) and
                ForAll( multiplicities_and_objects, tuple -> IsList( tuple ) and Length( tuple ) = 2 ) );
        
        if Length( multiplicities_and_objects ) > NumberOfObjectsOfUnderlyingCategory( DAC_GReps ) then
            
            # COVERAGE_IGNORE_NEXT_LINE
            Error( "the number of tuples can be at most ",
                   String( NumberOfObjectsOfUnderlyingCategory( DAC_GReps ) ),
                   "\n" );
            
        fi;
        
        for tuple in multiplicities_and_objects do
            
            if tuple[1] < 0 then
                
                # COVERAGE_IGNORE_NEXT_LINE
                Error( "The multiplicity of the tuple at index ",
                       String( Position( multiplicities_and_objects, tuple ) ),
                       " is smaller than 0\n" );
                
            fi;
            
            if CapCategory( tuple[2] ) <> underlying_category then
                
                # COVERAGE_IGNORE_NEXT_LINE
                Error( "The object of the tuple at index ",
                       String( Position( multiplicities_and_objects, tuple ) ),
                       " does not lie in <underlying_category>\n");
                
            fi;
            
        od;
        
        set_of_objects := SetOfObjectsOfCategory( underlying_category );
        
        # All tuples [ mult, obj ] have to be ordered by the indices of <obj> in
        # SetOfObjectsOfCategory( underlying_category ).
        # Example: the object S1 appears before S2, so the tuple [ i, S1 ] appears before [ j, S2 ].
        for i in [ 1 .. Length( multiplicities_and_objects ) - 1 ] do
            
            tuple_1 := multiplicities_and_objects[ i ];
            tuple_2 := multiplicities_and_objects[ i + 1 ];
            
            if Position( set_of_objects, tuple_1[2] ) > Position( set_of_objects, tuple_2[2] ) then
                
                # COVERAGE_IGNORE_NEXT_LINE
                Error( "the tuples at indices ",
                       String( i ),
                       " and ",
                       String( i + 1 ),
                       " have the wrong order\n");
                
            fi;
            
        od;
        
        return CreateCapCategoryObjectWithAttributes( DAC_GReps,
                   MultiplicitiesAndObjects, multiplicities_and_objects );
        
    end;
    
    ##
    object_datum := { DAC_GReps, obj } -> MultiplicitiesAndObjects( obj );
    
    ##
    morphism_datum_type := CapJitDataTypeOfListOf(
                                CapJitDataTypeOfListOf(
                                    CapJitDataTypeOfListOf(
                                        CapJitDataTypeOfMorphismOfCategory( underlying_category ) ) ) );
   
    ##
    morphism_constructor :=
      function( DAC_GReps, S, list_of_matrices, T )
        
        # Checks are done in the modeling category.
        
        return CreateCapCategoryMorphismWithAttributes( DAC_GReps,
                       S,
                       T,
                       ListOfMatrices, list_of_matrices );
        
    end;
    
    ##
    morphism_datum := { DAC_GReps, phi } -> ListOfMatrices( phi );
    
    ####################################
    # Reinterpretation
    ####################################
    
    AC_objfin := AdditiveClosureOfObjectFiniteDisconnectedCategory( underlying_category : FinalizeCategory := true );
    
    ## From the raw object data to the object in the modeling category
    modeling_tower_object_constructor :=
      function( DAC_GReps, multiplicities_and_objects )
        local nr_summands, multiplicities, tuple, pos;
        
        # Checks are done in the modeling category.
        
        nr_summands := 0;
        
        multiplicities :=
            ListWithIdenticalEntries( NumberOfObjectsOfUnderlyingCategory( DAC_GReps ), 0 );
        
        for tuple in multiplicities_and_objects do
            
            nr_summands := nr_summands + tuple[1];
            
            pos := Position( SetOfObjectsOfCategory( underlying_category ), tuple[2] );
            
            multiplicities[ pos ] := tuple[1];
            
        od;
        
        return ObjectConstructor( ModelingCategory( DAC_GReps ), [ nr_summands, multiplicities ] );
        
    end;
    
    ## From the object in the modeling category to the raw object data.
    modeling_tower_object_datum :=
      function( DAC_GReps, objDAC )
        local set_of_objects, multiplicities_and_objects;
        
        set_of_objects := SetOfObjectsOfCategory( underlying_category );
        
        multiplicities_and_objects :=
            ListWithKeys( Multiplicities( objDAC ), { obj, multiplicity } ->
                NTuple( 2, multiplicity, set_of_objects[ obj ] ) );
        
        return multiplicities_and_objects;
        
    end;
    
    ## From the raw morphism data to the morphism in the modeling category.
    modeling_tower_morphism_constructor :=
      function( DAC_GReps, source, list_of_matrices, target )
        local DAC;
        
        # Checks are done in the modeling category.
        
        DAC := ModelingCategory( DAC_GReps );
        
        return MorphismConstructor( DAC, source, list_of_matrices, target );
        
    end;
    
    ## From the morphism in the modeling category to the raw morphism data
    modeling_tower_morphism_datum :=
      function( DAC_GReps, phi )
        
        return ListOfMatrices( phi );
        
    end;
    
    ##
    DAC_GReps :=
      ReinterpretationOfCategory( AC_objfin,
              rec( name := Concatenation( "AdditiveClosureOfObjectFiniteDisconnectedCategoryGReps( ", Name( underlying_category ), " )" ),
                   category_filter := IsAdditiveClosureOfObjectFiniteDisconnectedCategoryGReps,
                   category_object_filter := IsObjectInAdditiveClosureOfObjectFiniteDisconnectedCategoryGReps,
                   category_morphism_filter := IsMorphismInAdditiveClosureOfObjectFiniteDisconnectedCategoryGReps,
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
    
    ####################################
    # Categorical properties
    ####################################
    
    if HasIsSkeletalCategory( underlying_category ) and IsSkeletalCategory( underlying_category ) then
        
        SetIsSkeletalCategory( DAC_GReps, true );
        
    fi;
    
    Append( DAC_GReps!.compiler_hints.category_attribute_names,
            [ "UnderlyingCategory",
              "NumberOfObjectsOfUnderlyingCategory" ] );
    
    ####################################
    # Attributes
    ####################################
    
    SetUnderlyingCategory( DAC_GReps, underlying_category );
    
    SetNumberOfObjectsOfUnderlyingCategory( DAC_GReps, Length( SetOfObjectsOfCategory( underlying_category ) ) );
    
    ####################################
    # Finalize
    ####################################
    
    if CAP_NAMED_ARGUMENTS.FinalizeCategory then
        
        Finalize( DAC_GReps );
        
    fi;
    
    return DAC_GReps;
    
end ) );

####################################
##
## Attributes
##
####################################

InstallMethodForCompilerForCAP( UnderlyingObjectList,
                                [ IsObjectInAdditiveClosureOfObjectFiniteDisconnectedCategoryGReps ],
                                
  function( obj )
    
    return UnderlyingObjectList( ModelingObject( CapCategory( obj ), obj  ) );
    
end );

InstallMethodForCompilerForCAP( Support,
                                [ IsObjectInAdditiveClosureOfObjectFiniteDisconnectedCategoryGReps ],
                                
  function( obj )
    
    return List( MultiplicitiesAndObjects( obj ), pair -> pair[2] );
    
end );

InstallMethodForCompilerForCAP( Component,
                                [ IsMorphismInAdditiveClosureOfObjectFiniteDisconnectedCategoryGReps,
                                  IsCapCategoryObject ],
                                
  function( mor, obj )
    local set_of_objects, position;
    
    set_of_objects := SetOfObjectsOfCategory( UnderlyingCategory( CapCategory( mor ) ) );
    
    position := Position( set_of_objects, obj );
    
    return ListOfMatrices( mor )[ position ];
    
end );

####################################
##
## Operators
##
####################################

##
InstallMethodForCompilerForCAP( \[\],
                                [ IsObjectInAdditiveClosureOfObjectFiniteDisconnectedCategoryGReps, IsInt ],
                                
  function( object, i )
    local obj_list;
    
    obj_list := UnderlyingObjectList( object );
    
    if i < 1 or i > Length( obj_list ) then
        
        # COVERAGE_IGNORE_NEXT_LINE
        Error( "out of bounds\n" );
        
    fi;
    
    return obj_list[ i ];
    
end );

##
InstallMethodForCompilerForCAP( \[\],
                                [ IsMorphismInAdditiveClosureOfObjectFiniteDisconnectedCategoryGReps, IsInt ],
                                
  function( morphism, i )
    
    if i < 1 or i > NumberOfObjectsOfUnderlyingCategory( CapCategory( morphism ) ) then
        
        # COVERAGE_IGNORE_NEXT_LINE
        Error( "out of bounds\n" );
        
    fi;
    
    return ListOfMatrices( morphism )[i];
    
end );

##
InstallOtherMethod( \/,
                    [ IsList, IsAdditiveClosureOfObjectFiniteDisconnectedCategoryGReps ],
                  
  function( list, DAC_GReps )
    local underlying_category, multiplicities, nr_summands_and_multiplicities, DAC,
          sources_multiplicities, nr_rows, targets_multiplicities,
          source_dac, target_dac, source, target, mor;
    
    underlying_category := UnderlyingCategory( DAC_GReps );
    
    DAC := ModelingCategory( DAC_GReps );

    if ForAll( list, obj -> IsCapCategoryObject( obj ) and
                            IsIdenticalObj( CapCategory( obj ), underlying_category ) )
    then
        
        # It's a list of objets in the underlying category.
        
        multiplicities := ObjectsToMultiplicityList( underlying_category, list );
        
        nr_summands_and_multiplicities := [ Length( list ), multiplicities ];
        
        return ReinterpretationOfObject( DAC_GReps,
                    ObjectConstructor( DAC, nr_summands_and_multiplicities ) );
        
    else
        
        # Assume it's a list of matrices of morphisms in the underlying category.
        # 
        # WARNING: We can only detect 0xn matrices as 0x0 matrices, as they correspond to empty lists '[]'.
        #          If you need 0xn matrices, then explicitly use MorphismConstructor.
        
        sources_multiplicities := List( list, matrix -> Length( matrix ) );
        
        nr_rows :=
          function( matrix )
            if IsEmpty( matrix ) then
                return 0;
            fi;
            return Length( matrix[1] );
        end;
        
        targets_multiplicities := List( list, matrix -> nr_rows( matrix ) );
        
        source_dac := ObjectConstructor( DAC, [ Sum( sources_multiplicities ), sources_multiplicities ] );
        target_dac := ObjectConstructor( DAC, [ Sum( targets_multiplicities ), targets_multiplicities ] );
        
        source := ReinterpretationOfObject( DAC_GReps, source_dac );
        target := ReinterpretationOfObject( DAC_GReps, target_dac );
        
        return MorphismConstructor( DAC_GReps, source, list, target );
        
    fi;
    
end );

##
InstallOtherMethod( \/,
                    [ IsCapCategoryObject, IsAdditiveClosureOfObjectFiniteDisconnectedCategoryGReps ],
                  
  function( obj, DAC_GReps )
    local DAC, multiplicity_list;
    
    Assert( 0, IsIdenticalObj( UnderlyingCategory( DAC_GReps ), CapCategory( obj ) ) );
    
    return ObjectConstructor( DAC_GReps, [ [ 1, obj ] ] );
    
end );

##
InstallOtherMethod( \/,
               [ IsCapCategoryMorphism, IsAdditiveClosureOfObjectFiniteDisconnectedCategoryGReps ],

  function( alpha, DAC_GReps )
    local underlying_category, source, object, list_of_matrices;

    underlying_category := UnderlyingCategory( DAC_GReps );

    Assert( 0, IsIdenticalObj( underlying_category, CapCategory( alpha ) ) );

    source := Source( alpha );

    if not IsIdenticalObj( source, Target( alpha ) ) then

        Error( "The source and target of <alpha> have to be equal." );

    fi;

    object := ObjectConstructor( DAC_GReps, [ [ 1, source ] ] );

    # All matrices are empty except for the one corresponding to <alpha>.
    list_of_matrices := ListWithIdenticalEntries( NumberOfObjectsOfUnderlyingCategory( DAC_GReps ), [ ] );

    list_of_matrices[ Position( SetOfObjectsOfCategory( underlying_category ), source ) ] := [ [ alpha ] ];

    return MorphismConstructor( DAC_GReps, object, list_of_matrices, object );

end );

####################################
##
## View
##
####################################

##
InstallMethod( ViewString,
               [ IsObjectInAdditiveClosureOfObjectFiniteDisconnectedCategoryGReps ],
               
  function( object )
    local underlying_obj, nr_summands;
    
    underlying_obj := ModelingObject( CapCategory( object ), object );

    nr_summands := NrOfSummands( underlying_obj );
    
    if nr_summands = 1 then
        
        return Concatenation(
                    "<An object in ", Name( CapCategory( object ) ),
                    " defined by ", String( nr_summands ), " underlying object>" );
        
    else
        
        return Concatenation(
                    "<An object in ", Name( CapCategory( object ) ),
                    " defined by ", String( nr_summands ), " underlying objects>" );
        
    fi;
    
end );

##
InstallMethod( ViewString,
               [ IsMorphismInAdditiveClosureOfObjectFiniteDisconnectedCategoryGReps ],
               
  function( morphism )
    local string, number_matrices;
    
    number_matrices := Length( ListOfMatrices( morphism ) );
    
    string := Concatenation( "<A morphism in ", Name( CapCategory( morphism ) ),
                             " defined by a list of ",
                             String( number_matrices ) );
    
    if number_matrices = 1 then
        
        string := Concatenation( string, " matrix of underlying morphisms>" );
        
    else
        
        string := Concatenation( string, " matrices of underlying morphisms>" );
        
    fi;
    
    return string;
end );

##
InstallMethod( DisplayString,
               [ IsObjectInAdditiveClosureOfObjectFiniteDisconnectedCategoryGReps ],
               
  function( object )
    local DAC_GReps, A, underlying_obj, objects_of_underlying_category, nr_objects_of_underlying_category,
          nr_summands, multiplicities, string, obj;
    
    DAC_GReps := CapCategory( object );
    A := UnderlyingCategory( DAC_GReps );
    
    underlying_obj := ModelingObject( CapCategory( object ), object );
    
    objects_of_underlying_category := SetOfObjectsOfCategory( A );
    nr_objects_of_underlying_category := NumberOfObjectsOfUnderlyingCategory( DAC_GReps );
    
    nr_summands := NrOfSummands( underlying_obj );
    multiplicities := Multiplicities( underlying_obj );
    
    if nr_summands = 1 then
      
      string := Concatenation( "A formal direct sum consisting of ", String( nr_summands ), " object:\n\n" );
      
    else
      
      string := Concatenation( "A formal direct sum consisting of ", String( nr_summands ), " objects:\n\n" );
      
    fi;
    
    for obj in [ 1 .. nr_objects_of_underlying_category  ] do
        
        string := Concatenation( string, String( multiplicities[ obj ] ), " times: " );
        
        string := Concatenation( string, ViewString( objects_of_underlying_category[ obj ] ), "\n" );
        
    od;
    
    return string;
    
end );

##
InstallMethod( DisplayString,
               [ IsMorphismInAdditiveClosureOfObjectFiniteDisconnectedCategoryGReps ],
               
  function( morphism )
    local i, target, matrix, nr_rows, nr_cols, string, j, k;
    
    string := "";

    for i in [ 1 .. Length( ListOfMatrices( morphism ) ) ] do
        
        matrix := morphism[i];
        
        # 0xn matrix?
        if IsEmpty( matrix ) then
            
            target := Target( morphism );
            
            nr_cols := Multiplicities( ModelingObject( CapCategory( target ), target ) )[i];
            
            string := Concatenation( string,
                                     "A ", String( 0 ), " x ", String( nr_cols ),
                                     " matrix with entries in ",
                                     Name( UnderlyingCategory( CapCategory( morphism ) ) ), "\n\n" );
            
            continue;
            
        fi;
        
        nr_rows := Length( matrix );

        # nx0 matrix?
        if IsEmpty( matrix[1] ) then
            
            string := Concatenation( string,
                                     "A ", String( nr_rows ), " x ", String( 0 ),
                                     " matrix with entries in ",
                                     Name( UnderlyingCategory( CapCategory( morphism ) ) ), "\n\n" );
            
            continue;
            
        fi;
        
        nr_cols := Length( matrix[1] );
        
        string := Concatenation( string,
                                 "A ", String( nr_rows ), " x ", String( nr_cols ),
                                 " matrix with entries in ",
                                 Name( UnderlyingCategory( CapCategory( morphism ) ) ), "\n" );
        
        # Not a zero matrix so we can display its values.
        for j in [ 1 .. nr_rows ] do
            
            for k in [ 1 .. nr_cols ] do
                
                string := Concatenation( string, Concatenation( "\n[", String(j), ",", String(k), "]: " ) );
                
                string := Concatenation( string, ViewString( matrix[j,k] ) );
                
            od;
            
        od;
        
        string := Concatenation( string, "\n\n" );
        
    od;
    
    return string;
    
end );

