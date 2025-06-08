# SPDX-License-Identifier: GPL-2.0-or-later
# FreydCategoriesForCAP: Freyd categories - Formal (co)kernels for additive categories
#
# Implementations
#

##
InstallMethod( DisconnectedAdditiveClosure,
               [ IsCapCategory ],
               DISCONNECTED_ADDITIVE_CLOSURE
);

##
InstallMethod( DISCONNECTED_ADDITIVE_CLOSURE,
               [ IsCapCategory ],
               
  FunctionWithNamedArguments(
  [
    [ "FinalizeCategory", true ],
  ],
  function( CAP_NAMED_ARGUMENTS, C )
    local object_datum_type, object_constructor, object_datum,
          morphism_datum_type, morphism_constructor, morphism_datum,
          AC_objfin,
          modeling_tower_object_constructor, modeling_tower_object_datum,
          modeling_tower_morphism_constructor, modeling_tower_morphism_datum,
          DAC;
    
    Assert( 0, HasIsObjectFiniteCategory( C ) and IsObjectFiniteCategory( C ) and CanCompute( C, "SetOfObjectsOfCategory" ) );
    
    Assert( 0, HasIsAbCategory( C ) and IsAbCategory( C ) );
    
    ##
    object_datum_type := CapJitDataTypeOfNTupleOf( 2, IsBigInt, CapJitDataTypeOfListOf( IsBigInt ) );
    
    ##
    object_constructor :=
      function( DAC, checksum_and_multiplicities )
        
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
        
        return CreateCapCategoryObjectWithAttributes( DAC,
                       ChecksumAndMultiplicities, checksum_and_multiplicities );
        
    end;
    
    ##
    object_datum := { DAC, obj } -> ChecksumAndMultiplicities( obj );
    
    ##
    morphism_datum_type := CapJitDataTypeOfListOf(
                                CapJitDataTypeOfListOf(
                                    CapJitDataTypeOfListOf(
                                        CapJitDataTypeOfMorphismOfCategory( C ) ) ) );
   
    ##
    morphism_constructor :=
      function( DAC, S, list_of_matrices, T )
        
        #% CAP_JIT_DROP_NEXT_STATEMENT
        Assert( 0, IsList( list_of_matrices ) and
                   Length( list_of_matrices ) = NumberOfObjectsOfUnderlyingCategory( DAC ) );
        
        #% CAP_JIT_DROP_NEXT_STATEMENT
        Assert( 0, ForAllWithKeys( list_of_matrices,
                   { key, matrix } -> IsList( matrix ) and
                                      Length( matrix ) = ChecksumAndMultiplicities( S )[2][key] and
                                      ForAll( matrix,
                                              row -> IsList( row ) and
                                                     Length( row ) = ChecksumAndMultiplicities( T )[2][key] ) ) );
        
        return CreateCapCategoryMorphismWithAttributes( DAC,
                       S,
                       T,
                       ListOfMatrices, list_of_matrices );
        
    end;
    
    ##
    morphism_datum := { DAC, phi } -> ListOfMatrices( phi );
    
    ## Building the categorical tower:
    
    AC_objfin := AdditiveClosureOfObjectFiniteCategory_Reinterpreted( C : FinalizeCategory := true );
    
    ## From the raw object data to the object in the modeling category
    modeling_tower_object_constructor :=
      function( DAC, checksum_and_multiplicities )
        local AC_objfin;
        
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
        
        AC_objfin := ModelingCategory( DAC );
        
        return ObjectConstructor( AC_objfin, checksum_and_multiplicities );
        
    end;
    
    ## From the object in the modeling category to the raw object data
    modeling_tower_object_datum :=
      function( DAC, objAC )
        
        return ChecksumAndMultiplicities( objAC );
        
    end;
    
    ## From the raw morphism data to the morphism in the modeling category
    modeling_tower_morphism_constructor :=
      function( DAC, source, list_of_matrices, target )
        local AC_objfin, C, objects, nr_objects, nr_matrices, source_mults, target_mults, get_row_of_matrix_or_zero_row, morphism_matrix;
        
        #% CAP_JIT_DROP_NEXT_STATEMENT
        Assert( 0, IsList( list_of_matrices ) and
                   Length( list_of_matrices ) = NumberOfObjectsOfUnderlyingCategory( DAC ) );
        
        #% CAP_JIT_DROP_NEXT_STATEMENT
        Assert( 0, ForAllWithKeys( list_of_matrices,
                   { key, matrix } -> IsList( matrix ) and
                                      Length( matrix ) = ChecksumAndMultiplicities( source )[2][key] and
                                      ForAll( matrix,
                                              row -> IsList( row ) and
                                                     Length( row ) = ChecksumAndMultiplicities( target )[2][key] ) ) );
        
        AC_objfin := ModelingCategory( DAC );
        
        C := UnderlyingCategory( DAC );
        
        objects := SetOfObjectsOfCategory( C );
        nr_objects := NumberOfObjectsOfUnderlyingCategory( DAC );
        nr_matrices := Length( list_of_matrices );
        
        source_mults := ChecksumAndMultiplicities( source )[2];
        target_mults := ChecksumAndMultiplicities( target )[2];
        
        # Extend the rows of the matrices with zero morphisms.
        # Note: number of matrices = number of objects,
        #       source_mults = number of rows for each matrix,
        #       target_mults = number of columns for each matrix.
        list_of_matrices :=
            ListWithKeys( list_of_matrices, { obj, matrix } ->
                List( matrix, row ->
                    Concatenation(
                        Concatenation( List( [ 1 .. obj-1 ],
                                       i -> ListWithIdenticalEntries( target_mults[i],
                                                                      ZeroMorphism( C, objects[obj], objects[i] ) ) ) ),
                        row,
                        Concatenation( List( [ obj+1 .. nr_objects ],
                                       i -> ListWithIdenticalEntries( target_mults[i],
                                                                      ZeroMorphism( C, objects[obj], objects[i] ) ) ) ) ) ) );
        
        # All rows of all matrices now have the same number of colums
        # so we can stack all matrices to get our final matrix.
        morphism_matrix := Concatenation( list_of_matrices );
        
        return MorphismConstructor( AC_objfin, source, morphism_matrix, target );
        
    end;
    
    ## From the morphism in the modeling category to the raw morphism data
    modeling_tower_morphism_datum :=
      function( DAC, phi )
        local AC_objfin, C, nr_objects, morphism_matrix, source, target, source_mults, target_mults, row_indices, col_indices, list_of_matrices;
        
        AC_objfin := ModelingCategory( DAC );
        
        C := UnderlyingCategory( DAC );
        
        nr_objects := NumberOfObjectsOfUnderlyingCategory( DAC );
        
        morphism_matrix := MorphismMatrix( phi );
        
        source := Source( phi );
        target := Target( phi );
        
        source_mults := ChecksumAndMultiplicities( source )[2];
        target_mults := ChecksumAndMultiplicities( target )[2];
        
        row_indices := List( [ 0 .. Length( source_mults ) ], i -> Sum( source_mults{ [ 1 .. i ] } ) );
        col_indices := List( [ 0 .. Length( target_mults ) ], i -> Sum( target_mults{ [ 1 .. i ] } ) );
        
        # Extract the block matrices on the diagonal
        list_of_matrices := List( [ 1 .. nr_objects ],
                                  obj_idx -> List( [ row_indices[obj_idx] + 1 .. row_indices[obj_idx + 1] ],
                                                   row_nr -> morphism_matrix[row_nr]{ [ col_indices[obj_idx] + 1 .. col_indices[obj_idx + 1] ] } ) );
        
        return list_of_matrices;
        
    end;
    
    ##
    DAC :=
      ReinterpretationOfCategory( AC_objfin,
              rec( name := Concatenation( "DisconnectedAdditiveClosure( ", Name( C ), " )" ),
                   category_filter := IsDisconnectedAdditiveClosure,
                   category_object_filter := IsObjectInDisconnectedAdditiveClosure,
                   category_morphism_filter := IsMorphismInDisconnectedAdditiveClosure,
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
    
    SetUnderlyingCategory( DAC, C );
    SetNumberOfObjectsOfUnderlyingCategory( DAC, Length( SetOfObjectsOfCategory( C ) ) );
    
    if HasIsSkeletalCategory( C ) and IsSkeletalCategory( C ) then
        SetIsSkeletalCategory( DAC, true );
    fi;
    
    Append( DAC!.compiler_hints.category_attribute_names,
            [ "UnderlyingCategory",
              "NumberOfObjectsOfUnderlyingCategory" ] );
    
    if CAP_NAMED_ARGUMENTS.FinalizeCategory then
        
        Finalize( DAC );
        
    fi;
    
    return DAC;
    
end ) );
