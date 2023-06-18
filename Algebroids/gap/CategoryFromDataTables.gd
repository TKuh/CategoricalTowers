# SPDX-License-Identifier: GPL-2.0-or-later
# Algebroids: Algebroids and bialgebroids as preadditive categories generated by enhanced quivers
#
# Declarations
#

#! @Chapter Finite categories from data tables

####################################
#
#! @Section GAP categories
#
####################################

#! @Description
#!  The &GAP; category of categories from data tables.
DeclareCategory( "IsCategoryFromDataTables",
        IsCapCategory );

#! @Description
#!  The &GAP; category of cells in a category from data tables.
DeclareCategory( "IsCellInCategoryFromDataTables",
        IsCapCategoryCell );

#! @Description
#!  The &GAP; category of objects in a category from data tables.
DeclareCategory( "IsObjectInCategoryFromDataTables",
        IsCellInCategoryFromDataTables and IsCapCategoryObject );

#! @Description
#!  The &GAP; category of morphisms in a category from data tables.
DeclareCategory( "IsMorphismInCategoryFromDataTables",
        IsCellInCategoryFromDataTables and IsCapCategoryMorphism );

####################################
#
#! @Section Attributes
#
####################################

#! @Description
#!  The data tables used to create the category <A>C</A>.
#!  It might differ from the <Q>normalized</Q> output of
#!  <C>DataTablesOfCategory</C>( <A>C</A> ).
#! @Arguments C
#! @Returns a pair of lists
DeclareAttribute( "DataTables",
        IsCapCategory );

CapJitAddTypeSignature( "DataTables", [ IsCapCategory ],
  function ( input_types )
    
    Assert( 0, IsFinite( input_types[1].category ) );
    
    return rec( filter := IsNTuple,
                element_types :=
                [ rec( filter := IsNTuple,
                       element_types :=
                       [ # C0
                         rec( filter := IsInt ),
                         # C1
                         rec( filter := IsInt ) ] ),
                  rec( filter := IsNTuple,
                       element_types :=
                       [ # identity
                         rec( filter := IsList,
                              element_type := rec( filter := IsInt ) ),
                         # s
                         rec( filter := IsList,
                              element_type := rec( filter := IsInt ) ),
                         # t
                         rec( filter := IsList,
                              element_type := rec( filter := IsInt ) ),
                         # precompose
                         rec( filter := IsList,
                              element_type :=
                              rec( filter := IsList,
                                   element_type := rec( filter := IsInt ) ) ),
                         # hom_on_objs
                         rec( filter := IsList,
                              element_type :=
                              rec( filter := IsList,
                                   element_type := rec( filter := IsInt ) ) ),
                         # hom_on_mors
                         rec( filter := IsList,
                              element_type :=
                              rec( filter := IsList,
                                   element_type :=
                                   rec( filter := IsList,
                                        element_type := rec( filter := IsInt ) ) ) ),
                         # introduction
                         rec( filter := IsList,
                              element_type :=
                              rec( filter := IsList,
                                   element_type := rec( filter := IsInt ) ) ),
                         # elimination
                         rec( filter := IsList,
                              element_type :=
                              rec( filter := IsList,
                                   element_type :=
                                   rec( filter := IsList,
                                        element_type := rec( filter := IsInt ) ) ) ) ] )
                  ] );
    
end );

#! @Description
#!  The finite set of objects of the category <A>C</A> created from data tables.
#! @Arguments C
#! @Returns a list
DeclareAttribute( "SetOfObjects",
        IsCategoryFromDataTables );

#! @Description
#!  The finite set of morphisms of the category <A>C</A> created from data tables.
#! @Arguments C
#! @Returns a list
DeclareAttribute( "SetOfMorphisms",
        IsCategoryFromDataTables );

DeclareAttribute( "IndicesOfGeneratingMorphisms",
        IsCategoryFromDataTables );

CapJitAddTypeSignature( "IndicesOfGeneratingMorphisms", [ IsCategoryFromDataTables ],
  function ( input_types )
    
    return CapJitDataTypeOfListOf( IsInt );
    
end );

DeclareAttribute( "DecompositionOfAllMorphisms",
        IsCategoryFromDataTables );

#CapJitAddTypeSignature( "DecompositionOfAllMorphisms", [ IsCategoryFromDataTables ],
#  function ( input_types )
#    
#    return rec( filter := IsList,
#                element_type :=
#                rec( filter := IsList,
#                     element_type := rec( filter := IsInt ) ) );
#    
#end );

DeclareAttribute( "RelationsAmongGeneratingMorphisms",
        IsCategoryFromDataTables );

#CapJitAddTypeSignature( "RelationsAmongGeneratingMorphisms", [ IsCategoryFromDataTables ],
#  function ( input_types )
#    
#    return rec( filter := IsList,
#                element_type :=
#                rec( filter := IsNTuple,
#                     element_types :=
#                     [ rec( filter := IsList,
#                            element_type := rec( filter := IsInt ) ),
#                       rec( filter := IsList,
#                            element_type := rec( filter := IsInt ) ) ] ) );
#    
#end );

#! @Description
#!  The finite set of morphisms generating the category <A>C</A> created from data tables.
#! @Arguments C
#! @Returns a list
DeclareAttribute( "SetOfGeneratingMorphisms",
        IsCategoryFromDataTables );

#! @Description
#!  The number of morphisms in the category <A>C</A> created from data tables.
#! @Arguments C
#! @Returns a nonnegative integer
DeclareAttribute( "Size",
        IsCategoryFromDataTables );

##
DeclareAttribute( "MapOfObject",
        IsObjectInCategoryFromDataTables );

CapJitAddTypeSignature( "MapOfObject", [ IsObjectInCategoryFromDataTables ],
  function ( input_types )
    local V;
    
    Assert( 0, IsCategoryFromDataTables( input_types[1].category ) );
    
    V := RangeCategoryOfHomomorphismStructure( input_types[1].category );
    
    return CapJitDataTypeOfMorphismOfCategory( V );
    
end );

##
DeclareAttribute( "MapOfMorphism",
        IsMorphismInCategoryFromDataTables );

CapJitAddTypeSignature( "MapOfMorphism", [ IsMorphismInCategoryFromDataTables ],
  function ( input_types )
    local V;
    
    Assert( 0, IsCategoryFromDataTables( input_types[1].category ) );
    
    V := RangeCategoryOfHomomorphismStructure( input_types[1].category );
    
    return CapJitDataTypeOfMorphismOfCategory( V );
    
end );

#! @Description
#!  The opposite category of the category <A>C</A> defined by nerve data.
#! @Arguments C
#! @Returns a &CAP; category
DeclareAttribute( "OppositeCategoryFromDataTables",
        IsCategoryFromDataTables );

####################################
#
#! @Section Constructors
#
####################################

#! @Description
#!  Construct an enriched finite category out of the <A>input_record</A>
#!  consisting of values to the keys:
#!  * name
#!  * nerve_data
#!  * indices_of_generating_morphisms
#!  * relations
#!  * labels
#!  * properties
#! @Arguments input_record
#! @Returns a &CAP; category
DeclareAttribute( "CategoryFromDataTables",
        IsRecord );
#! @InsertChunk CategoryFromDataTables

#! @Arguments C
DeclareAttribute( "CategoryFromDataTables",
        IsFpCategory );

#! @Arguments C
DeclareAttribute( "CategoryFromDataTables",
        IsCategoryFromNerveData );

#! @Description
#!  Construct the <A>o</A>-th object in the category <A>C</A> created from data tables.
#! @Arguments C, o
#! @Returns a &CAP; category
DeclareOperation( "CreateObject",
        [ IsCategoryFromDataTables, IsInt ] );

#! @Description
#!  Construct the <A>m</A>-th morphism <A>source</A>$\to$<A>range</A>
#!  in the category <A>C</A> created from data tables.
#! @Arguments C, m
#! @Returns a &CAP; category
#! @Group CreateMorphism
DeclareOperation( "CreateMorphism",
        [ IsCategoryFromDataTables, IsInt ] );

#! @Arguments source, m, range
#! @Group CreateMorphism
DeclareOperation( "CreateMorphism",
        [ IsObjectInCategoryFromDataTables, IsInt, IsObjectInCategoryFromDataTables ] );
