# SPDX-License-Identifier: GPL-2.0-or-later
# Algebroids: Algebroids and bialgebroids as preadditive categories generated by enhanced quivers
#
# Declarations
#

#! @Chapter Algebroids from data tables

####################################
#
#! @Section GAP categories
#
####################################

#! @Description
#!  The &GAP; category of objects in an algebroid from data tables.
DeclareCategory( "IsAlgebroidFromDataTables",
        IsCapCategory );

#! @Description
#!  The &GAP; category of cells in an algebroid from data tables.
DeclareCategory( "IsCellInAlgebroidFromDataTables",
        IsCapCategoryCell );

#! @Description
#!  The &GAP; category of algebroids from data tables.
DeclareCategory( "IsAlgebroidFromDataTablesObject",
        IsCellInAlgebroidFromDataTables and
        IsCapCategoryObject );

#! @Description
#!  The &GAP; category of morphisms in an algebroid from data tables.
DeclareCategory( "IsAlgebroidFromDataTablesMorphism",
        IsCellInAlgebroidFromDataTables and
        IsCapCategoryMorphism );

####################################
#
#! @Section Constructors
#
####################################

#! @Description
#!  Construct an enrichted algebroid $B$ out of the <A>data_tables</A> consisting of values to the keys:
#!  * <A>coefficients_ring</A>: the commutative ring $k$ over which $B$ is linear.
#!  * <A>nr_objs</A>: the number of objects of $B$.
#!  * <A>labels_objs</A>: list of strings representing the names of the objects of $B$.
#!  * <A>nr_gmors</A>: the number of generating morphisms of $B$.
#!  * <A>labels_gmors</A>: list of strings representing the names of the generating morphisms of $B$.
#!  * <A>nr_bases_elms</A>: the sum of dimensions of all hom-spaces in $B$, i.e., $\Sigma_{u,v\in B}~\mathrm{dim}_{k}~\mathrm{Hom}(u,v)$, i.e., the dimension over $k$ of the endomorphism algebra of $B$.
#!  * <A>indices_objs</A>: the indices of the identity morphisms in the list-of-all-bases-elements in $B$.
#!  * <A>indices_gmors</A>: the indices of the generating morphisms in the list-of-all-bases-elements in $B$.
#!  * <A>sources_gmors</A>: the indices of sources of the generating morphisms in the list of objects of $B$.
#!  * <A>ranges_gmors</A>: the indices of ranges of the generating morphisms in the list of objects of $B$.
#!  * <A>bases_elms_comps</A>: a list of length <A>nr_bases_elms</A> of lists of elements in <A>[-1,-2,..,-nr_objs]</A> or <A>[1,2,..,nr_gmors]</A>.
#!     The $i$'th entry identifies the $i$'th element of list-of-all-bases-elements as an identity morphism or as a precomposition of generating morphisms.
#!  * <A>indices_of_bases_elms</A>: a list $L$ of length <A>nr_objs</A> of lists each of length <A>nr_objs</A> where the entry $L[i][j]$ is the list of indices
#!    of the basis elements of $\mathrm{Hom}_{B}(u_j,u_i)$ in the list-of-all-bases-elements in $B$ where $u_i$ and $u_j$ are the $i$'th resp. $j$'th objects.
#!  * <A>hom_structure_gmors_objs</A>: a list $L$ of length <A>nr_objs</A> of lists of length <A>nr_gmors</A> where the entry $L[i][j]$
#!    is the list of entries of the matrix of the $k$-linear map $\mathrm{Hom}_{B}(m_j,u_i)$ where $u_i$ and $m_j$ are the $i$'th object and the $j$'th generating morphism.
#!  * <A>hom_structure_objs_gmors</A>: a list $L$ of length <A>nr_objs</A> of lists of length <A>nr_gmors</A> where the entry $L[i][j]$
#!    is the list of entries of the matrix of the $k$-linear map $\mathrm{Hom}_{B}(u_i,m_j)$ where $u_i$ and $m_j$ are the $i$'th object and the $j$'th generating morphism.
#! @Arguments data_tables
#! @Returns a &CAP; category
DeclareAttribute( "AlgebroidFromDataTables",
        IsRecord );
#! @InsertChunk AlgebroidFromDataTables

DeclareGlobalFunction( "ADD_FUNCTIONS_FOR_AdditiveClosureOfAlgebroidFromDataTables" );

####################################
#
#! @Section Attributes
#
####################################

if false then
#! @Description
#!  The argument is a $k$-algebroid <A>A</A> defined by a finite dimensional quiver-algebra.
#!  This operation extracts a data-tables record from <A>A</A> which can be used to construct an algebroid $B$, that is isomorphic to <A>A</A>.
#! @Arguments A
#! @Returns a &CAP; functor
DeclareAttribute( "DataTablesOfCategory",
        IsAlgebroid );
fi;

#! @Description
#!  The arguments is a $k$-algebroid $A$ defined by a finite dimensional quiver-algebra.
#!  The output is an isomorphism functor from <A>A</A> onto the isomorphic $k$-algebroid $B:=$<C>AlgebroidFromDataTables</C>(<C>DataTablesOfCategory</C>(<A>A</A>)).
#! @Arguments A
#! @Returns a &CAP; functor
DeclareAttribute( "IsomorphismOntoAlgebroidFromDataTables",
        IsAlgebroid );

#! @Description
#!  The arguments is a $k$-algebroid $A$ defined by a finite dimensional quiver-algebra.
#!  The output is an isomorphism functor Onto <A>A</A> from the isomorphic $k$-algebroid $B:=$<C>AlgebroidFromDataTables</C>(<C>DataTablesOfCategory</C>(<A>A</A>)).
#! @Arguments A
#! @Returns a &CAP; functor
DeclareAttribute( "IsomorphismFromAlgebroidFromDataTables",
        IsAlgebroid );

#! @Description
#!  The arguments are an algebroid $B$ and a list <A>I</A> of morphisms in $B$.
#!  The output is the quotient category $B/I$ of $B$ modulo the two-sided ideal of morphisms generated by <A>I</A>.
#! @Arguments B, I
#! @Returns a record
DeclareOperation( "QuotientCategory",
        [ IsAlgebroidFromDataTables, IsDenseList ] );

#! @Description
#!  The data tables used to define $B$ enhanced with further key values.
#! @Arguments B
#! @Returns a record
DeclareAttribute( "EnhancedDataTables",
        IsAlgebroidFromDataTables );

CapJitAddTypeSignature( "EnhancedDataTables", [ IsAlgebroidFromDataTables ],
  function ( input_types )

    return rec( filter := IsNTuple,
                element_types :=
                [ # (1) ring
                  rec( filter := IsHomalgRing ),
                  
                  # (2) nr_objs
                  rec( filter := IsInt ),
                  
                  # (3) labels_objs
                  rec( filter := IsList,
                       element_type := rec( filter := IsString ) ),
                  
                  # (4) latex_strings_objs
                  rec( filter := IsList,
                       element_type := rec( filter := IsString ) ),
                  
                  # (5) indices_objs
                  rec( filter := IsList,
                       element_type := rec( filter := IsInt ) ),
                  
                  # (6) nr_gmors
                  rec( filter := IsInt ),
                  
                  # (7) labels_gmors
                  rec( filter := IsList,
                       element_type := rec( filter := IsString ) ),
                  
                  # (8) latex_strings_gmors
                  rec( filter := IsList,
                       element_type := rec( filter := IsString ) ),
                  
                  # (9) indices_gmors
                  rec( filter := IsList,
                       element_type := rec( filter := IsInt ) ),
                  
                  # (10) sources_gmors
                  rec( filter := IsList,
                       element_type := rec( filter := IsInt ) ),
                  
                  # (11) ranges_gmors
                  rec( filter := IsList,
                       element_type := rec( filter := IsInt ) ),
                  
                  # (12) nr_bases_elms
                  rec( filter := IsInt ),
                  
                  # (13) bases_elms_comps
                  rec( filter := IsList,
                       element_type := rec( filter := IsList,
                                            element_type := rec( filter := IsInt ) ) ),
                  
                  # (14) labels_of_bases_elms
                  rec( filter := IsList,
                       element_type := rec( filter := IsString ) ),
                  
                  # (15) latex_strings_of_bases_elms
                  rec( filter := IsList,
                       element_type := rec( filter := IsString ) ),
                  
                  # (16) indices_of_bases_elms
                  rec( filter := IsList,
                       element_type := rec( filter := IsList,
                                            element_type := rec( filter := IsList,
                                                                 element_type := rec( filter := IsInt ) ) ) ),
                  
                  # (17) hom_structure_objs_gmors
                  rec( filter := IsList,
                       element_type := rec( filter := IsList,
                                            element_type := rec( filter := IsList,
                                                                 element_type := rec( filter := IsList,
                                                                                      element_type := rec( filter := IsHomalgRingElement ) ) ) ) ),
                  
                  # (18) hom_structure_gmors_objs
                  rec( filter := IsList,
                       element_type := rec( filter := IsList,
                                            element_type := rec( filter := IsList,
                                                                 element_type := rec( filter := IsList,
                                                                                      element_type := rec( filter := IsHomalgRingElement ) ) ) ) ),
                  
                  # (19) hom_structure_ranks
                  rec( filter := IsList,
                       element_type := rec( filter := IsList,
                                            element_type := rec( filter := IsInt ) ) ),
                  
                  # (20) hom_structure_on_bases_elms
                  rec( filter := IsList,
                       element_type := rec( filter := IsList,
                                            element_type := rec( filter := IsList,
                                                                 element_type := rec( filter := IsList,
                                                                                      element_type := rec( filter := IsList,
                                                                                                           element_type := rec( filter := IsList,
                                                                                                                                element_type := rec( filter := IsList,
                                                                                                                                                      element_type := rec( filter := IsList,
                                                                                                                                                                            element_type := rec( filter := IsHomalgRingElement ) ) ) ) ) ) ) ) ),
                  
                  # (21) indices_composable_gmors
                  rec( filter := IsList,
                       element_type := rec( filter := IsList,
                                            element_type := rec( filter := IsList,
                                                                 element_type := rec( filter := IsInt ) ) ) ),
                  
                  # (22) colors
                  rec( filter := IsRecord ) ] );

end );

#! @Description
#!  The argument is an algebroid <A>B</A>.
#!  The output is the finite set of objects of <A>B</A>.
#! @Arguments B
#! @Returns a list of &CAP; category objects
DeclareAttribute( "SetOfObjects", IsAlgebroidFromDataTables );

CapJitAddTypeSignature( "SetOfObjects", [ IsAlgebroidFromDataTables ],
  function ( input_types )
    
    return rec( filter := IsList,
                element_type := CapJitDataTypeOfObjectOfCategory( input_types[1].category ) );
    
end );

#! @Description
#!  The argument is an algebroid <A>B</A>.
#!  The output is the finite set of generating morphisms of <A>B</A>.
#! @Arguments B
#! @Returns a list of a &CAP; category morphisms
DeclareAttribute( "SetOfGeneratingMorphisms", IsAlgebroidFromDataTables );

CapJitAddTypeSignature( "SetOfGeneratingMorphisms", [ IsAlgebroidFromDataTables ],
  function ( input_types )
    
    return rec( filter := IsList,
                element_type := CapJitDataTypeOfMorphismOfCategory( input_types[1].category ) );
    
end );

#! @Description
#!  The argument is an algebroid <A>B</A>.
#!  The output is a list of lists $L$ where $L[i][j]$ is the basis of the external hom $\mathrm{Hom}_B(u,v)$ where $u$ and $v$ are $i$'th resp. $j$'th objects in $B$.
#! @Arguments B
#! @Returns a list of lists
DeclareAttribute( "SetOfBasesOfExternalHoms", IsAlgebroidFromDataTables );

#! @Description
#!  The arguments are an algebroid <A>B</A> and a non-negative integer <A>i</A>.
#!  The output is a generating set for $\mathfrak{m}^i$ where $\mathfrak{m}$ is
#!  the ideal generated by all generating morphisms in <A>B</A>.
#! @Arguments B, i
#! @Returns a list
KeyDependentOperation( "PowerOfArrowIdeal", IsAlgebroidFromDataTables, IsInt, ReturnTrue );

####################################
#
#! @Section Properties
#
####################################

#! @Description
#!  The arguments are an algebroid <A>B</A> linear over a field $k$.
#!  This output is <C>true</C> iff the following two conditions hold:
#!  (1) the union of all identity morphisms and all generating morphism
#!  remain linear independent in the quotient category $C/\mathfrak{m}^2$;
#!  (2) $\mathfrak{m}^i=0$ for some $i\in\mathbb{N}$,
#!  where $\mathfrak{m}^i=$<C>PowerOfArrowIdeal</C>(<A>B</A>,$i$).
#! @Arguments B, i
#! @Returns a list
DeclareProperty( "IsAdmissibleAlgebroid", IsAlgebroidFromDataTables );
#! @InsertChunk AdmissibleAlgebroidFromDataTables

####################################
#
#! @Section Operations
#
####################################

#! @Description
#!  The arguments are an algebroid <A>B</A> and a string <A>optional_string</A>.
#!  This operation assigns the objects of <A>B</A> to global variables.
#!  Names of the variables are the concatenation of the labels of the objects of <A>B</A> with <A>optional_string</A>.
#!  The default value of <A>optional_string</A> is the empty string.
#! @Arguments B [, optional_string]
#! @Returns nothing
DeclareOperation( "AssignSetOfObjects",
        [ IsAlgebroidFromDataTables, IsString ] );

#! @Description
#!  The arguments are an algebroid <A>B</A> and a string <A>optional_string</A>.
#!  This operation assigns the generating morphisms of <A>B</A> to global variables.
#!  Names of the variables are the concatenation of the labels of the generating morphisms of <A>B</A> with <A>optional_string</A>.
#!  The default value of <A>optional_string</A> is the empty string.
#! @Arguments B [, optional_string]
#! @Returns nothing
DeclareOperation( "AssignSetOfGeneratingMorphisms",
        [ IsAlgebroidFromDataTables, IsString ] );

#! @Description
#!  The arguments are an algebroid <A>B</A> and an integer <A>i</A>.
#!  The output is the <A>i</A>'th object in <C>SetOfObjects</C>(<A>B</A>).
#! @Arguments B, i
#! @Returns a &CAP; category object
DeclareOperation( "CreateObject",
            [ IsAlgebroidFromDataTables, IsInt ] );

#! @Description
#!  The argument is an object <A>v</A> in an algebroid <A>B</A>.
#!  The output is the index of <A>v</A> in <C>SetOfObjects</C>(<A>B</A>).
#! @Arguments v
#! @Returns an integer
DeclareAttribute( "ObjectIndex", IsAlgebroidFromDataTablesObject );

CapJitAddTypeSignature( "ObjectIndex", [ IsAlgebroidFromDataTablesObject ], IsInt );

#! @Description
#!  The arguments are an algebroid <A>B</A> (over a commutative ring $k$), two objects <A>u,v</A> in <A>B</A> and list <A>coeffs</A> of elements in
#!  $k$ of length $\mathrm{dim}_k~\mathrm{Hom}_{B}(u,v)$.
#!  The output is the $k$-linear combination of the basis elements of $\mathrm{Hom}_B(u,v)$ with the coefficients-list <A>coeffs</A>.
#! @Arguments B, u, coeffs, v
#! @Returns a &CAP; category morphism
DeclareOperation( "CreateMorphism",
            [ IsAlgebroidFromDataTables, IsAlgebroidFromDataTablesObject, IsDenseList, IsAlgebroidFromDataTablesObject ] );

#! @Description
#!  The argument is a morphism <A>alpha</A> in an algebroid <A>B</A>.
#!  The output is the list of coefficients of <A>alpha</A> with respect to the basis of external hom $\mathrm{Hom}_B(u,v)$ where $u$ and $v$ are source resp. range of <A>alpha</A>.
#! @Arguments alpha
#! @Returns a &CAP; category morphism
DeclareAttribute( "MorphismCoefficients", IsAlgebroidFromDataTablesMorphism );

CapJitAddTypeSignature( "MorphismCoefficients", [ IsAlgebroidFromDataTablesMorphism ], function ( input_types )
    
    return rec( filter := IsList, element_type := rec( filter := IsHomalgRingElement ) );
    
end );

#! @Description
#!  The argument is a morphism <A>alpha</A> in an algebroid <A>B</A>.
#!  The output is the list of indices of the nonzero entries of <C>MorphismCoefficients</C>(<A>alpha</A>).
#! @Arguments alpha
#! @Returns a &CAP; category morphism
DeclareAttribute( "MorphismSupport", IsAlgebroidFromDataTablesMorphism );

CapJitAddTypeSignature( "MorphismSupport", [ IsAlgebroidFromDataTablesMorphism ], function ( input_types )
    
    return rec( filter := IsList, element_type := rec( filter := IsInt ) );
    
end );

#! @Description
#!  The argument is a morphism <A>alpha</A> in an algebroid $B$ (over a commutative ring $k$).
#!  The output is a list of pairs $L=[[c_1,l_1],..,[c_n,l_n]]$ where for each $i=1,\dots,n$,
#!  $c_i$ is a non-zero element in $k$ and $l_i$ is either a list containing an identity morphism or a list of (precomposable) generating morphisms such that
#!  <A>alpha</A> = $c_1\cdot\mathrm{PreCompose}(l_1)+..+c_n\cdot\mathrm{PreCompose}(l_n)$.
#! @Arguments alpha
#! @Returns a list of pairs
DeclareAttribute( "DecompositionOfMorphismInAlgebroid",
        IsAlgebroidFromDataTablesMorphism );

#! @Description
#!  The argument is an algebroid <A>B</A>.
#!  The ouput is the opposite algebroid $B^{\mathrm{op}}$ constructed as an algebroid from data tables.
#! @Arguments B
#! @Returns a &CAP; category
DeclareAttribute( "OppositeAlgebroid",
        IsAlgebroidFromDataTables );

#! @Description
#!  The arguments are two algebroids <A>A</A> and <A>B</A>.
#!  The output is the tensor product algebroid <A>A</A>$\otimes$<A>B</A>.
#! @Arguments A, B
#! @Returns a &CAP; category
DeclareOperation( "TensorProductOfAlgebroids",
            [ IsAlgebroidFromDataTables, IsAlgebroidFromDataTables ] );

#! @Description
#!  Delegates to <C>TensorProductOfAlgebroids</C>(<A>A</A>,<A>B</A>).
#! @Arguments A, B
#! @Returns a &CAP; category
DeclareOperation( "\*",
            [ IsAlgebroidFromDataTables, IsAlgebroidFromDataTables ] );

#! @Description
#!  The arguments are two objects <A>a</A>, <A>b</A> and a tensor product algebroid <A>T</A>$=A\otimes B$ where <A>a</A> and <A>b</A> belong to $A$ resp. $B$.
#!  The output is the object $a\otimes b$ in <A>T</A>.
#! @Arguments a, b, T
#! @Returns a &CAP; category object
DeclareOperation( "ElementaryTensor",
            [ IsAlgebroidFromDataTablesObject, IsAlgebroidFromDataTablesObject, IsAlgebroidFromDataTables ] );

#! @Description
#!  The arguments are two morphisms <A>f</A>, <A>g</A> and a tensor product algebroid <A>T</A>$=A\otimes B$ where <A>f</A> and <A>g</A> belong to $A$ resp. $B$.
#!  The output is the morphism $f\otimes g$ in <A>T</A>.
#! @Arguments f, g, T
#! @Returns a &CAP; category morphism
DeclareOperation( "ElementaryTensor",
            [ IsAlgebroidFromDataTablesMorphism, IsAlgebroidFromDataTablesMorphism, IsAlgebroidFromDataTables ] );

#! @Description
#!  The argument is an algebroid $B$ over a commutative ring $k$.
#!  The output is the presheaf object $F_{B}\in \mathrm{PSh}(B^{\mathrm{op}}\otimes B)$ which maps an object $u^{\mathrm{op}}\otimes t \in B^{\mathrm{op}}\otimes B$ to
#!  $\mathrm{Hom}_B(t,u) \in k\mbox{-}\mathrm{rows}$ and maps a morphism $g^{\mathrm{op}}\otimes f : v^{\mathrm{op}}\otimes s \to u^{\mathrm{op}}\otimes t \in B^{\mathrm{op}}\otimes B$
#!  to $f\bullet(-)\bullet g =\mathrm{Hom}_B(f,g): \mathrm{Hom}_B(t,u) \to \mathrm{Hom}_B(s,v) \in k\mbox{-}\mathrm{rows}$.
#! @Arguments B
#! @Returns a &CAP; category morphism
DeclareAttribute( "AlgebroidAsObjectInPreSheavesCategory", IsAlgebroidFromDataTables );

DeclareAttribute( "AlgebroidAsObjectInPreSheavesCategoryData", IsAlgebroidFromDataTables );

#! @Description
#!  The argument is a morphism $\alpha: t \to u$ in an algebroid $B$ over a commutative ring $k$.
#!  The output is the morphism $\lambda_{\alpha}:P_{u^{\mathrm{op}}\otimes t} \to F_{B}$ where $P_{u^{\mathrm{op}}\otimes t}$ is the image of $u^{\mathrm{op}}\otimes t$ under the Yoneda embdding
#!  $B^{\mathrm{op}}\otimes B \hookrightarrow \mathrm{PSh}(B^{\mathrm{op}}\otimes B)$; and $\lambda_{\alpha}$ the image of $\alpha$ under the natural isomorphism
#!  $\mathrm{Hom}_{B}(t,u) = F_{B}(u^{\mathrm{op}}\otimes t) \simeq \mathrm{Hom}_{\mathrm{PSh}(B^{\mathrm{op}}\otimes B)}(P_{u^{\mathrm{op}}\otimes t},F_{B})$.
#! @Arguments alpha
#! @Returns a &CAP; category morphism
DeclareAttribute( "AssociatedMorphismIntoAlgebroidAsObjectInPreSheavesCategory", IsAlgebroidFromDataTablesMorphism );

DeclareAttribute( "SetOfBasesOfExternalHomsLazyHList", IsAlgebroidFromDataTables );

CapJitAddTypeSignature( "SetOfBasesOfExternalHomsLazyHList", [ IsAlgebroidFromDataTables ], function ( input_types )
    
    return rec( filter := IsList,
                element_type := rec(  filter := IsList,
                                      element_type := rec( filter := IsList,
                                                           element_type := CapJitDataTypeOfMorphismOfCategory( input_types[1].category ) ) ) );
    
end );

