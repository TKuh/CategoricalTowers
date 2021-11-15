# SPDX-License-Identifier: GPL-2.0-or-later
# Toposes: Elementary toposes
#
# Implementations
#

##
InstallGlobalFunction( CreateFilesForToposesPackage,
  function( )

##
WriteFileForMonoidalStructure(
        rec(
             IsMonoidalCategory := "IsCartesianCategory",
             IsStrictMonoidalCategory := "IsStrictCartesianCategory",
             IsBraidedMonoidalCategory := "IsCartesianCategory",
             IsSymmetricMonoidalCategory := "IsCartesianCategory",
             AdditiveMonoidal := "DistributiveCartesian",
             TensorProductOnObjects := "DirectProduct",
             TensorProduct := "DirectProduct",
             TensorUnit := "TerminalObject",
             Associator := "CartesianAssociator",
             LeftUnitor := "CartesianLeftUnitor",
             RightUnitor := "CartesianRightUnitor",
             Distributivity := "CartesianDistributivity",
             DirectSum := "Coproduct",
             Braiding := "CartesianBraiding",
             Lambda := "CartesianLambda",
             Evaluation := "CartesianEvaluation",
             Coevaluation := "CartesianCoevaluation",
             MONOIDAL := "CARTESIAN",
             Monoidal := "Cartesian",
             monoidal := "cartesian",
             tensor_object := "direct_product_object",
             tensored := "x",
             otimes := "times",
             oplus := "sqcup",
             tensor_product := "direct_product",
             tensorSproduct := "direct product",
             AdditiveS := "",
             BraidedS := "",
             TensorProductOnObjectsBCcat := "DirectProduct(",
             ),
        "Toposes",
        rec( MonoidalCategoriesDoc_gd := "CartesianCategoriesDoc.gd",
             MonoidalCategoriesTensorProductAndUnit_gd := fail,
             MonoidalCategories_gd := "CartesianCategories.gd",
             AdditiveMonoidalCategories_gd := "DistributiveCartesianCategories.gd",
             BraidedMonoidalCategoriesDoc_gd := fail,
             BraidedMonoidalCategories_gd := "BraidedCartesianCategories.gd",
             SymmetricMonoidalCategoriesDoc_gd := fail,
             MonoidalCategoriesTensorProductAndUnitMethodRecord_gi := fail,
             MonoidalCategoriesTensorProductAndUnit_gi := fail,
             MonoidalCategoriesMethodRecord_gi := "CartesianCategoriesMethodRecord.gi",
             MonoidalCategories_gi := "CartesianCategories.gi",
             AdditiveMonoidalCategoriesMethodRecord_gi := "DistributiveCartesianCategoriesMethodRecord.gi",
             AdditiveMonoidalCategories_gi := "DistributiveCartesianCategories.gi",
             BraidedMonoidalCategoriesMethodRecord_gi := "BraidedCartesianCategoriesMethodRecord.gi",
             BraidedMonoidalCategories_gi := "BraidedCartesianCategories.gi",
             MonoidalCategoriesDerivedMethods_gi := "CartesianCategoriesDerivedMethods.gi",
             AdditiveMonoidalCategoriesDerivedMethods_gi := fail,
             BraidedMonoidalCategoriesDerivedMethods_gi := "BraidedCartesianCategoriesDerivedMethods.gi",
             SymmetricMonoidalCategoriesDerivedMethods_gi := "SymmetricCartesianCategoriesDerivedMethods.gi",
             )
        );

##
WriteFileForClosedMonoidalStructure(
        rec(
             IsMonoidalCategory := "IsCartesianCategory",
             IsStrictMonoidalCategory := "IsStrictCartesianCategory",
             IsBraidedMonoidalCategory := "IsCartesianCategory",
             IsSymmetricMonoidalCategory := "IsCartesianCategory",
             IsClosedMonoidalCategory := "IsCartesianClosedCategory",
             IsSymmetricClosedMonoidalCategory := "IsCartesianClosedCategory",
             AdditiveMonoidal := "DistributiveCartesian",
             TensorProductOnObjects := "DirectProduct",
             TensorProduct := "DirectProduct",
             TensorUnit := "TerminalObject",
             Associator := "CartesianAssociator",
             LeftUnitor := "CartesianLeftUnitor",
             RightUnitor := "CartesianRightUnitor",
             Distributivity := "CartesianDistributivity",
             DirectSum := "Coproduct",
             Braiding := "CartesianBraiding",
             Lambda := "CartesianLambda",
             Evaluation := "CartesianEvaluation",
             Coevaluation := "CartesianCoevaluation",
             InternalHom := "Exponential",
             ClosedMonoidalCategories := "CartesianClosedCategories",
             CLOSED_MONOIDAL := "CARTESIAN_CLOSED",
             ClosedMonoidal := "Cartesian",
             MONOIDAL := "CARTESIAN",
             Monoidal := "Cartesian",
             monoidal := "cartesian",
             Dual := "CartesianDual",
             Bidual := "CartesianBidual",
             tensor_object := "direct_product_object",
             tensored := "x",
             otimes := "times",
             oplus := "sqcup",
             tensor_product := "direct_product",
             tensorSproduct := "direct product",
             tensor_hom := "direct product-exponential",
             Hom := "Exponential",
             ClosedSMonoidal := "Cartesian Closed",
             TensorProductOnObjectsBCcat := "DirectProduct(",
             ),
        "Toposes",
        rec( ClosedMonoidalCategoriesDoc_gd := "CartesianClosedCategoriesDoc.gd",
             ClosedMonoidalCategories_gd := "CartesianClosedCategories.gd",
             SymmetricClosedMonoidalCategoriesDoc_gd := fail,
             RigidSymmetricClosedMonoidalCategoriesDoc_gd := fail,
             RigidSymmetricClosedMonoidalCategories_gd := fail,
             ClosedMonoidalCategoriesMethodRecord_gi := "CartesianClosedCategoriesMethodRecord.gi",
             ClosedMonoidalCategories_gi := "CartesianClosedCategories.gi",
             RigidSymmetricClosedMonoidalCategoriesMethodRecord_gi := fail,
             RigidSymmetricClosedMonoidalCategories_gi := fail,
             ClosedMonoidalCategoriesDerivedMethods_gi := "CartesianClosedCategoriesDerivedMethods.gi",
             SymmetricClosedMonoidalCategoriesDerivedMethods_gi := "SymmetricCartesianClosedCategoriesDerivedMethods.gi",
             RigidSymmetricClosedMonoidalCategoriesDerivedMethods_gi := fail,
             )
        );

##
WriteFileForMonoidalStructure(
        rec(
             IsMonoidalCategory := "IsCocartesianCategory",
             IsStrictMonoidalCategory := "IsStrictCocartesianCategory",
             IsBraidedMonoidalCategory := "IsCocartesianCategory",
             IsSymmetricMonoidalCategory := "IsCocartesianCategory",
             AdditiveMonoidal := "DistributiveCocartesian",
             TensorProductOnObjects := "Coproduct",
             TensorProduct := "Coproduct",
             TensorUnit := "InitialObject",
             Associator := "CocartesianAssociator",
             LeftUnitor := "CocartesianLeftUnitor",
             RightUnitor := "CocartesianRightUnitor",
             Distributivity := "CocartesianDistributivity",
             DirectSum := "DirectProduct",
             Braiding := "CocartesianBraiding",
             CoLambda := "CocartesianLambda",
             CoclosedEvaluation := "CocartesianEvaluation",
             CoclosedCoevaluation := "CocartesianCoevaluation",
             MONOIDAL := "COCARTESIAN",
             Monoidal := "Cocartesian",
             monoidal := "cocartesian",
             tensor_object := "coproduct_object",
             tensored := "u",
             otimes := "sqcup",
             oplus := "times",
             tensor_product := "coproduct",
             tensorSproduct := "coproduct",
             AdditiveS := "",
             BraidedS := "",
             TensorProductOnObjectsBCcat := "Coproduct(",
             ),
        "Toposes",
        rec( MonoidalCategoriesDoc_gd := "CocartesianCategoriesDoc.gd",
             MonoidalCategoriesTensorProductAndUnit_gd := fail,
             MonoidalCategories_gd := "CocartesianCategories.gd",
             AdditiveMonoidalCategories_gd := "DistributiveCocartesianCategories.gd",
             BraidedMonoidalCategoriesDoc_gd := fail,
             BraidedMonoidalCategories_gd := "BraidedCocartesianCategories.gd",
             SymmetricMonoidalCategoriesDoc_gd := fail,
             MonoidalCategoriesTensorProductAndUnitMethodRecord_gi := fail,
             MonoidalCategoriesTensorProductAndUnit_gi := fail,
             MonoidalCategoriesMethodRecord_gi := "CocartesianCategoriesMethodRecord.gi",
             MonoidalCategories_gi := "CocartesianCategories.gi",
             AdditiveMonoidalCategoriesMethodRecord_gi := "DistributiveCocartesianCategoriesMethodRecord.gi",
             AdditiveMonoidalCategories_gi := "DistributiveCocartesianCategories.gi",
             BraidedMonoidalCategoriesMethodRecord_gi := "BraidedCocartesianCategoriesMethodRecord.gi",
             BraidedMonoidalCategories_gi := "BraidedCocartesianCategories.gi",
             MonoidalCategoriesDerivedMethods_gi := "CocartesianCategoriesDerivedMethods.gi",
             AdditiveMonoidalCategoriesDerivedMethods_gi := fail,
             BraidedMonoidalCategoriesDerivedMethods_gi := "BraidedCocartesianCategoriesDerivedMethods.gi",
             SymmetricMonoidalCategoriesDerivedMethods_gi := "SymmetricCocartesianCategoriesDerivedMethods.gi",
             )
        );

##
WriteFileForCoclosedMonoidalStructure(
        rec(
             IsMonoidalCategory := "IsCocartesianCategory",
             IsStrictMonoidalCategory := "IsStrictCocartesianCategory",
             IsBraidedMonoidalCategory := "IsCocartesianCategory",
             IsSymmetricMonoidalCategory := "IsCocartesianCategory",
             IsCoclosedMonoidalCategory := "IsCocartesianCoclosedCategory",
             IsSymmetricCoclosedMonoidalCategory := "IsCocartesianCoclosedCategory",
             AdditiveMonoidal := "DistributiveCocartesian",
             TensorProductOnObjects := "Coproduct",
             TensorProduct := "Coproduct",
             TensorUnit := "InitialObject",
             Associator := "CocartesianAssociator",
             LeftUnitor := "CocartesianLeftUnitor",
             RightUnitor := "CocartesianRightUnitor",
             Distributivity := "CocartesianDistributivity",
             DirectSum := "DirectProduct",
             Braiding := "CocartesianBraiding",
             CoLambda := "CocartesianLambda",
             CoclosedEvaluation := "CocartesianEvaluation",
             CoclosedCoevaluation := "CocartesianCoevaluation",
             InternalCoHom := "Coexponential",
             CoclosedMonoidalCategories := "CocartesianCoclosedCategories",
             COCLOSED_MONOIDAL := "COCARTESIAN_COCLOSED",
             CoclosedMonoidal := "Cocartesian",
             MONOIDAL := "COCARTESIAN",
             Monoidal := "Cocartesian",
             monoidal := "cocartesian",
             CoDual := "CocartesianDual",
             CoBidual := "CocartesianBidual",
             tensor_object := "coproduct_object",
             tensored := "u",
             otimes := "sqcup",
             oplus := "times",
             tensor_product := "coproduct",
             tensorSproduct := "coproduct",
             coHom_tensor := "coexponential-coproduct",
             coHom := "Coexponential",
             CoclosedSMonoidal := "Cocartesian Coclosed",
             TensorProductOnObjectsBCcat := "Coproduct(",
             ),
        "Toposes",
        rec( CoclosedMonoidalCategoriesDoc_gd := "CocartesianCoclosedCategoriesDoc.gd",
             CoclosedMonoidalCategories_gd := "CocartesianCoclosedCategories.gd",
             SymmetricCoclosedMonoidalCategoriesDoc_gd := fail,
             RigidSymmetricCoclosedMonoidalCategoriesDoc_gd := fail,
             RigidSymmetricCoclosedMonoidalCategories_gd := fail,
             CoclosedMonoidalCategoriesMethodRecord_gi := "CocartesianCoclosedCategoriesMethodRecord.gi",
             CoclosedMonoidalCategories_gi := "CocartesianCoclosedCategories.gi",
             RigidSymmetricCoclosedMonoidalCategoriesMethodRecord_gi := fail,
             RigidSymmetricCoclosedMonoidalCategories_gi := fail,
             CoclosedMonoidalCategoriesDerivedMethods_gi := "CocartesianCoclosedCategoriesDerivedMethods.gi",
             SymmetricCoclosedMonoidalCategoriesDerivedMethods_gi := "SymmetricCocartesianCoclosedCategoriesDerivedMethods.gi",
             RigidSymmetricCoclosedMonoidalCategoriesDerivedMethods_gi := fail,
             )
        );

end );
