# THIS FILE WAS AUTOMATICALLY GENERATED

# SPDX-License-Identifier: GPL-2.0-or-later
# Toposes: Elementary toposes
#
# Implementations
#

InstallValue( BRAIDED_CARTESIAN_CATEGORIES_METHOD_NAME_RECORD, rec(

CartesianBraiding := rec(
  filter_list := [ "category", "object", "object" ],
  io_type := [ [ "a", "b" ], [ "s", "r" ] ],
  output_source_getter_string := "BinaryDirectProduct( cat, a, b )",
  output_range_getter_string := "BinaryDirectProduct( cat, b, a )",
  with_given_object_position := "both",
  return_type := "morphism",
  dual_operation := "CartesianBraidingInverse",
  dual_arguments_reversed := false,
),

CartesianBraidingWithGivenDirectProducts := rec(
  filter_list := [ "category", "object", "object", "object", "object" ],
  io_type := [ [ "s", "a", "b", "r" ], [ "s", "r" ] ],
  return_type := "morphism",
  dual_operation := "CartesianBraidingInverseWithGivenDirectProducts",
  dual_preprocessor_func := { cat, s, a, b, r } -> [ Opposite( cat ), Opposite( r ), Opposite( a ), Opposite( b ), Opposite( s ) ],
  dual_arguments_reversed := false,
),

CartesianBraidingInverse := rec(
  filter_list := [ "category", "object", "object" ],
  io_type := [ [ "a", "b" ], [ "s", "r" ] ],
  output_source_getter_string := "BinaryDirectProduct( cat, b, a )",
  output_range_getter_string := "BinaryDirectProduct( cat, a, b )",
  with_given_object_position := "both",
  return_type := "morphism",
  dual_operation := "CartesianBraiding",
  dual_arguments_reversed := false,
),

CartesianBraidingInverseWithGivenDirectProducts := rec(
  filter_list := [ "category", "object", "object", "object", "object" ],
  io_type := [ [ "s", "a", "b", "r" ], [ "s", "r" ] ],
  return_type := "morphism",
  dual_operation := "CartesianBraidingWithGivenDirectProducts",
  dual_preprocessor_func := { cat, s, a, b, r } -> [ Opposite( cat ), Opposite( s ), Opposite( a ), Opposite( b ), Opposite( r ) ],
  dual_arguments_reversed := false,
),

) );

CAP_INTERNAL_ENHANCE_NAME_RECORD( BRAIDED_CARTESIAN_CATEGORIES_METHOD_NAME_RECORD );

CAP_INTERNAL_GENERATE_DOCUMENTATION_FROM_METHOD_NAME_RECORD(
    BRAIDED_CARTESIAN_CATEGORIES_METHOD_NAME_RECORD,
    "Toposes",
    "BraidedCartesianCategories.autogen.gd",
    "Cartesian Categories",
    "Add-methods"
);

CAP_INTERNAL_REGISTER_METHOD_NAME_RECORD_OF_PACKAGE( BRAIDED_CARTESIAN_CATEGORIES_METHOD_NAME_RECORD, "Toposes" );

CAP_INTERNAL_INSTALL_ADDS_FROM_RECORD( BRAIDED_CARTESIAN_CATEGORIES_METHOD_NAME_RECORD );
