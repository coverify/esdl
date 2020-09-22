module esdl.intf.z3.api.z3_polynomial;
import esdl.intf.z3.api.z3_types;
import esdl.intf.z3.api.z3_api;

/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    z3_polynomial.h

Abstract:

    Additional APIs for polynomials.

Author:

    Leonardo de Moura (leonardo) 2012-12-09

Notes:

--*/

version(LDC) {
  import ldc.attributes;
}
 else {
   enum weak;
 }

// __cplusplus

/** \defgroup capi C API */
/*@{*/

/** @name Polynomials */
/*@{*/

/**
   \brief Return the nonzero subresultants of \c p and \c q with respect to the "variable" \c x.

   \pre \c p, \c q and \c x are Z3 expressions where \c p and \c q are arithmetic terms.
   Note that, any subterm that cannot be viewed as a polynomial is assumed to be a variable.
   Example: \ccode{f(a)} is a considered to be a variable in the polynomial \ccode{
   f(a)*f(a) + 2*f(a) + 1}

   def_API('Z3_polynomial_subresultants', AST_VECTOR, (_in(CONTEXT), _in(AST), _in(AST), _in(AST)))
*/
extern(C) Z3_ast_vector Z3_polynomial_subresultants (Z3_context c, Z3_ast p, Z3_ast q, Z3_ast x);

/*@}*/
/*@}*/

// __cplusplus

