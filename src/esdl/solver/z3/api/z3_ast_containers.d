module esdl.solver.z3.api.z3_ast_containers;

import esdl.solver.z3.api.z3_types;
import esdl.solver.z3.api.z3_api;

/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    z3_ast_containers.h

Abstract:

    AST Containers

Author:

    Christoph M. Wintersteiger (cwinter) 2015-12-03

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

/** @name AST vectors */
/*@{*/
/**
   \brief Return an empty AST vector.

   \remark Reference counting must be used to manage AST vectors, even when the Z3_context was
   created using #Z3_mk_context instead of #Z3_mk_context_rc.

   def_API('Z3_mk_ast_vector', AST_VECTOR, (_in(CONTEXT),))
*/
extern(C) Z3_ast_vector Z3_mk_ast_vector (Z3_context c);

/**
   \brief Increment the reference counter of the given AST vector.

   def_API('Z3_ast_vector_inc_ref', VOID, (_in(CONTEXT), _in(AST_VECTOR)))
*/
extern(C) void Z3_ast_vector_inc_ref (Z3_context c, Z3_ast_vector v);

/**
   \brief Decrement the reference counter of the given AST vector.

   def_API('Z3_ast_vector_dec_ref', VOID, (_in(CONTEXT), _in(AST_VECTOR)))
*/
extern(C) void Z3_ast_vector_dec_ref (Z3_context c, Z3_ast_vector v);

/**
   \brief Return the size of the given AST vector.

   def_API('Z3_ast_vector_size', UINT, (_in(CONTEXT), _in(AST_VECTOR)))
*/
extern(C) uint Z3_ast_vector_size (Z3_context c, Z3_ast_vector v);

/**
   \brief Return the AST at position \c i in the AST vector \c v.

   \pre i < Z3_ast_vector_size(c, v)

   def_API('Z3_ast_vector_get', AST, (_in(CONTEXT), _in(AST_VECTOR), _in(UINT)))
*/
extern(C) Z3_ast Z3_ast_vector_get (Z3_context c, Z3_ast_vector v, uint i);

/**
   \brief Update position \c i of the AST vector \c v with the AST \c a.

   \pre i < Z3_ast_vector_size(c, v)

   def_API('Z3_ast_vector_set', VOID, (_in(CONTEXT), _in(AST_VECTOR), _in(UINT), _in(AST)))
*/
extern(C) void Z3_ast_vector_set (Z3_context c, Z3_ast_vector v, uint i, Z3_ast a);

/**
   \brief Resize the AST vector \c v.

   def_API('Z3_ast_vector_resize', VOID, (_in(CONTEXT), _in(AST_VECTOR), _in(UINT)))
*/
extern(C) void Z3_ast_vector_resize (Z3_context c, Z3_ast_vector v, uint n);

/**
   \brief Add the AST \c a in the end of the AST vector \c v. The size of \c v is increased by one.

   def_API('Z3_ast_vector_push', VOID, (_in(CONTEXT), _in(AST_VECTOR), _in(AST)))
*/
extern(C) void Z3_ast_vector_push (Z3_context c, Z3_ast_vector v, Z3_ast a);

/**
   \brief Translate the AST vector \c v from context \c s into an AST vector in context \c t.

   def_API('Z3_ast_vector_translate', AST_VECTOR, (_in(CONTEXT), _in(AST_VECTOR), _in(CONTEXT)))
*/
extern(C) Z3_ast_vector Z3_ast_vector_translate (Z3_context s, Z3_ast_vector v, Z3_context t);

/**
   \brief Convert AST vector into a string.

   def_API('Z3_ast_vector_to_string', STRING, (_in(CONTEXT), _in(AST_VECTOR)))
*/
extern(C) Z3_string Z3_ast_vector_to_string (Z3_context c, Z3_ast_vector v);

/*@}*/

/** @name AST maps */
/*@{*/
/**
\brief Return an empty mapping from AST to AST

\remark Reference counting must be used to manage AST maps, even when the Z3_context was
created using #Z3_mk_context instead of #Z3_mk_context_rc.

def_API('Z3_mk_ast_map', AST_MAP, (_in(CONTEXT),) )
*/
@weak Z3_ast_map Z3_mk_ast_map (Z3_context c) {
  assert (false, Z3NotLoadedError);
}

/**
\brief Increment the reference counter of the given AST map.

def_API('Z3_ast_map_inc_ref', VOID, (_in(CONTEXT), _in(AST_MAP)))
*/
@weak void Z3_ast_map_inc_ref (Z3_context c, Z3_ast_map m) {
  assert (false, Z3NotLoadedError);
}

/**
\brief Decrement the reference counter of the given AST map.

def_API('Z3_ast_map_dec_ref', VOID, (_in(CONTEXT), _in(AST_MAP)))
*/
@weak void Z3_ast_map_dec_ref (Z3_context c, Z3_ast_map m) {
  assert (false, Z3NotLoadedError);
}

/**
\brief Return true if the map \c m contains the AST key \c k.

def_API('Z3_ast_map_contains', BOOL, (_in(CONTEXT), _in(AST_MAP), _in(AST)))
*/
@weak bool Z3_ast_map_contains (Z3_context c, Z3_ast_map m, Z3_ast k) {
  assert (false, Z3NotLoadedError);
}

/**
\brief Return the value associated with the key \c k.

The procedure invokes the error handler if \c k is not in the map.

def_API('Z3_ast_map_find', AST, (_in(CONTEXT), _in(AST_MAP), _in(AST)))
*/
@weak Z3_ast Z3_ast_map_find (Z3_context c, Z3_ast_map m, Z3_ast k) {
  assert (false, Z3NotLoadedError);
}

/**
\brief Store/Replace a new key, value pair in the given map.

def_API('Z3_ast_map_insert', VOID, (_in(CONTEXT), _in(AST_MAP), _in(AST), _in(AST)))
*/
@weak void Z3_ast_map_insert (Z3_context c, Z3_ast_map m, Z3_ast k, Z3_ast v) {
  assert (false, Z3NotLoadedError);
}

/**
\brief Erase a key from the map.

def_API('Z3_ast_map_erase', VOID, (_in(CONTEXT), _in(AST_MAP), _in(AST)))
*/
@weak void Z3_ast_map_erase (Z3_context c, Z3_ast_map m, Z3_ast k) {
  assert (false, Z3NotLoadedError);
}

/**
\brief Remove all keys from the given map.

def_API('Z3_ast_map_reset', VOID, (_in(CONTEXT), _in(AST_MAP)))
*/
@weak void Z3_ast_map_reset (Z3_context c, Z3_ast_map m) {
  assert (false, Z3NotLoadedError);
}

/**
\brief Return the size of the given map.

def_API('Z3_ast_map_size', UINT, (_in(CONTEXT), _in(AST_MAP)))
*/
@weak uint Z3_ast_map_size (Z3_context c, Z3_ast_map m) {
  assert (false, Z3NotLoadedError);
}

/**
\brief Return the keys stored in the given map.

def_API('Z3_ast_map_keys', AST_VECTOR, (_in(CONTEXT), _in(AST_MAP)))
*/
@weak Z3_ast_vector Z3_ast_map_keys (Z3_context c, Z3_ast_map m) {
  assert (false, Z3NotLoadedError);
}

/**
\brief Convert the given map into a string.

def_API('Z3_ast_map_to_string', STRING, (_in(CONTEXT), _in(AST_MAP)))
*/
@weak Z3_string Z3_ast_map_to_string (Z3_context c, Z3_ast_map m) {
  assert (false, Z3NotLoadedError);
}
/*@}*/
/*@}*/

// __cplusplus

