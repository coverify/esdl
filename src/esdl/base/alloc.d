module esdl.base.alloc;

import std.experimental.allocator.typed: TypedAllocator;
// import std.experimental.allocator.gc_allocator : GCAllocator;
import esdl.experimental.allocator.mallocator: Mallocator;
// import std.experimental.allocator.mmap_allocator : MmapAllocator;

alias EsdlAllocator = TypedAllocator!(Mallocator);

static EsdlAllocator _esdl__allocator;

auto make(T, U...)(U args) {
  // import std.stdio;
  // writeln("Make: ", T.stringof);
  return _esdl__allocator.make!T(args);
}

