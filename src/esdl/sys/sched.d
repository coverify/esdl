module esdl.sys.sched;

import core.stdc.string: memset;
// version(Posix) {
  
import core.sys.posix.sys.types: pthread_t;
import core.sys.posix.unistd;

extern(C) pthread_t pthread_self();
version (Android) { }
 else {
   extern(C) int pthread_setaffinity_np(pthread_t thread, size_t cpusetsize,
					cpu_set_t *cpuset);
 }
extern(C) void sched_getaffinity(pthread_t thread, size_t cpusetsize,
				 cpu_set_t *cpuset);
  
alias size_t __cpu_mask;	// unsigned long int in bits/sched.h

enum __CPU_SETSIZE = 1024;	// max 1024 CPUs
enum __NCPUBITS = 8 * __cpu_mask.sizeof;

struct cpu_set_t {
  __cpu_mask[__CPU_SETSIZE / __NCPUBITS] __bits;
}

void CPU_SET(size_t cpu, cpu_set_t* cpusetp) {
  assert(cpu / 8 < cpu_set_t.sizeof);
  (*cpusetp).__bits[cpu / __NCPUBITS] |=
    (cast(__cpu_mask) 1) << (cpu % __NCPUBITS);
}

void CPU_CLR(size_t cpu, cpu_set_t* cpusetp) {
  assert(cpu / 8 < cpu_set_t.sizeof);
  (*cpusetp).__bits[cpu / __NCPUBITS] &=
    ~ ((cast(__cpu_mask) 1) << (cpu % __NCPUBITS));
}

bool CPU_ISSET(size_t cpu, cpu_set_t* cpusetp) {
  assert(cpu / 8 < cpu_set_t.sizeof);
  return (((*cpusetp).__bits[cpu / __NCPUBITS]) &
	  ((cast(__cpu_mask) 1) << (cpu % __NCPUBITS))) != 0;
}

// CPU_COUNT is not implemented for the time being
size_t[] CPU_LIST() {
  cpu_set_t cs;
  size_t[] list;
  CPU_ZERO(&cs);
  sched_getaffinity(0, cs.sizeof, &cs);

  int count = 0;
  for (int i = 0; i < __CPU_SETSIZE; i++)
    {
      if (CPU_ISSET(i, &cs)) {
	list ~= i;
      }
    }
  return list;
}

int CPU_COUNT() {
  return cast(int) sysconf(_SC_NPROCESSORS_ONLN);
}

int CPU_COUNT_AFFINITY() {
  return cast(int) CPU_LIST().length;
}

void CPU_ZERO(cpu_set_t* cpusetp) {
  memset(cpusetp, '\0', cpu_set_t.sizeof);
}

public int stickToCpuCore(size_t coreId) {
  version (Android) { return 0; }
  else {
    import std.stdio;
    import core.cpuid: threadsPerCPU;

    assert(coreId >= 0 && coreId < CPU_COUNT());

    cpu_set_t cpuset;
    CPU_ZERO(&cpuset);
    // writeln(cpuset.__bits);
    CPU_SET(coreId, &cpuset);

    // writeln(cpuset.__bits);

    pthread_t current_thread = pthread_self();
    return pthread_setaffinity_np(current_thread, cpu_set_t.sizeof, &cpuset);
  }
}

// }
