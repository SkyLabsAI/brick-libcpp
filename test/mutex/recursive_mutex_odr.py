#!/usr/bin/env python3
"""Check that the recursive mutex header links across translation units."""

from pathlib import Path
import subprocess
import sys
import tempfile


compiler, header = sys.argv[1:]
header = Path(header).resolve()
with tempfile.TemporaryDirectory(prefix="brick-recursive-mutex-odr-") as directory:
    root = Path(directory)
    # Include the header in two translation units and check that they share the
    # sentinel variable, rather than giving it internal linkage in each unit.
    (root / "first.cpp").write_text('''
#include "custom_recursive_mutex.hpp"
#include "custom_recursive_mutex.hpp"
size_t* sentinel_address() { return &id_hash; }
void exercise_mutex() {
  MyRecursiveMutex mutex;
  mutex.lock();
  mutex.lock();
  mutex.unlock();
  mutex.unlock();
}
''')
    (root / "second.cpp").write_text('''
#include "custom_recursive_mutex.hpp"
size_t* sentinel_address();
void exercise_mutex();
int main() {
  if (sentinel_address() != &id_hash)
    return 1;
  exercise_mutex();
  MyRecursiveMutex mutex;
  if (!mutex.try_lock())
    return 2;
  mutex.unlock();
}
''')
    executable = root / "odr-test"
    subprocess.run([compiler, "-std=c++17", "-stdlib=libstdc++", "-pthread",
                    "-I", str(header.parent), str(root / "first.cpp"),
                    str(root / "second.cpp"), "-o", str(executable)],
                   check=True, timeout=60)
    subprocess.run([str(executable)], check=True, timeout=20)
