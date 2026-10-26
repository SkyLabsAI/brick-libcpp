/*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */
#include <istream>

int second(std::istream &in) {
  int a = 0, b = 0;
  in >> a;
  in >> b;
  return b;
}
int first(std::istream &in) {
  int a = 5;
  in >> a;
  return a;
}
