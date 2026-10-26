/*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */
#include <istream>

int init(std::istream &in) {
  int b = 0;
  in >> b;
  return b;
}
int uninit(std::istream &in) {
  int b;
  in >> b;
  return b;
}
