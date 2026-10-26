/*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */
#include <vector>

int deref_first() {
  std::vector<int> v;
  v.push_back(7);
  return *v.begin();
}
void inc_to_end() {
  std::vector<int> v;
  v.push_back(7);
  auto it = v.begin();
  ++it;
}
bool deref_empty() {
  std::vector<int> v;
  return &*v.begin() == nullptr;
}
void inc_past_end() {
  std::vector<int> v;
  auto e = v.end();
  ++e;
}
