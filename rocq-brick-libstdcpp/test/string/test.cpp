/*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */
#include <string>

void SelfAssign(std::string& value) {
    value = value;
}

void AssignAlias(std::string& value) {
    const std::string& source = value;
    value = source;
}

void CopyAssign(std::string& destination, const std::string& source) {
    destination = source;
}

bool SizeAfterAssign(std::string& s) {
    s = 'a';
    return !s.empty() && s.size() == 1 && s.length() == 1;
}

bool SizeIsLength(const std::string& s) {
    return s.size() == s.length();
}

bool EmptyIffZero(const std::string& s) {
    return s.empty() == (s.size() == 0);
}
