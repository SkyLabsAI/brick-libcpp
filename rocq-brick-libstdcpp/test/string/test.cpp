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

// s is "abca".
bool FindChar(const std::string& s) {
    return s.find('b') == 1 && s.find('z') == std::string::npos &&
           s.find('a', 1) == 3 && s.find('a', 4) == std::string::npos &&
           s.find('a', 10) == std::string::npos;
}

void Append(std::string& s) {
    s.push_back('a');
    s += 'b';
}

// s is "abc".
void EraseTail(std::string& s) {
    s.erase(1);
}

// s is "abc".
void EraseMiddle(std::string& s) {
    s.erase(1, 1);
}

// s is "a": pos == size() erases nothing.
void EraseAtEnd(std::string& s) {
    s.erase(1);
}

std::string::size_type FindA(const std::string& s) {
    return s.find('a');
}

// Binds a local std::string to FindA's const std::string& parameter.
void FindInLocal() {
    std::string s;
    FindA(s);
}

// The same with a const local, which is made const after construction and
// mutable again before destruction.
void FindInConstLocal() {
    const std::string s;
    FindA(s);
}
