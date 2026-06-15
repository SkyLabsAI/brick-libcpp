/**
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */
#include <cassert>
#include <compare>
#include <limits>

struct IntPoint {
    int x;
    int y;

    auto operator<=>(const IntPoint&) const = default;
};

struct WeakBucket {
    int key;

    friend std::weak_ordering
    operator<=>(const WeakBucket& lhs, const WeakBucket& rhs) {
        int lhs_bucket = lhs.key / 10;
        int rhs_bucket = rhs.key / 10;
        if (lhs_bucket < rhs_bucket) {
            return std::weak_ordering::less;
        }
        if (rhs_bucket < lhs_bucket) {
            return std::weak_ordering::greater;
        }
        return std::weak_ordering::equivalent;
    }

    friend bool
    operator==(const WeakBucket& lhs, const WeakBucket& rhs) {
        return lhs.key / 10 == rhs.key / 10;
    }
};

struct FloatingBox {
    double value;

    auto operator<=>(const FloatingBox&) const = default;
};

bool
TestIntegralSpaceship() {
    std::strong_ordering less = 1 <=> 2;
    std::strong_ordering equal = 7 <=> 7;
    std::strong_ordering greater = 9 <=> 3;

    return std::is_lt(less) &&
           (std::is_eq(equal) &&
           (std::is_gt(greater) &&
           (less == std::strong_ordering::less &&
           (equal == std::strong_ordering::equal &&
           greater == std::strong_ordering::greater))));
}

bool
TestFloatingSpaceship() {
    double nan = std::numeric_limits<double>::quiet_NaN();
    std::partial_ordering less = 1.0 <=> 2.0;
    std::partial_ordering equal = 3.0 <=> 3.0;
    std::partial_ordering greater = 4.0 <=> -1.0;
    std::partial_ordering unordered = nan <=> 1.0;

    return std::is_lt(less) &&
           (std::is_eq(equal) &&
           (std::is_gt(greater) &&
           (less == std::partial_ordering::less &&
           (equal == std::partial_ordering::equivalent &&
           (greater == std::partial_ordering::greater &&
           (unordered == std::partial_ordering::unordered &&
           (!std::is_lt(unordered) &&
           (!std::is_eq(unordered) &&
           !std::is_gt(unordered)))))))));
}

bool
TestComparisonCategories() {
    std::strong_ordering strong = std::strong_ordering::less;
    std::weak_ordering weak = std::weak_ordering::equivalent;
    std::partial_ordering partial = std::partial_ordering::unordered;
    std::partial_ordering from_strong = strong;
    std::partial_ordering from_weak = weak;

    return strong < 0 &&
           (0 > strong &&
           ((strong <=> 0) == std::strong_ordering::less &&
           ((0 <=> strong) == std::strong_ordering::greater &&
           (weak == 0 &&
           (0 == weak &&
           ((weak <=> 0) == std::weak_ordering::equivalent &&
           ((0 <=> weak) == std::weak_ordering::equivalent &&
           (!(partial < 0) &&
           (!(0 < partial) &&
           ((partial <=> 0) == std::partial_ordering::unordered &&
           ((0 <=> partial) == std::partial_ordering::unordered &&
           (from_strong < 0 &&
           from_weak == 0))))))))))));
}

bool
TestDefaultedIntegerClass() {
    IntPoint a{1, 2};
    IntPoint b{1, 3};
    IntPoint c{2, 0};
    IntPoint same{1, 2};

    return (a <=> b) == std::strong_ordering::less &&
           ((c <=> b) == std::strong_ordering::greater &&
           (a < b &&
           (c > b &&
           (a == same &&
           !(a == b)))));
}

bool
TestWeakOrderingClass() {
    WeakBucket a{11};
    WeakBucket b{19};
    WeakBucket c{25};

    return (a <=> b) == std::weak_ordering::equivalent &&
           ((a <=> c) == std::weak_ordering::less &&
           ((c <=> a) == std::weak_ordering::greater &&
           (a == b &&
           c > a)));
}

bool
TestDefaultedFloatingClass() {
    FloatingBox a{1.0};
    FloatingBox b{2.0};
    FloatingBox same{1.0};
    FloatingBox nan{std::numeric_limits<double>::quiet_NaN()};

    std::partial_ordering less = a <=> b;
    std::partial_ordering unordered = nan <=> a;

    return less == std::partial_ordering::less &&
           (a < b &&
           (a == same &&
           (unordered == std::partial_ordering::unordered &&
           (!(nan == a) &&
           (!(nan < a) &&
           !(nan > a))))));
}

int
main() {
    assert(TestIntegralSpaceship());
    assert(TestFloatingSpaceship());
    assert(TestComparisonCategories());
    assert(TestDefaultedIntegerClass());
    assert(TestWeakOrderingClass());
    assert(TestDefaultedFloatingClass());
    return 0;
}
