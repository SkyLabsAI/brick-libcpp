#include<memory>

std::shared_ptr<int> testshared1() {
    auto x= std::shared_ptr<int>(new int);
    *x=1;
    return x;
  }

std::shared_ptr<int[]> testsharedarr() {
    auto x= std::shared_ptr<int[]>(new int[2]);
    x[0]=1;
    x[1]=2;
    return x;
  }

int scalar_deletions = 0;
int array_deletions = 0;

struct ClassDelete {
    int value = 42;
    static void operator delete(void* p) noexcept {
        ++scalar_deletions;
        ::operator delete(p);
    }
    static void operator delete[](void* p) noexcept {
        ++array_deletions;
        ::operator delete[](p);
    }
};

// Global new does not suppress class-specific lookup at the later delete.
int test_delete_effects() {
    scalar_deletions = 0;
    array_deletions = 0;
    {
        std::shared_ptr<ClassDelete> p(::new ClassDelete);
    }
    if (scalar_deletions != 1 || array_deletions != 0) return 1;
    {
        std::shared_ptr<ClassDelete[]> p(::new ClassDelete[2]);
    }
    if (scalar_deletions != 1 || array_deletions != 1) return 2;
    {
        std::shared_ptr<ClassDelete> p = std::make_shared<ClassDelete>();
        std::shared_ptr<ClassDelete[]> a = std::make_shared<ClassDelete[]>(2);
    }
    if (scalar_deletions != 1 || array_deletions != 1) return 3;
    return 0;
}

void test_shared_copy_empty(std::shared_ptr<int> const& source) {
    std::shared_ptr<int> copy(source);
}

#ifdef SHARED_PTR_DELETE_EFFECTS_TEST
int main() {
    std::shared_ptr<int> empty;
    test_shared_copy_empty(empty);
    return test_delete_effects();
}
#endif
