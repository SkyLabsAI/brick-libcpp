
Require Export skylabs.brick.libstdcpp.numeric.pred.

Require Import skylabs.auto.cpp.spec.
Require Import skylabs.prelude.numbers.
Require Export skylabs.brick.libstdcpp.numeric.inc_numeric_cpp.
Require Export skylabs.brick.libstdcpp.numeric.inc_numeric_cpp_templates.
#[local] Open Scope Z_scope.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.

  cpp.spec "std::gcd<int, int>(int, int)" as gcd_int_spec
    from inc_numeric_cpp.source with
    (\arg{m} "__m" (Vint m)
     \arg{n} "__n" (Vint n)
     \require gcd_callable signed32_range m n
     \post[Vint (gcd m n)] emp).

  cpp.spec "std::lcm<int, int>(int, int)" as lcm_int_spec
    from inc_numeric_cpp.source with
    (\arg{m} "__m" (Vint m)
     \arg{n} "__n" (Vint n)
     \require lcm_callable signed32_range m n
     \post[Vint (model.lcm m n)] emp).

  cpp.spec "std::gcd<int, long long>(int, long long)" as gcd_int_long_long_spec
    from inc_numeric_cpp.source with
    (\arg{m} "__m" (Vint m)
     \arg{n} "__n" (Vint n)
     \require gcd_callable signed64_range m n
     \post[Vint (gcd m n)] emp).

  cpp.spec "std::lcm<int, long long>(int, long long)" as lcm_int_long_long_spec
    from inc_numeric_cpp.source with
    (\arg{m} "__m" (Vint m)
     \arg{n} "__n" (Vint n)
     \require lcm_callable signed64_range m n
     \post[Vint (model.lcm m n)] emp).

End with_cpp.

(* Bootstrap file; substantive edits are made through the live rocq-ed session. *)
