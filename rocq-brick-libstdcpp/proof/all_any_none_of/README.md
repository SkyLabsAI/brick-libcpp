# `std::all_of`, `std::any_of`, and `std::none_of`

## Fixed scope

These specifications cover the C++20 non-execution-policy overloads instantiated
with `const unsigned char*` iterators and a `bool (*)(unsigned char)` predicate.
They do not cover arbitrary iterator types, other element types, functors,
`std::ranges` algorithms, or overloads taking an execution policy.

## Contracts

[spec.v](spec.v) preserves ownership and contents of the selected byte slice.
The predicate contract in [pred.v](pred.v) tracks separate resources through
`I k`, where `k` counts predicate applications. The postconditions expose a count
`k` satisfying `0 <= k <= length xs`; no exact call count, visit order, or
short-circuit behavior is promised.

[model.v](model.v) describes the Boolean results, including empty ranges.
`test x = None` leaves the predicate result unspecified; a known decisive value
can still determine the algorithm result. [hints.v](hints.v) relates total
predicates to `forallb` and `existsb`.

These are library contracts with verified clients, not proofs of the underlying
libstdc++ implementations. The predicate must satisfy the supplied callback
contract.

## Clients

[The tests](../../test/all_any_none_of) include 14 concrete clients, stateful
counting clients for all three algorithms, an arbitrary-input `all_of` branch
client, and a partial-predicate client. Separate proof files allow the expensive
checks to compile in parallel.

## References

- [all_of](https://eel.is/c++draft/alg.all.of)
- [any_of](https://eel.is/c++draft/alg.any.of)
- [none_of](https://eel.is/c++draft/alg.none.of)
- [Overloads and examples](https://en.cppreference.com/w/cpp/algorithm/all_any_none_of)
