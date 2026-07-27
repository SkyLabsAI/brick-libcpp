# Mutations

Six deliberate defects injected into the specification, authored by two agents
that had not seen each other's work: **M1** (gpt-5.5) wrote the two `m_terra`
mutations, **M2** (Claude Sonnet) wrote the four `m_sonnet` ones. Neither author
saw the client proofs.

Each mutation must (a) still compile — a syntax break is not a semantic
mutation, (b) genuinely change what the contract means, and (c) be **killed** by
a named client proof that was already green. All six were killed. That is 66 of
the judge's 169 checks.

This is the discrimination evidence. A specification that no client can
distinguish from a wrong one is not worth trusting, regardless of how many
positive proofs close against it.

The `.patch` files are verbatim agent output, unedited.

| Mutation | Attacks | Killed by |
|---|---|---|
| `m_terra__invert_has_value` | `REQ_CORE_001` | `literal_bool_result` |
| `m_terra__zero_value_absent` | `REQ_CORE_001`, `REQ_BOUNDARY_001`, `REQ_BOUNDARY_002` | `zero_value_reports_true`, `emplace_zero_still_engaged` |
| `m_sonnet__reset_no_op` | `REQ_COMPOSITION_001` | `reset_then_query_reports_false` |
| `m_sonnet__emplace_no_op` | `REQ_COMPOSITION_002`, `_003`, `REQ_BOUNDARY_002` | `emplace_then_query_reports_true`, `reemplace_already_engaged_stays_engaged`, `emplace_zero_still_engaged` |
| `m_sonnet__nullopt_assign_no_op` | `REQ_COMPOSITION_006` | `assign_nullopt_disengages` |
| `m_sonnet__move_ctor_disengages_source` | `REQ_COMPOSITION_005` | `move_construct_preserves_source_engagement` |

## What each one does

**`invert_has_value`** — one token. `\post[Vbool (is_engaged state)]` becomes
`\post[Vbool (negb (is_engaged state))]`. The blunt instrument: engaged optionals
report false and vice versa.

**`zero_value_absent`** — the only mutation that hits `model.v` rather than
`spec.v`. Redefines `is_engaged (Some value)` as `negb (Z.eqb value 0)`, so a
stored zero counts as absence. This is the truthiness confusion the two boundary
requirements exist to forbid, and it is the interesting one: the mutation also
rewrites the model's own `Succeed Example is_engaged_zero` from `= true` to
`= false`, so the model stays internally consistent and still compiles. Only a
client that constructs `optional<int>{0}` and asserts `true` catches it.

**`reset_no_op`**, **`emplace_no_op`**, **`nullopt_assign_no_op`** — the same
shape three times, on three different operations: replace a postcondition that
establishes a new state with one that restates the precondition's existential
`state` variable. The operation becomes a no-op in the model while remaining
well-typed. `nullopt_assign_no_op` is the one worth dwelling on — `o = std::nullopt`
is the most common way real code clears an optional, and this makes it silently
do nothing.

**`move_ctor_disengages_source`** — the subtlest, and the only one that encodes a
plausible wrong belief rather than an obvious weakening. It remodels move
construction on the owning-pointer intuition that `std::unique_ptr` teaches:
split the source's engagement out of the shared `\prepost` into a `\pre`, then
add `otherp |-> optionalR 1$m None` to the postcondition, leaving the moved-from
source disengaged. The standard requires that only the contained `int` is moved
from — engagement survives. A specification author who had internalized
`unique_ptr` semantics would write exactly this.

## Coverage gap

Every mutation targets `spec.v` or `model.v`. **None targets `pred.v`**, where
the ownership predicate `optionalR` lives. The linkage between the abstract state
and the object's ownership is therefore not covered by a recorded kill. The same
gap was independently found in a sibling run of this pipeline, where a reviewer
closed it by hand and confirmed the linkage was load-bearing.

`min_mutations` in the frozen manifest is 2; six were authored. There is no policy
requiring a mutation per specification layer, which is why the representation
layer went untouched.
