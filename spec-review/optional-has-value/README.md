# Review artifacts — `std::optional<int>::has_value()`

**This branch is not a merge candidate.** It exists so the output of our spec
pipeline can be read and commented on inline, and it will be closed rather than
merged. Nothing here is wired into the build; the files sit under
`spec-review/` precisely so they cannot affect `rocq-brick-libstdcpp/`.

What we are asking for is a quality judgement on agent-generated specification
work, and whatever feedback you have that would improve the pipeline that
produced it.

Everything below was produced on 2026-07-27. The only human input was a scope
statement naming the API. No requirement, contract, client, or proof was written
or repaired by hand.

## Reading order

| File | What it is | Who wrote it |
|---|---|---|
| `1-obligations.md` | 15 requirements the spec must satisfy | 3 blind authors (gpt-5.6-sol, gpt-5.5, Claude Sonnet), audited by Claude Opus, merged by gpt-5.6-sol |
| `2-spec.v` | the Rocq contracts | Spec Agent (gpt-5.6-sol, xhigh) |
| `3-clients-positive.cpp` | 15 clients that must verify | Client Agent (gpt-5.6-sol, xhigh), blind to the spec |
| `4-client-negative.cpp` | 1 client that must **not** verify | same |
| `5-mutations/` | 6 injected defects, each killed by a named client | 2 mutation agents (gpt-5.5, Claude Sonnet), blind to the proofs |
| `6-what-is-checked.md` | the criteria: what the mechanical gates test, and what the three-seat adversarial jury is asked to judge | — |
| `proofs/` | the 17 Rocq proofs, one per client plus the negative probe | Proof Agent (gpt-5.6-sol, xhigh) |

Read 1 through 4 for the substance. `6-what-is-checked.md` explains what the
pipeline can and cannot establish on its own, which is the context for the last
section here.

Scope is deliberately one observer: `bool std::optional<int>::has_value() const`.
The constructor, assignment, `reset` and `emplace` contracts in `2-spec.v` exist
only so a client can reach a known engagement state before asking `has_value()`.
They are state drivers, not pinned observables.

## Relationship to #109

#109 is a separate, genuine merge candidate for `std::optional<std::uint8_t>`
covering a wider surface. This branch is the same pipeline run at a deliberately
narrower scope, packaged for reading rather than for merging. The two are not
alternatives and this one is not competing for those paths.

## How it was validated

Requirements were frozen under SHA-256 before any specification existed. The
Client Agent never saw the spec, and three critics reviewed the clients while
blind to both the spec and the proofs. A deterministic judge then ran 169
mechanical checks, all passing:

- Every one of the 15 positive clients was compiled with asserts live and **run
  against the real libstdc++**; each exits 0.
- 16 proof targets close. The judge generates each theorem statement itself from
  the frozen contract, and each proof must be pinned to the judge's statement —
  a proof of a weaker, self-authored lemma does not count.
- `4-client-negative.cpp` asserts that a default-constructed optional reports
  `true`. Its proof **must fail to close**, and does.
- All 6 mutations in `5-mutations/` were killed. Each had to compile, genuinely
  change the contract's meaning, and break a named client proof that was green
  beforehand.
- Each contract must resolve to its registered spec by typeclass search and
  `eq_refl`, not by name match.

After the judge, three independent reviewers scored ten gates each. Two accepted;
one requested changes. `6-what-is-checked.md` describes the criteria they apply.

## What we already know is wrong with it

Left unrepaired on purpose. These are the things we would rather hear your view
on than quietly fix first.

**Only one negative client.** `4-client-negative.cpp` holds a single probe. The
frozen manifest sets a floor on mutation count but none on adversarial probes, so
one satisfied the gate. Probes we should have and do not: an engaged optional
asserting `false`; `reset()` then asserting `true`; `emplace(v)` then asserting
`false`; `optional<int>{0}` asserting `false`; a copy of a disengaged source
asserting `true`. The zero case is the notable omission — two requirements exist
specifically to reject truthiness-derived engagement and neither has a probe.

**No mutation reaches the representation layer.** All six target `2-spec.v` or the
model. None targets the ownership predicate, where abstract state is tied to the
object, so that linkage has no recorded kill.

**One registered contract has no client.** `move_assign_spec`
(`operator=(optional&&)`) is registered and globally dispatchable, but no client
exercises it and no mutation targets it, so a wrong postcondition there would go
undetected. One of our reviewers caught this and it is an open finding. Relatedly,
plain copy assignment `operator=(const optional&)` has no contract at all. Both
trace to one cause: the frozen requirement set asked about `o = std::nullopt` and
`o = value` but never about optional-to-optional assignment, so the Spec Agent
registered one contract nobody asked for and omitted another.

**`3-clients-positive.cpp` contains a forwarder.**
`static bool has_value(const std::optional<int>& o) { return o.has_value(); }`,
and two of the fifteen clients pin through it rather than calling the member
directly. We know this is the shape you rejected before. Its own contract is
*proved* from the member contract in `proofs/optional_has_value_forwarder_proof.v`,
and one reviewer checked with `Print Assumptions` that it adds no axiom over a
direct member proof — but it only exists because our value-pinning gate accepts a
bare free call and not a member call. That is a defect in our gate, and the fix we
intend is to the gate, not to the client.

**Two hygiene problems in the generated output.** The proofs carry
`go $usenamed=true` rather than the plain `go` this repository uses, and the
negative probe ends in a bare `Qed.` that is expected to *fail* the build, which
is workable as evidence but not committable. Both would be fixed before anything
was proposed for merge.

## Where feedback helps most

The mechanical layer can establish that a contract is non-vacuous, sensitive to
mutation, pinned to judge-authored statements, and in agreement with the real
library at every tested point.

It cannot establish that the contract says the right thing, that these were the
right requirements, or that what is absent from the spec should have been absent.
Those are the judgements we are asking for.

Fuller artifacts — the requirement set with its N4861 citations and rationales,
the certificate with all 169 named checks, the execution-oracle log, and all three
reviews — are available if any of this is worth going deeper on.
