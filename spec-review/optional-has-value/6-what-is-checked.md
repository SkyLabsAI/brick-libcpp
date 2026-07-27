# What gets checked, and by whom

Every candidate passes through two independent layers.

A **deterministic judge** runs a fixed set of mechanical checks and is the only
authority that can accept. An **adversarial jury** of three independent reviewers
then reads the result and can only reject.

That asymmetry is deliberate. A jury ACCEPT never creates acceptance on its own,
so no reviewer can talk a weak candidate through. A single justified blocker
forces remediation, so no reviewer needs to.

---

# Part 1 — The adversarial jury

## How the three seats are kept independent

- **Three seats, one brief.** All three jurors get the identical brief, rubric,
  output schema, and evidence paths. Nothing varies per seat except which model
  fills it, so a disagreement between them is a disagreement in judgement rather
  than in instructions.
- **Fresh sessions.** No juror inherits authoring context. None of them sees the
  requirements being written, the spec being authored, or the proofs being closed.
- **Cross-family review.** The reviewing models are from a different family than
  the authoring model, so a reviewer is less likely to share the author's blind
  spots.
- **Mutually blind.** Each juror is forbidden from reading the other seats' review
  files, work directories, or event logs. A juror may re-verify any lead from the
  repository, but never inherit another's conclusion.
- **Identity-bound.** Each seat writes an immutable launch record naming its model
  and a unique session id, carrying the certificate digest. All three digests must
  match the certificate. A mismatch or missing record is a fail-closed reject —
  this is what prevents one model being replayed as three reviewers.
- **Schema-validated.** Each review is machine-checked against a schema before it
  counts, and the validator recomputes the git comparison identity — base,
  candidate, tree, merge base, patch hash, changed paths — from the repository
  itself. An `accept` verdict requires that recomputation to succeed.

## The stance jurors are given

- A deterministic ACCEPT is *eligible*, never final. A green certificate is not
  evidence that the spec or the clients are good: a proof against weak clients is
  as green as a proof against strong ones.
- Client realness, value accuracy, and coverage are already established
  mechanically upstream. Rely on that rather than re-deriving it.
- Spend independent scrutiny where the mechanical gates cannot reach:
  1. Is the spec sound and strong **beyond the pinned points** — no convenient
     precondition quietly shifted onto the caller, no vacuous region the pins
     miss, no wrong-but-unpinned corner of the model?
  2. Is the **mutation set** adequate and diverse enough that "all mutations
     killed" actually means something?
  3. **Evidence integrity** and repository fit.
- Prefer scoped findings over blanket rejection. Quarantine only what is genuinely
  compromised. Additional clients may be requested.
- Known soft spots are disclosed *to* the jury rather than hidden from it, with an
  explicit invitation to judge whether each one weakens the evidence.

## Evidence hierarchy jurors must apply

Strongest first. **A lower tier cannot overrule a higher tier.**

1. Governing policy and explicit task constraints
2. Semantic authorities for the C++ version in use, plus the actual header and
   generated binding shape — an implementation header is *binding* evidence, not
   portable semantic authority
3. Committed mainline abstractions, specs, representations, clients, and proofs
   for the same or nearest mechanism
4. Repository history showing accepted fixes, rejected shapes, strengthening,
   simplification, or review-driven cleanup
5. Reproducible independent-client, counterexample, negative-control, mutation,
   build, and proof evidence for the candidate
6. Author-authored matrices, coverage notes, comments, and PR claims

Note where the author's own claims rank: last. And explicitly — a build confirms
elaboration and proof closure in one environment; it does not establish that the
contract is portable, strong, useful, non-circular, or idiomatic.

## The ten gates each juror scores

Each is scored pass or fail, with cited evidence and a written rationale.

| Gate | The question it asks |
|---|---|
| `review_independence` | Was this review genuinely fresh, uncontaminated by the authoring context or the other seats? |
| `assurance_claim` | Is what the candidate *claims* to have proved actually what it proved — no overstated assurance? |
| `semantic_adequacy` | Does the contract say the right thing about the real API, judged against the standard? |
| `anti_vacuity` | Is any part of the spec trivially satisfiable, or satisfiable for the wrong reason? |
| `independent_clients` | Does every registered contract have a client that a plausible wrong postcondition would break? |
| `counterexamples_and_boundaries` | Are the negative controls and boundary cases real and sufficient? |
| `abstraction_and_reuse` | Does it reuse the repository's existing abstractions, or reinvent them? |
| `proof_understanding` | Do the proofs demonstrate understanding, or did automation happen to close them? |
| `repository_fit` | Does this look like code the repository would have written — style, idiom, precedent? |
| `build_and_proof` | Does it build, and do the proofs close, reproduced independently? |

## Severity ladder

| Severity | Meaning | Merge effect |
|---|---|---|
| `blocker` | Wrong, unsound, or vacuous semantics; impossible acceptance claim; circular evidence as the sole basis for a claim; admits or cheating; non-hermetic pollution that invalidates proof evidence | Prevents accept |
| `major` | Material missing semantics, independent coverage, counterexample, reuse, family design, or proof understanding that must change before merge — explicitly including a forwarding wrapper presented only as incomplete adapter coverage | Prevents accept |
| `minor` | Local maintainability, idiom, naming, or proof noise that does not invalidate the result | None |
| `note` | Verified observation, question, or optional improvement | None |

Calibration: severity is tied to the claimed coverage and the failure risk. A
missing test is not automatically a blocker.

## The four verdicts available

| Verdict | When |
|---|---|
| `accept` | All applicable gates pass, no material unknown, no open blocker or major finding |
| `request_changes` | Reviewable, but specific fixes or evidence are required first |
| `stop` | Base, candidate, or scope is invalid or ambiguous; semantic authority unavailable for a decisive claim; required tooling misconfigured |
| `quarantine` | Evidence integrity compromised by circular clients, contamination, environment pollution, stale state, or provenance failure — named scopes excluded until clean evidence is regenerated |

A rerun requirement is set independently of the verdict: immediately, after
changes, blocked, or not required.

---

# Part 2 — The mechanical gates

Each check is named in the certificate with its result, so any of them can be
re-run and confirmed. Grouped by what they defend against.

## Provenance — is this the thing that was asked for?

| Check | What it defends against |
|---|---|
| `requirement freeze intact` | The frozen requirement set is re-hashed against its recorded digests. Any edit after freezing is a hard reject — the goalposts cannot be moved to pass. |
| `requested family matches frozen requirement family` | A run cannot silently certify a different family than the one frozen. |
| `structured natural-language requirements and client mappings` | Schema conformance, plus **bidirectional** requirement↔scenario mapping: every requirement reaches a client, every client traces back to a requirement. |
| `client manifest preserves every frozen requirement-to-scenario mapping` | A required scenario cannot be quietly dropped after freezing. |
| `candidate spec present`, `client manifest present` | Basic completeness. |

## Registration identity — is the spec that was proved the spec that was registered?

| Check | What it defends against |
|---|---|
| `public registration resolves to the frozen candidate contract` | The named contract must resolve to the registered spec **by typeclass search plus `eq_refl`**, not by string match. A spec that merely shares a name does not pass. |
| `client contracts match the frozen public API registrations` | Clients must verify against the registered contract, not a private copy of it. |
| `all required client rows are signed and judge-pinnable` | Every client row must be independently checkable rather than taken on the author's word. |
| `candidate introduces no unapproved theories` | No pulling in an outside theory to make something provable. |

## Statement pinning — is the proof about the claim, or about something easier?

| Check | What it defends against |
|---|---|
| `judge statement builds` | The judge generates the theorem statement itself from the frozen contract. The author does not supply it. |
| `proof is pinned to the judge statement` | The proof must discharge the *judge's* statement. This is what stops a proof of a weaker, self-authored lemma from counting. |
| `proof builds` | It actually closes. |
| the same three, keyed on scenarios | Run again against the frozen scenario list rather than the client list, so a scenario cannot be satisfied by an unrelated client. |

## Ground truth — does the spec agree with the real library?

| Check | What it defends against |
|---|---|
| `client execution oracle` | Every positive client is compiled with asserts **live** and **run** against the real standard library; each must exit 0. A spec can be internally consistent and still wrong about C++ — this is the check that catches it. If a client faithfully realizes a requirement and still fails here, the *requirement* is wrong and must be re-authored; patching the client to make the assert pass is forbidden. |
| `client value-pinning gate` | Each pinned function's result must be compared against a **literal**, not forwarded from the library. This stops a client from asking the library for the answer and then asserting the library agrees with itself. |

## Negative controls — does the spec forbid the wrong answer?

| Check | What it defends against |
|---|---|
| `at least one focused bad client is present` | A candidate cannot ship with no negative control at all. |
| `bad client must not prove` | The adversarial client asserts something false about the API. Its proof **must fail to close**; a spec that permits it is rejected. Note the direction — passing this check means a build *failing*. |

## Discrimination — would a wrong spec be noticed?

Eleven checks per mutation, and the largest group in the certificate.

| Check | What it defends against |
|---|---|
| `at least N semantic mutations supplied` | A floor on discrimination evidence. |
| `patch exists`, `name is unique`, `record has safe identifiers` | Bookkeeping integrity — no phantom or duplicate mutations padding the count. |
| `changes only candidate spec/model files` | A mutation must attack the *spec*, not weaken a client or the harness. |
| `applies and changes spec/model` | It must be a real edit, not a no-op. |
| `spec still compiles` | **A syntax break is not a semantic mutation.** This closes the easy cheat of "breaking" the spec by making it not build. |
| `maps to frozen required requirements` | Each mutation must attack a requirement that was actually frozen. |
| `targets real positive client proofs`, `targets clients mapped to those requirements` | The kill target must be a genuine client tied to the attacked requirement. |
| `client targets are green before mutation` | The target must be passing first — otherwise a "kill" proves nothing. |
| `is killed by at least one real client proof` | The payoff: with the defect injected, a named client proof must now fail. |

## Build

| Check | What it defends against |
|---|---|
| `candidate package and all positive client proofs build` | The whole family builds from clean, including every proof target. |

---

## What none of this can tell you

Worth stating plainly, since it is why the jury exists and why this package was
sent for review at all.

The mechanical layer can establish that a contract is non-vacuous, sensitive to
mutation, pinned to judge-authored statements, and in agreement with the real
standard library at every tested point.

It cannot establish that the contract **says the right thing**, that the
requirements were the **right requirements**, or that what is absent from the
spec should have been absent.

Those are the judgements we are asking for.
