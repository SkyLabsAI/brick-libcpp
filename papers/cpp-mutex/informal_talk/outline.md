# C++ mutexes: behavior and verification

Expanded informal talk based on [the supplied 25-page PDF](../.build/stdcpp.pdf).
There is **no fixed time limit**. The [Slidev deck](slides.md) contains 37 slides
and assumes basic separation logic, separating conjunction, lock invariants,
and fractional ownership.

**Central claim:** C++ mutex specifications must account for the calling thread
while preserving compositional reasoning about protected resources.

## Narrative

| Part | Slides | Purpose |
| --- | --- | --- |
| Functionality through paper examples | 1–7 | Start directly with add_two, recursive balance transfer, the reader/writer pair, and get_size; show behavior by following highlighted code without proof annotations. |
| The specification gap | 8–9 | Use the cross-thread handoff example to expose the C++ caller-identity requirement. |
| BRiCk background | 10 | Introduce the Iris-based C++ logic and its thread-specific predicates from §2.2. |
| Implementations and contracts | 11–14 | Compare the unchecked and owner-checking spinlocks and state precisely which contracts they satisfy. |
| Ordinary mutex discipline | 15–19 | Explain thread identity, permission exchange, registration, add_two, and destruction. |
| Recursive and shared ownership | 20–23 | Revisit balance transfer and the reader/writer example through their resource contracts. |
| Generic lock_guard | 24–25 | Explain BasicLockable and revisit get_size through the generic guard contract. |
| Encapsulation | 26–29 | Show Account and its client, then explain transferable representation predicates and disjoint namespaces. |
| Implementation witnesses | 30–34 | Connect the owner assertion to the proof and show the recursive and shared implementation algorithms. |
| Evidence and discussion | 35–37 | State the mechanized results and their scope, then discuss. |

## The SL / BRiCk distinction

The paper does **not** claim that an owner-unchecked spinlock is provable in
traditional SL but unprovable in BRiCk. Section 4.2.1 (p. 11) explicitly proves
both Mutex1 and Mutex2 against its mutex specifications in BRiCk.

| Subject | Usual transferable-token CSL contract | Paper’s thread-aware C++ contract in BRiCk |
| --- | --- | --- |
| Mutex1, without an owner check | Provable | Provable |
| Mutex2, with an owner check | Not satisfied | Provable |
| Cross-thread handoff client (§2.1) | Admitted under appropriate initial resources | Rejected: the releasing caller lacks the required identity |

These rows distinguish implementation verification from client verification.
BRiCk is itself a separation logic. The relevant contrast is between contracts,
not between SL and a non-SL system. A caller precondition need not be enforced
by a runtime check. The unchecked shared-mutex counter is another illustration.

## Coverage of paper examples

Repeated proof-annotated figures are covered by the same underlying code plus
a later explanation of the proof idea. Motivation slides contain code and API
behavior only. unique_lock and scoped_lock are excluded as requested;
Fig. 9 is therefore omitted. Commented-out LaTeX material absent from the PDF
is not included.

| Paper example | Source | Deck location |
| --- | --- | --- |
| Daring concurrency: acquire a / release b and acquire b / release a | §2.1, p. 3 | 8; revisited in 14–16 |
| Simple spinlock | Fig. 1, p. 4 | 11 (same algorithm as Mutex1) |
| Ordinary mutex: add_two and two-thread main | Fig. 2, p. 6 | Code 2; proof idea 18; lifecycle 19 |
| Recursive mutex: update_a, update_b, transfer | Fig. 3, p. 8 | Code 3–4; ownership explanation 20–21 |
| Shared mutex: set_resource and await_resource | Fig. 4, p. 9 | Code 5–6; ownership explanation 22–23 |
| Mutex1 and Mutex2 implementations | Fig. 5, p. 11 | 11–14, including initialization and Mutex2’s destructor |
| Mutex2 proof outline | Fig. 6, p. 13 | Same code 12–13; contract/owner-assertion bridge 30 |
| RecursiveMutex implementation and proof outline | Fig. 7, p. 14 | 31–32; abstract client discipline 20–21 |
| SharedMutex implementation | Fig. 8, p. 15 | 33–34; fractional client discipline 22–23 |
| lock_guard: get_size | §5.2, p. 17 | Code 7; generic guard explanation 24–25 |
| unique_lock: inc and answer | Fig. 9, p. 19 | Omitted as requested |
| Account: constructor, incr_balance, transfer_to, main | Fig. 10, p. 20 | Code 26–27; encapsulation 28–29 |
| Account proof outline | Fig. 11, p. 21 | Same code 26–27; representation and namespace explanation 28–29 |

## Slide-by-slide outline

| # | Single point | Paper anchor |
| --- | --- | --- |
| 1 | C++ mutexes: behavior and verification | Based on the supplied 25-page draft |
| 2 | std::mutex serializes add_two calls | §3.1, Fig. 2, p. 6 · Proof annotations removed; main uses the standard int return type |
| 3 | Both helpers acquire the same recursive mutex | §3.2, Fig. 3, p. 8 · Client code with proof annotations removed |
| 4 | transfer reacquires m through its helpers | §3.2, Fig. 3, pp. 7–8 · Lock-count trace added; helpers shown on the preceding slide |
| 5 | Exclusive locking lets set_resource write | §3.3, Fig. 4, p. 9 · Writer half of the paper example; proof annotations removed |
| 6 | Shared locking lets readers run together | §3.3, Fig. 4, p. 9 · Reader half; uses resource and m from the preceding slide |
| 7 | lock_guard releases m when get_size returns | §5.2, p. 17 · The paper’s get_size example, without proof annotations |
| 8 | C++ forbids this cross-thread unlock | §2.1, p. 3 · The paper's “daring concurrency” example; initialization and lock invariants omitted |
| 9 | A faithful spec must rule out three illegal operations | §3.1, pp. 3–4 · Reacquisition restriction here concerns std::mutex |
| 10 | BRiCk is an Iris-based program logic for C++ | §2.2, p. 3; §1, p. 2 · Iris machinery, C++ support, thread identity, and mechanization |
| 11 | Mutex1 never checks the calling thread | §3.1, Fig. 1, p. 4; §4.2.1, Fig. 5, p. 11 · Mutex1: field renamed lock → flag |
| 12 | Mutex2 records and checks the owner | §4.2.1, Fig. 5, p. 11 · Mutex2 method excerpts; field renamed and initialization normalized |
| 13 | Mutex2 also checks that destruction happens while unowned | §4.2.1, Figs. 5–6, pp. 11–13 · Completes Mutex2’s operations |
| 14 | Both implementations satisfy the BRiCk C++ contract | §2.1, pp. 2–3; §4.2.1, p. 11 · Compare implementation contracts separately from client proofs |
| 15 | Knowing an owner ID is different from being that thread | §2.2, p. 3; §3.1, p. 4 · BRiCk supplies the thread-specific tid predicate |
| 16 | Acquiring exchanges one permission for another | §3.1, pp. 4–5 · Schematic resource exchange: object shares, indices, and later modality omitted |
| 17 | A thread registers using a permission it cannot duplicate | §3.1, pp. 4–5; §4.1, p. 10 · N is a verifier-chosen namespace |
| 18 | Each add_two call restores the evenness invariant | §3.1, Fig. 2, pp. 5–6 · Proof idea for the motivation’s add_two program |
| 19 | Reassembling the token rules out outstanding lock ownership | §3.1, p. 5 · Token shares are distinct from shares of the object representation |
| 20 | Count acquisitions without duplicating the resource | §3.2, p. 7 · Abbreviated holds predicate; n is the acquisition depth and a the abstract state |
| 21 | The outer lock keeps both updates in one critical section | §3.2, Fig. 3, pp. 7–8 · Arithmetic follows the paper’s presentation |
| 22 | Shared mutexes combine thread ownership with fractional access | §3.3, pp. 8–10 · No recursive acquisition of std::shared_mutex |
| 23 | The fraction determines which access to resource is permitted | §3.3, Fig. 4, pp. 9–10 · Proof idea for both halves shown in motivation |
| 24 | One abstract interface supports all three mutex variants | §5.1, pp. 16–17 · The shared-mutex instance uses its exclusive lock/unlock operations |
| 25 | lock_guard manages one acquisition for one scope | §5.2, p. 17 · Revisit the get_size lock_guard example |
| 26 | Account protects its balance with an internal recursive mutex | §6, Fig. 10, p. 20 · Excerpts from class Account; constructor parameter shortened to n |
| 27 | transfer_to calls another account while holding the source lock | §6, Fig. 10, p. 20 · Account& makes explicit the reference intended by the paper’s simplified listing |
| 28 | An object can hide its mutex's thread identity | §6, pp. 18–22 · For this pattern, methods return with the internal mutex unowned by the caller |
| 29 | Disjoint namespaces let proofs compose across two objects | §6, pp. 20–22 · Permissions abbreviate mutex_perm; this is a safety argument, not deadlock freedom |
| 30 | The thread-indexed contract justifies the owner assertion | §4.2.1, Fig. 6, pp. 12–13 · High-level proof bridge for the earlier Mutex2 code |
| 31 | Only a first acquisition locks the underlying mutex | §4.2.2, Fig. 7, p. 14 · Initializers normalized; local t names the current thread ID |
| 32 | Only the final release unlocks the underlying mutex | §4.2.2, Fig. 7, pp. 14–15 · Completes the recursive implementation |
| 33 | A writer changes the counter from 0 to −1 | §4.2.3, Fig. 8, p. 15 · Exclusive operations of SharedMutex |
| 34 | A reader increments the counter while no writer holds it | §4.2.3, Fig. 8, pp. 15–16 · Shared operations; do/while punctuation normalized |
| 35 | The specifications have mechanized implementations and clients | §2.2, p. 3; §4, pp. 10–16; §5, pp. 16–19; §9–10, p. 23 |
| 36 | Faithful thread ownership can coexist with modular reasoning | §9, p. 23 |
| 37 | Questions | Source: A Separation Logic Formalization of the C++ Mutex Library, supplied local draft |

## Presentation and source fidelity

The BRiCk introduction follows the three C++ restrictions and precedes the
implementation comparison. Its content comes from §2.2 (p. 3); supporting
mechanization context comes from §1 (p. 2). Source references remain in speaker
notes. A shared per-slide component adds automatic page numbers.

- Start with the paper's code, with no verbal feature overview. Trace the two
  add_two callers to demonstrate exclusion; trace transfer's calls to the
  preceding helpers to show the same thread reacquiring m; follow the writer and
  reader calls to demonstrate
  the two shared-mutex modes; and follow get_size's return to show lock_guard
  destruction. Highlight the relevant statements and keep proof annotations out
  of the introduction. Both balance helpers and both reader/writer functions
  remain in the deck.
- The motivating handoff uses the paper’s exact thread bodies. Its initialization
  and invariants are omitted in the paper: do not present it as a complete
  program starting with two freshly unlocked C++ mutexes. Trace the usual CSL
  token through b, then explain why the C++ contract rejects the caller.
- `not_locked(t)` is permission for this thread to attempt acquisition, not a
  statement that the mutex is globally unheld. The permission predicates can
  move; `tid(t)` ties their use to the current caller. Registration is a proof
  step rather than a new C++ operation.
- The add_two proof preserves evenness; do not attribute a precise final-value
  theorem to the paper’s displayed invariant. Recursive acquisitions count
  ownership without duplicating P. Return a borrowed P before reusing the
  holds handle. State parameters give information only at positive depth.
- The shared reader copies resource while holding its fraction and inspects
  the local ret after releasing. No progress guarantee is inferred.
- BasicLockable abstracts the operation’s resource transformation. Its shared
  mutex instance uses exclusive operations. lock_guard balances one acquisition
  through construction and destruction in the examples shown.
- Account’s representation is thread independent, but method contracts still
  require and restore the caller’s namespace permissions. Logical transfer
  does not mean copying or moving the C++ mutex object. Disjoint namespaces
  establish composable permissions, not deadlock freedom.

Code is taken from the supplied PDF with proof annotations removed. Limited
presentation repairs are disclosed in the corresponding speaker notes:

1. `lock` fields are renamed `flag` to avoid colliding with `lock()` methods;
   constructor initialization may be written as in-class initialization.
2. The ordinary client uses `int main()` instead of the paper’s `void main()`.
3. Account’s `transfer_to` takes `Account&`, making the intended target reference
   explicit instead of the draft’s noncopyable by-value parameter. Its constructor
   parameter is shortened to `n` for layout.
4. RecursiveMutex directly constructs its underlying mutex instead of assigning
   `new std::mutex()` to an object field in the draft’s schematic constructor.
   A local `t` abbreviates its two calls to `std::this_thread::get_id()`.
5. SharedMutex’s do/while punctuation is normalized; the retry algorithm is
   retained. Mutex yield calls are namespace-qualified. Includes and enclosing
   class scaffolding may be omitted for method excerpts.

The lock_guard example retains the paper’s bool return type. Implementation
snippets remain paper-level illustrations, not production-ready replacements.
The recursive implementation’s mechanization assumes collision-free hashes of
thread IDs; mention this when discussing its implementation assumptions.

## Evidence and scope

The paper mechanizes specifications, portable mutex implementations, guard
implementations, and clients in Rocq/BRiCk. It verifies the libstdc++ lock_guard
implementation separately from its portable mutex witnesses.
Its 17 non-timed libc++ tests are supporting evidence. BRiCk’s C++ semantics is
axiomatic and has no operational adequacy proof. These are partial-correctness
results, with no general fairness, termination, or deadlock-freedom result and
no verification of production pthread/futex implementations. Preparing the
slides does not rebuild or reverify the Rocq artifact.

The [slide-design skill](https://github.com/hunkim/slide-skill/blob/main/SKILL.md)
and [official Slidev guidance](https://sli.dev/guide/work-with-ai#installation)
continue to guide the deck: one claim per slide, readable code, simple diagrams,
and supporting detail in speaker notes. The retained examples are part of the main deck.
