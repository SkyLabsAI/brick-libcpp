---
theme: default
title: 'C++ mutexes: behavior and verification'
info: |
  Expanded informal talk with selected program examples from
  A Separation Logic Formalization of the C++ Mutex Library.
  Audience: basic separation logic. No fixed time budget.
class: cover
layout: default
colorSchema: light
canvasWidth: 1280
aspectRatio: 16/9
fonts:
  sans: Arial
  mono: monospace
  provider: none
transition: fade
mdc: false
twoslash: false
wakeLock: false
drawings:
  enabled: false
exportFilename: cpp-mutex-informal-talk
---

# A Separation Logic Formalization of the C++ Mutex Library



<div class="presenter"><span class="presenter-name">Ke Du</span><time datetime="2026-10-22">10/22/2026</time></div>


<!--
Point: understand the behavior of each mutex and guard before discussing proofs.
Assume the audience already knows resource ownership and lock invariants.
The talk has three main ideas: tie operations to thread identity, adapt the
resource discipline to richer mutexes, and preserve modular client reasoning.
Introduce functionality directly through the paper's proof-free client code:
add_two for ordinary exclusion, balance transfer for recursive acquisition,
set_resource/await_resource for shared access, and get_size for lock_guard.
Point to the highlighted calls and follow their execution; do not precede the
code with a verbal feature overview.
Source: §1, pp. 1–2. The supplied PDF is anonymous, so no author or venue
metadata is inferred from the LaTeX source or the draft's template fields.
Transition: run through the two add_two callers to show ordinary exclusion.
-->

---


# std::mutex for mutual exclusion

<div class="paper-code"><div class="code-pair"><div class="code-panel"><strong>mutex ensures mutual exclusion</strong><pre class="example-code"><code>unsigned int x = 0;
std::mutex m{};
<span></span>
void add_two() {
<span class="example-focus">  m.lock();</span>
<span class="example-focus">  x += 2;</span>
<span class="example-focus">  m.unlock();</span>
}</code></pre></div><div class="code-panel"><strong>Running add_two concurrently</strong><pre class="example-code"><code>int main() {
  std::thread t(add_two);
  add_two();
  t.join();
}</code></pre></div></div></div>

While one caller holds m, the other waits at <code>m.lock()</code>.


---

# C++ forbids cross-thread unlock

<div class="code-pair">
  <div class="code-panel">
    <strong>Thread L</strong>
    <pre class="example-code"><code><span class="example-focus">acquire(a);</span>
*x = *x + 1;
release(b);</code></pre>
  </div>
  <div class="code-panel">
    <strong>Thread R</strong>
    <pre class="example-code"><code>acquire(b);
*y = *x + 1;
<span class="example-focus">release(a);</span></code></pre>
  </div>
</div>

<div class="handoff">
  <span>Supported in traditional Concurrent Separation Logic</span>
</div>

---

# recursive_mutex: can acquire multiple times

<div class="paper-code"><div class="code-strip"><pre class="example-code"><code>unsigned long balance_a, balance_b;
std::recursive_mutex m{};</code></pre></div>

<div class="code-pair"><div class="code-panel"><strong>Update the first balance</strong><pre class="example-code"><code>void update_a(long x) {
  m.lock();
  balance_a += x;
  m.unlock();
}</code></pre></div><div class="code-panel"><strong>Update the second balance</strong><pre class="example-code"><code>void update_b(long x) {
  m.lock();
  balance_b += x;
  m.unlock();
}</code></pre></div></div></div>

---

# Atomic Account Transfer With Recursive Mutex

<div class="paper-code"><div class="code-panel"><strong>Outer call · lock count starts at 0</strong><pre class="example-code"><code>void transfer(int x) {
  m.lock();            // 0 -> 1
  update_a(x);         // 1 -> 2 -> 1
  update_b(-(long)x);  // 1 -> 2 -> 1
  m.unlock();          // 1 -> 0
}</code></pre></div></div>

The thread owns m while its lock count is positive.


---

# shared_mutex: Reader-Writer Lock

<div class="paper-code"><div class="code-panel"><pre class="example-code"><code>bool resource = false;
std::shared_mutex m{};
<span></span>
void set_resource() {
<span class="example-focus">  m.lock();</span>
<span class="example-focus">  resource = true;</span>
<span class="example-focus">  m.unlock();</span>
}</code></pre></div></div>

While this writer holds m, readers and other writers wait.

<!--
Reference: §3.3, Fig. 4, p. 9 · Writer half of the paper example; proof annotations removed

Introduce the writer half of the shared-mutex example. An exclusive
acquisition permits changing resource and excludes all other readers and writers.
Keep the motivation at the API level. The next slide completes the same example
with its reader; later we will revisit both sides using fractional ownership.
-->

---

# shared_mutex: Reader-Writer Lock

<div class="paper-code"><div class="code-panel"><pre class="example-code"><code>void await_resource() {
  for (;;) {
<span class="example-focus">    m.lock_shared();</span>
<span class="example-focus">    bool ret = resource;</span>
<span class="example-focus">    m.unlock_shared();</span>
    if (ret)
      break;
  }
}</code></pre></div></div>

Several <code>await_resource</code> calls may read at once.

<!--
Reference: §3.3, Fig. 4, p. 9 · Reader half; uses resource and m from the preceding slide

Complete Fig. 4. The reader copies resource while holding shared ownership,
releases that ownership, and then inspects its local copy. Multiple readers can
read together, while set_resource needs exclusive ownership. Pair lock_shared
with unlock_shared. The loop is a safety example; no fairness or eventual
termination result is claimed. Keep proof annotations out of this motivation.
-->

---

# lock_guard: RAII wrapper of a BasicLockable object

<div class="paper-code"><div class="code-panel"><pre class="example-code"><code>std::mutex m;
int res;
<span></span>
void f() {
<span class="example-focus">  std::lock_guard&lt;std::mutex&gt; lock(m);</span>
<span class="example-focus"> // critical section </span>
}</code></pre></div></div>

Named requirements: informal C++ contracts.

<code>m.lock()</code>: Blocks until a lock can be acquired for the current thread.

<code>m.unlock()</code>: Unlocks the lock.


---

# Challenge 1 : specs should ensure that

<div class="rows">
  <div class="row"><strong>Unlock</strong><span>by a thread that did not acquire the mutex</span></div>
  <div class="row"><strong>Reacquire</strong><span>an ordinary mutex already owned by this thread</span></div>
  <div class="row"><strong>Destroy</strong><span>a mutex while any thread holds it</span></div>
</div>

<div class="callout">Violation: <strong>undefined behavior in C++.</strong></div>

---

# Contribution

<div class="rows">
  <div class="row"> Thread-aware specs for mutexes, RAII wrappers </div>
  <div class="row"> Formalize "BasicLockable" </div>
  <div class="row"> Reference implementations for mutexes, satisfy our specs and passed libC++ test suite  </div>
  <div class="row"> Case study: data structure predicate that uses lock under the hood is not tied to a thread and still transferrable.  </div>
</div>

---

# BRiCk: an Iris-based program logic for C++

<div class="rows">
  <div class="row"><strong>C++ support</strong><span> class, template. Translates C++ to an AST defined in Rocq. </span></div>
  <div class="row"><strong>Iris based</strong><span>Ghost state, invariants, WP. No semantics, axiomatized proof rules. </span></div>
  <div class="row"><strong>Thread-local resource</strong><span>Every predicate is implicitly indexed by a thread ID.</span></div>
</div>

$\mathsf{tid}(t)$ a special proposition that says **“the current thread is $t$.”**. Cannot transfer between threads.

Other (primitive) assertions can move between threads, like in most CSLs.

---

# Mutex1 never checks the calling thread

<div class="paper-code"><div class="code-panel"><pre class="example-code"><code>std::atomic&lt;bool&gt; flag{false};
<span></span>
void lock() {
  while (flag.exchange(true))
    std::this_thread::yield();
}
void unlock() {
  flag = false;
}</code></pre></div></div>

The ordinary CSL lock contract can describe this spinlock.

<!--
Reference: §3.1, Fig. 1, p. 4; §4.2.1, Fig. 5, p. 11 · Mutex1: field renamed lock → flag

This covers the basic spinlock in Fig. 1 and Mutex1 in Fig. 5. Renaming
the field avoids the paper's field/method name collision. Its constructor's
initialization is expressed as an in-class initializer; yield is qualified.
The implementation carries no runtime owner ID, and the usual transferable
locked token can be used to verify it. Crucially, the paper also proves this
same implementation against its more restrictive C++ mutex contract in BRiCk.
A stricter client precondition does not require a runtime test of every condition.
Do not say that the absence of an owner check makes this code unprovable in BRiCk.
-->

---

# Mutex2 records and checks the owner

<div class="paper-code"><div class="code-strip"><pre class="example-code"><code>std::atomic&lt;bool&gt; flag{false};
std::thread::id owner{};</code></pre></div><div class="code-pair"><div class="code-panel"><strong>Acquire and record</strong><pre class="example-code"><code>void lock() {
  while (flag.exchange(true))
    std::this_thread::yield();
  owner =
    std::this_thread::get_id();
}</code></pre></div><div class="code-panel"><strong>Check and release</strong><pre class="example-code"><code>void unlock() {
  assert(owner ==
    std::this_thread::
      get_id());
  owner = std::thread::id{};
  flag = false;
}</code></pre></div></div></div>

<!--
Reference: §4.2.1, Fig. 5, p. 11 · Mutex2 method excerpts; field renamed and initialization normalized

Mutex2 adds an owner field and an assertion. The usual CSL release rule
only demands a transferable token and P; it permits a different thread to call
unlock. Such a caller cannot justify the owner assertion. Thus Mutex2 fails the
usual lock contract even though it is a legitimate C++ mutex implementation.
The paper proves its faithful C++ contract in BRiCk. This is a comparison of
specifications, not a claim that BRiCk and separation logic are disjoint systems.
Under that contract only the owner accesses owner during a critical section,
so this field need not be atomic. Initialization uses the constructor values.
-->

---

# Mutex2 also checks that destruction happens while unowned

<div class="paper-code"><div class="code-panel"><pre class="example-code"><code>~Mutex2() {
  assert(!flag);
  assert(owner == std::thread::id{});
}</code></pre></div></div>

The destructor needs evidence that every acquisition has ended.

<!--
Reference: §4.2.1, Figs. 5–6, pp. 11–13 · Completes Mutex2’s operations

Finish the Mutex2 example with its destructor. The assertions expose
another obligation absent from the usual simple lock API: a mutex must be
unowned when destroyed. Later, full representation ownership plus the complete
token supplies this evidence. Violations of the C++ mutex preconditions are
undefined behavior; implementations do not have to detect them uniformly.
This slide adds no proof annotations to the implementation code.
-->

---

# Both implementations satisfy the BRiCk C++ contract

<table class="comparison">
<thead><tr><th>Implementation</th><th>Usual CSL lock contract</th><th>Paper’s BRiCk C++ contract</th></tr></thead>
<tbody>
<tr><td>Mutex1: no owner check</td><td>Provable</td><td>Provable</td></tr>
<tr><td>Mutex2: checks owner</td><td>Not satisfied</td><td>Provable</td></tr>
</tbody></table>

<div class="callout">The <strong>cross-thread client</strong> is admitted by the usual CSL contract and rejected by the C++ contract.</div>

<!--
Reference: §2.1, pp. 2–3; §4.2.1, p. 11 · Compare implementation contracts separately from client proofs

State the correction explicitly. The paper says that both implementations
meet its mutex specifications, and that the Mutex1 proof is simpler. It does not
claim that an unchecked spinlock is provable in traditional SL but not BRiCk.
Instead, owner-checking Mutex2 cannot satisfy the usual transferable-token spec.
The cross-thread handoff client is what the usual spec admits and the faithful
C++ spec rules out. BRiCk is itself a separation logic; it can express the thread
identity needed by the C++ interface. A runtime owner check is an implementation
choice, whereas the public contract restricts what a client may assume.
-->

---

# Knowing an owner ID is different from being that thread

<div class="flow">
  <div class="card"><strong>Ownership token</strong><span>“The owner is t.”</span><span class="muted">Transferable resource</span></div>
  <div class="arrow">+</div>
  <div class="card thread-bound"><strong>tid(t)</strong><span>“I am thread t.”</span><span class="muted">About the current caller</span></div>
</div>

**An operation requires both to agree.**

<!--
Reference: §2.2, p. 3; §3.1, p. 4 · BRiCk supplies the thread-specific tid predicate

Return to the example: R received a token for a, which L acquired.
The predicates describing lock ownership can move like ordinary resources.
The essential non-transferable assertion is tid(t), which says that the current
thread is t. Instantiate t=L: moving an L-indexed token to R does not let R
establish tid(L). R has tid(R), so the faithful rule rejects its release(a).
This avoids the misleading explanation that every mutex token is itself a
non-transferable resource. The caller check is where thread identity matters.
Recall the earlier BRiCk introduction: its assertions can express this
thread-specific fact.
Do not explain monotonic predicates or their implementation.
Transition: combine that identity check with an exclusive permission exchange.
-->

---

# Acquiring exchanges one permission for another

<div class="centered">

$$
\mathsf{not\_locked}(t)
\;\xrightarrow{\;\mathtt{lock}\;}\;
\mathsf{m\_locked}(t) * P
$$

$$
\mathsf{m\_locked}(t) * P
\;\xrightarrow{\;\mathtt{unlock}\;}\;
\mathsf{not\_locked}(t)
$$

</div>

Both operations require **tid(t)**.<br>
The permission to acquire cannot be duplicated.

<!--
Reference: §3.1, pp. 4–5 · Schematic resource exchange: object shares, indices, and later modality omitted

These are explanatory resource transitions, not the complete Hoare triples.
The mutex representation and tid(t) are preserved; unlock formally restores
the protected resource under a later modality.
not_locked(t) means this thread has permission to attempt acquisition. Another
thread may currently own the mutex, so it does not assert global availability.
After acquisition, this thread no longer has its not_locked permission.
Exclusivity prevents it from retaining a spare copy and acquiring again.
To release, it must have the matching locked permission, the protected resource,
and the right caller identity. Familiar invariant reasoning now sits inside a
discipline that enforces the C++ restrictions.
Transition: where does a thread obtain its first permission?
-->

---

# A thread registers using a permission it cannot duplicate

<div class="flow">
  <div class="card"><strong>Reserve N</strong><span>from this thread's permission set</span></div>
  <div class="arrow">+</div>
  <div class="card"><strong>Token share</strong><span>for this mutex</span></div>
  <div class="arrow">→</div>
  <div class="card"><strong>Register</strong><span>obtain not_locked(t)</span></div>
</div>

Unregister after use to recover both resources.

<div class="callout"><strong>Registration is a proof step.</strong> No new C++ API is required.</div>

<!--
Reference: §3.1, pp. 4–5; §4.1, p. 10 · N is a verifier-chosen namespace

We cannot enumerate all threads that will use a mutex at allocation time.
Each newly created thread instead starts with permissions for the universe of
namespaces. It splits out N and combines that permission with a token share
to register for the chosen mutex. The namespace permission is exclusive for
that thread, so it cannot register twice concurrently using the same N.
A namespace is chosen in the proof. The mutex also has a fresh allocation ID;
the two roles allow dynamic allocation while keeping distinct permissions
available for composition. Do not unpack the ghost map or infinite-set algebra.
Unregistering restores N, making this discipline local to a method's proof.
This is the main bridge to encapsulation near the end of the talk.
Transition: revisit add_two with this registration discipline, then use the
token shares to explain safe destruction.
-->

---

# Each add_two call restores the evenness invariant

$$
P \;\triangleq\; \exists n.\; x \mapsto n * \mathsf{even}(n)
$$

<div class="flow">
  <div class="card"><strong>Acquire</strong><span>obtain P</span></div>
  <div class="arrow">→</div>
  <div class="card"><strong>x += 2</strong><span>even stays even</span></div>
  <div class="arrow">→</div>
  <div class="card"><strong>Release</strong><span>restore P</span></div>
</div>

Each thread registers with its own identity; join reunites the shared ownership.

<!--
Reference: §3.1, Fig. 2, pp. 5–6 · Proof idea for the motivation’s add_two program

Revisit the exact program introduced in motivation. The paper's proof
establishes an evenness invariant rather than a precise final-value theorem.
Each caller owns a share of the mutex and token plus its own namespace permission.
Register, acquire P, preserve it across x += 2, release, and unregister. The
main thread splits shares at spawn and recovers them at join. The heap proof is
familiar SL; the extra discipline proves legal use of the C++ mutex.
No line-by-line proof script or full proof-annotated listing is required.
-->

---

# Reassembling the token rules out outstanding lock ownership

<div class="flow">
  <div class="card"><strong>Shares</strong><span>returned by users</span></div>
  <div class="arrow">→</div>
  <div class="card"><strong>Whole token</strong><span>no thread holds the mutex</span></div>
</div>

$$
\text{full mutex ownership} * \mathsf{token}(1)
\quad\Longrightarrow\quad \text{permission to destroy}
$$

<!--
Reference: §3.1, p. 5 · Token shares are distinct from shares of the object representation

Every registered user accounts for a share; while a thread holds the mutex,
that share cannot be recovered as a free token. Reuniting the whole token
therefore rules out outstanding acquisition. Unregistration returns a share.
The destructor also requires full ownership of the mutex representation.
Do not suggest token(1) alone permits deallocation or settles unrelated lifetime
issues. The paper's destructor then recovers the protected resource P.
Transition: retain it, but change the shape of ownership for recursive mutexes.
-->

---

# Count acquisitions without duplicating the resource

<div class="depth"><b>0</b><span>lock →</span><b>1</b><span>lock →</span><b>2</b><span>unlock →</span><b>1</b><span>unlock →</span><b>0</b></div>

$$
\mathsf{holds}(t,n,a)
$$

<div class="rows">
  <div class="row"><strong>n > 0</strong><span>borrow the single protected resource P(a)</span></div>
  <div class="row"><strong>Finish using P</strong><span>return it to recover the holds handle</span></div>
</div>

<!--
Reference: §3.2, p. 7 · Abbreviated holds predicate; n is the acquisition depth and a the abstract state

Use the count sequence to distinguish ownership depth from resource quantity.
There is one protected heap fragment, not n copies. holds unifies the unowned
case at n=0 with all positive depths. Acquire increments n; release decrements it.
At positive depth the borrowing rule gives P(a) and a continuation that rebuilds
holds after receiving P(b). Hence a client cannot both retain P and freely reuse
the original handle to obtain another copy. Return P before a nested acquisition
that requires the handle. This is ordinary linear resource accounting.
That single interface lets a method be verified for an arbitrary initial n.
Transition: carrying a in the handle also preserves knowledge across nested calls.
-->

---

# The outer lock keeps both updates in one critical section

$$
P(a,b) \;\triangleq\;
\mathit{balance\_a} \mapsto a * \mathit{balance\_b} \mapsto b
$$

<div class="flow">
  <div class="card"><strong>(a, b)</strong><span>outer lock held</span></div>
  <div class="arrow">→</div>
  <div class="card"><strong>(a + x, b)</strong><span>after update_a(x)</span></div>
  <div class="arrow">→</div>
  <div class="card"><strong>(a + x, b − x)</strong><span>after update_b(−x)</span></div>
</div>

Each helper temporarily adds one acquisition and returns to its entry depth.

<!--
Reference: §3.2, Fig. 3, pp. 7–8 · Arithmetic follows the paper’s presentation

This is the specification-level explanation of the recursive balance
example already shown as code. The helpers have a uniform contract for any
initial depth n. Since transfer owns the outer acquisition, state arguments
remain meaningful across both helper calls. Return the borrowed P to holds
before passing the handle into the next nested operation. No second copy of P
is created. After the outermost release, the stored argument no longer certifies
the current heap value. Treat arithmetic at the paper's level of abstraction;
the displayed integers do not assert an extra absence-of-overflow theorem.
-->

---

# Shared mutexes combine thread ownership with fractional access

<div class="flow">
  <div class="card"><strong>One writer</strong><span>full resource P(1)</span><span>exclusive permission</span></div>
  <div class="arrow">or</div>
  <div class="card"><strong>Several readers</strong><span>fractions P(q)</span><span>per-thread reader permissions</span></div>
</div>

Release must match **both the caller and the acquisition mode**.

<!--
Reference: §3.3, pp. 8–10 · No recursive acquisition of std::shared_mutex

Assume fractional-permission intuition and spend the time on what changes.
The protected predicate is fractional: exclusive acquisition yields P(1), while
shared acquisition yields P(q) for a fraction chosen by the specification.
Readers have separate thread-indexed reader permissions that remember their
resource fraction. A writer token cannot justify unlock_shared, nor a reader
token unlock. Identity still rules out another thread performing the release.
This C++ mutex does not permit the same thread to reacquire in either mode.
-->

---

# The fraction determines which access to resource is permitted

$$
P(q) \;\triangleq\; \exists b.\; \mathit{resource} \mapsto_q b
$$

<div class="flow">
  <div class="card"><strong>set_resource()</strong><span>P(1) permits the write</span></div>
  <div class="card"><strong>await_resource()</strong><span>P(q) permits the read</span></div>
</div>

The reader saves <code>ret</code> before releasing its share.

<!--
Reference: §3.3, Fig. 4, pp. 9–10 · Proof idea for both halves shown in motivation

Connect fractional access to the concrete code. The writer receives full
ownership, updates resource, and restores full ownership. Each reader receives
a fraction, reads while that fraction is available, and returns precisely its
fraction through unlock_shared. ret is a local copy, so testing it after unlock
does not require further access to the shared location. Thread- and mode-specific
permissions prevent mismatched release and repeated acquisition. This proves
safety of the loop, not that it eventually sees true.
-->

---

# One abstract interface supports all three mutex variants

<div class="flow">
  <div class="card"><strong>Mutex variants</strong><span>ordinary · recursive · shared</span></div>
  <div class="arrow">→</div>
  <div class="card"><strong>BasicLockable</strong><span>do_lock · do_unlock</span></div>
  <div class="arrow">→</div>
  <div class="card"><strong>Generic wrapper</strong><span>lock_guard</span></div>
</div>

Abstract the **resource transformation** of each operation.

<!--
Reference: §5.1, pp. 16–17 · The shared-mutex instance uses its exclusive lock/unlock operations

C++ BasicLockable is a requirement on types providing lock and unlock, rather
than a concrete base class. The paper gives it a matching logical interface.
Different mutex types transform different resources: ordinary acquisition
exchanges permissions and exposes P; recursive acquisition changes a count.
The generic contract therefore uses do_lock and do_unlock predicate transformers
with a requested postcondition K, plus a preserved representation predicate.
This interface does not bake in the incorrect assumption that every lock call
produces a fresh copy of P. Guards can be proved generically over it.
No need to put the transformer formulas or all representation arguments onscreen.
Transition: a guard uses this interface to tie one acquisition to a scope.
-->

---

# lock_guard manages one acquisition for one scope

<div class="flow">
  <div class="card"><strong>Construct</strong><span>perform do_lock</span></div>
  <div class="arrow">→</div>
  <div class="card"><strong>Use</strong><span>work with the resources</span></div>
  <div class="arrow">→</div>
  <div class="card"><strong>Destroy</strong><span>perform do_unlock</span></div>
</div>

In <code>get_size</code>, the local guard balances acquisition and release.

<!--
Reference: §5.2, p. 17 · Revisit the get_size lock_guard example

Expand RAII once: Resource Acquisition Is Initialization. A normal lock_guard
constructor acquires; its destructor releases when the scope exits. Its contract
is parameterized by the abstract operation transformations, preserving all
identity and resource preconditions of the underlying mutex.
Return to get_size: constructing lock obtains the resources needed for the
read, and returning from the function destroys lock and returns those resources.
The usual mutex-taking constructor shown here acquires; the adopt-lock overload
assumes an acquisition already made. The generic proof retains the underlying
mutex's ownership requirements.
Transition: Account uses lock_guard inside methods while hiding its mutex.
-->

---

# Account protects its balance with an internal recursive mutex

<div class="paper-code"><div class="code-pair"><div class="code-panel"><strong>Fields and constructor</strong><pre class="example-code"><code>unsigned long balance;
std::recursive_mutex mut;
<span></span>
explicit Account(
    unsigned long n)
  : balance(n) {}</code></pre></div><div class="code-panel"><strong>Public update method</strong><pre class="example-code"><code>void incr_balance(
    unsigned long i) {
  std::lock_guard&lt;
    std::recursive_mutex&gt;
      lg(mut);
  balance += i;
}</code></pre></div></div></div>

<!--
Reference: §6, Fig. 10, p. 20 · Excerpts from class Account; constructor parameter shortened to n

Introduce the actual Account class before discussing its representation.
The fields are private; the constructor and methods are public. Its recursive
mutex protects balance. incr_balance follows the lock_guard pattern already
introduced in motivation. The next slide shows transfer_to and the main client.
These excerpts belong to the same class. Headers and class scaffolding are
omitted for readability, not because the fields are intended as global variables.
-->

---

# transfer_to calls another account while holding the source lock

<div class="paper-code"><div class="code-pair"><div class="code-panel"><strong>Account method</strong><pre class="example-code"><code>void transfer_to(
    Account&amp; target,
    unsigned long i) {
  std::lock_guard&lt;
    std::recursive_mutex&gt;
      lg(mut);
  balance -= i;
  target.incr_balance(i);
}</code></pre></div><div class="code-panel"><strong>Client</strong><pre class="example-code"><code>int main() {
  Account from{4};
  Account to{2};
  from.transfer_to(to, 3);
}</code></pre></div></div></div>

<!--
Reference: §6, Fig. 10, p. 20 · Account& makes explicit the reference intended by the paper’s simplified listing

This completes Fig. 10. The source guard remains live while the target's
incr_balance creates its own guard. The proof needs both objects' permissions
and must distinguish their mutex namespaces. The paper prints a by-value Account
parameter, which would copy a class containing a noncopyable mutex. The slide
explicitly adapts that parameter to Account& while retaining the intended example.
The later proof is about safe modular use, not a banking invariant or deadlock
freedom. Opposite lock orders are still a possible progress issue.
-->

---

# An object can hide its mutex's thread identity

<div class="centered big">Account representation: <strong>no caller ID</strong></div>

<div class="scope centered">
  <strong>Inside a method</strong>
  <p>register → lock → use → unlock → unregister</p>
</div>

The caller supplies and recovers its namespace permission.

<!--
Reference: §6, pp. 18–22 · For this pattern, methods return with the internal mutex unowned by the caller

This is the modularity payoff of the Account example just shown.
The Account representation contains a share of its mutex representation and a
token share; it does not contain a caller ID or a held-lock predicate.
The caller brings its own tid(t) and namespace permission. The method temporarily
registers, operates through a guard, unregisters, and returns the permission.
The same Account representation is therefore usable by another thread with
that thread's own available namespace permission. This is logical transfer of
ownership; no moving or copying of the C++ mutex object is claimed.
Be precise: thread-local obligations have not vanished from method contracts.
They are managed separately from the transferable representation. The claim
is for this balanced encapsulation pattern, not every synchronization protocol.
Transition: namespace separation also handles calls that use two objects.
-->

---

# Disjoint namespaces let proofs compose across two objects

<div class="flow">
  <div class="card"><strong>Account A</strong><span>hold A's mutex</span></div>
  <div class="arrow">calls →</div>
  <div class="card"><strong>Account B</strong><span>acquire B's mutex</span></div>
</div>

$$
\mathsf{perm}_t(A \uplus B)
\;\dashv\vdash\;
\mathsf{perm}_t(A) * \mathsf{perm}_t(B)
$$

Reserve disjoint A and B from the thread's permission set.

<!--
Reference: §6, pp. 20–22 · Permissions abbreviate mutex_perm; this is a safety argument, not deadlock freedom

The paper's transfer_to example holds the source account's mutex while calling
incr_balance on the target. Give the two objects disjoint proof namespaces A
and B. The caller splits its initial namespace budget and can reserve B while
A is already in use. Each method returns the resources it temporarily used.
The displayed equivalence splits an already owned permission; disjointness
alone does not create resources. The disjoint union requires A and B to be disjoint.
Avoid a by-value Account code listing: the PDF uses simplified presentation
code, while a C++ account containing a mutex is not ordinarily copyable.
Do not infer deadlock freedom from distinct namespaces. Opposite lock orders
are a separate progress issue. Nor does this example prove full banking
functional correctness; its intended result is safety and modularity.
-->

---

# The thread-indexed contract justifies the owner assertion

<div class="flow">
  <div class="card"><strong>owner ↦ t</strong><span>recorded at acquisition</span></div>
  <div class="arrow">+</div>
  <div class="card"><strong>tid(t)</strong><span>identity of this caller</span></div>
</div>

<div class="paper-code"><div class="code-panel"><pre class="example-code"><code>assert(owner == std::this_thread::get_id());</code></pre></div></div>

These two facts make the assertion succeed for every permitted call.

<!--
Reference: §4.2.1, Fig. 6, pp. 12–13 · High-level proof bridge for the earlier Mutex2 code

Cover the proof outline in Fig. 6 without transcribing every invariant.
Acquisition records the actual caller ID in owner and builds m_locked(t).
Release requires that fragment plus tid(t), so the runtime owner assertion is
justified. The representation and full token justify the destructor assertions.
By comparison, a transferable unindexed locked token cannot tell us that the
current thread equals owner. An owner check is not an obligation imposed on all
implementations: Mutex1 has no such check and satisfies the same C++ contract.
The extra identity information is what permits the proof of this implementation.
-->

---

# Only a first acquisition locks the underlying mutex

<div class="paper-code"><div class="code-pair"><div class="code-panel"><strong>State</strong><pre class="example-code"><code>std::atomic&lt;
  std::thread::id&gt; owner{};
int count = 0;
std::mutex m{};</code></pre></div><div class="code-panel"><strong>Acquire</strong><pre class="example-code"><code>void lock() {
  const auto t =
    std::this_thread::get_id();
  if (owner != t) {
    m.lock();
    owner = t;
  }
  count++;
}</code></pre></div></div></div>

<!--
Reference: §4.2.2, Fig. 7, p. 14 · Initializers normalized; local t names the current thread ID

Show the implementation associated with the recursive specification.
If the caller already owns this recursive mutex, it skips m.lock and increments
count. A different thread must first acquire m. owner is atomic because potential
callers inspect it concurrently; count is only accessed by the current owner.
The paper writes a schematic constructor assigning new std::mutex to an object
field; the slide uses a directly constructed std::mutex m{} instead.
The local t abbreviates the two get_id calls, which return the same caller ID.
The paper's mechanization represents thread IDs by hashes with an explicit
no-collision assumption; mention that if asked about implementation assumptions.
The code here is the paper-level algorithm, not a production mutex replacement.
-->

---

# Only the final release unlocks the underlying mutex

<div class="paper-code"><div class="code-panel"><pre class="example-code"><code>void unlock() {
  count--;
  if (count == 0) {
    owner = std::thread::id{};
    m.unlock();
  }
}</code></pre></div></div>

Intermediate releases only decrement the acquisition count.

<!--
Reference: §4.2.2, Fig. 7, pp. 14–15 · Completes the recursive implementation

This is the release half of Fig. 7, with proof annotations removed.
The caller has a positive holds depth and access to count. A nonfinal release
keeps the underlying mutex held. The final release clears owner before releasing
m, permitting another thread to become the owner. Relate the implementation's
count to the abstract n in holds. The abstract client specification hides this
first/final case split, even though the implementation proof must examine it.
-->

---

# A writer changes the counter from 0 to −1

<div class="paper-code"><div class="code-panel"><pre class="example-code"><code>std::atomic&lt;int&gt; sharers = 0;
<span></span>
void lock() {
  int idle = 0;
  while (!sharers.compare_exchange_strong(idle, -1)) {
    idle = 0;
  }
}
void unlock() {
  sharers = 0;
}</code></pre></div></div>

<!--
Reference: §4.2.3, Fig. 8, p. 15 · Exclusive operations of SharedMutex

The shared-mutex implementation uses one atomic counter: zero means
unheld, minus one means writer-held, and a positive value counts readers.
A writer succeeds only from zero. compare_exchange updates its expected argument
on failure, so the loop resets idle to zero before trying again. Release sets
the counter to zero. The next slide adds the shared operations of the same class.
The owner discipline can be maintained in the specification's ghost state even
though this runtime representation stores a counter rather than thread IDs.
-->

---

# A reader increments the counter while no writer holds it

<div class="paper-code"><div class="code-panel"><pre class="example-code"><code>void lock_shared() {
  int val;
  do {
    val = sharers;
  } while (val &lt; 0 ||
           !sharers.compare_exchange_strong(val, val + 1));
}
void unlock_shared() {
  sharers--;
}</code></pre></div></div>

<!--
Reference: §4.2.3, Fig. 8, pp. 15–16 · Shared operations; do/while punctuation normalized

Finish Fig. 8. A reader loads the counter, retries while a writer owns
it, and uses compare_exchange to add one reader. A shared release subtracts one.
The draft's do/while listing has an extra brace block after the condition; this
slide uses the standard semicolon while retaining the algorithm.
At proof level, a map of thread identities tracks reader fractions and prevents
repeat acquisition or wrong-thread release. The physical counter records how
many readers there are, not which callers are authorized. As in Mutex1, this
is further evidence that a faithful contract need not add runtime owner checks.
No fairness, bounded waiting, or production-level counter-bound claim is added.
-->

---

# The specifications have mechanized implementations and clients

<div class="rows evidence">
  <div class="row"><strong>Specifications</strong><span>ordinary, recursive, shared; Rocq + BRiCk</span></div>
  <div class="row"><strong>Mutex witnesses</strong><span>portable implementations using atomics</span></div>
  <div class="row"><strong>Generic clients</strong><span>libstdc++ lock_guard and encapsulated objects</span></div>
</div>

<div class="callout small">Proof scope: partial correctness in BRiCk's axiomatic C++ logic.<br>Production pthread/futex implementations and operational adequacy remain outside this result.</div>

<!--
Reference: §2.2, p. 3; §4, pp. 10–16; §5, pp. 16–19; §9–10, p. 23

Connect the implementation examples just shown to the precise proof boundary.
The paper mechanizes the specifications, simple mutex implementations, and
examples in Rocq using BRiCk. An implementation that checks its owning thread
illustrates why the usual transferable CSL contract would be too permissive.
It separately verifies the libstdc++ implementation of lock_guard.
The portable mutex implementations also pass 17 non-timed libc++ mutex tests,
reported in §4; tests support the development but are not its proof foundation.
This is not a proof of production pthread mutexes or their OS/futex layers.
BRiCk provides axiomatic C++ reasoning and has no operational adequacy theorem.
There is no general termination, fairness, or deadlock-freedom guarantee.
If asked about artifacts: §10 says the proofs and logical rules are open source
but running the development needs proprietary automation. No artifact rebuild
or verification was performed as part of preparing these slides.
-->

---

# Faithful thread ownership can coexist with modular reasoning

<div class="rows">
  <div class="row"><strong>Caller identity</strong><span>restrict who may use a permission</span></div>
  <div class="row"><strong>Resource shape</strong><span>count acquisitions; split read access</span></div>
  <div class="row"><strong>Composition</strong><span>reuse guards and hide object internals</span></div>
</div>

<!--
Reference: §9, p. 23

Return to the initial mismatch: an ownership token can travel, but the right to
invoke a C++ mutex operation depends on the caller. Pair the two explicitly.
Counted handles make recursive calls compositional without duplicating P;
fractions support shared access. Abstract operation contracts and balanced
registration keep the resulting client reasoning modular.
Close by returning to the motivating programs and the distinction between a contract and an implementation.
-->

---

# Questions

<div class="rows">
  <div class="row"><strong>Contracts</strong><span>Which implementation satisfies which interface?</span></div>
  <div class="row"><strong>Recursion</strong><span>How does one resource support nested calls?</span></div>
  <div class="row"><strong>Encapsulation</strong><span>What remains in the client’s contract?</span></div>
</div>

<!--
Reference: Source: A Separation Logic Formalization of the C++ Mutex Library, supplied local draft

All program examples in the supplied PDF have now been shown or revisited.
Use the source coverage table in outline.md to locate the corresponding figure.
No time limit or preset Q&A duration is imposed on this expanded version.
-->
