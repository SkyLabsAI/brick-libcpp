Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.brick.libstdcpp.mutex.inc_hpp.

Require Export skylabs.brick.libstdcpp.runtime.pred.
Require Import skylabs.brick.libstdcpp.mutex.spec.mutex.

Module scoped_lock.
  Section with_cpp.
    Context `{Σ : cpp_logic}.

    (* Parameter gname : Set. *)
    Parameter R : forall {HAS_THREADS : HasStdThreads Σ} {σ : genv},
      cQp.t -> list (ptr * gname * Qp * mpred) -> Rep.

    #[only(type_ptr="std::scoped_lock<std::mutex, std::mutex>")] derive R.

    Section with_threads.
      Context {σ : genv}.
      Context `{HAS_THREADS : !HasStdThreads Σ}.

      cpp.spec
      "std::scoped_lock<...<std::mutex, std::mutex>>::scoped_lock(std::mutex&, std::mutex&)"
      (* "std::scoped_lock<std::mutex, std::mutex>::scoped_lock(std::mutex&, std::mutex&)" *)
      as ctor_spec from source with (
        \this this
        \arg{mp1} "" (Vptr mp1)
        \pre{g1 q1 P1} mp1 |-> mutex.R g1 q1$m P1
        \pre mutex.token g1 q1
        \arg{mp2} "" (Vptr mp2)
        \pre{g2 q2 P2} mp2 |-> mutex.R g2 q2$m P2
        \pre mutex.token g2 q2
        \persist{thr} current_thread thr
        \post
          this |-> R 1$m [ (mp1, g1, q1, P1); (mp2, g2, q2, P2)] **
          P1 ** mutex.locked g1 thr q1 **
          P2 ** mutex.locked g2 thr q2
      ).

      cpp.spec "std::scoped_lock<...<std::mutex, std::mutex>>::~scoped_lock()"
        as dtor_spec from source with (
        \this this
        \persist{thr} current_thread thr
        \pre{
          mp1 mp2
          g1 q1 P1
          g2 q2 P2
        }
          this |-> R 1$m [ (mp1, g1, q1, P1); (mp2, g2, q2, P2)]
        \pre |> P1
        \pre |> P2
        \pre mutex.locked g1 thr q1
        \pre mutex.locked g2 thr q2
        \post
          mp1 |-> mutex.R g1 q1$m P1 ** mutex.token g1 q1 **
          mp2 |-> mutex.R g2 q2$m P2 ** mutex.token g2 q2
      ).

      cpp.spec "foo()" as foo_spec from source with
      (
        \persist{thr} current_thread thr
        \post emp
      ).

      (* #[only(cfracsplittable)] derive R. *)
      #[only(cfractional,ascfractional,cfracvalid)] derive R.

      Lemma foo_ok : verify[source] foo_spec.
      Proof.
        verify_spec; go.
        iExists emp; go.
        iExists emp; go.
        Fail solve [ego].
        ework.
        ego.

        (**
        (** Weird failure! *)
        ego.
  match args_for <$> as_function (normalize_type ?ty0) with
  | Some _ =>
  eval evaluation_order.nd (map (wp_operand ?tu ?ρ) ?es0)
  (λ (vs : list val) (free : FreeTemps),
  builtins.wp_builtin ?f0 ?ty0 vs
  (λ v : val,
  match v with
  | Vptr obj_ptr =>
  if bool_decide (obj_ptr = nullptr)
  then wp_delete_null ?default_delete ?destroyed_type (?Q Vvoid free)
  else
  new_delete.wp_delete_dispatch.body ?default_delete ?destroyed_type obj_ptr
  (?Q Vvoid free)
  | _ => False
  end))
  | None => errors.Errors.ERROR.body "builtin does not have function type"%bs
  end ∗
  match args_for <$> as_function (normalize_type ?ty) with
  | Some _ =>
  eval evaluation_order.nd (map (wp_operand ?tu0 ?ρ0) ?es)
  (λ (vs : list val) (free : FreeTemps),
  builtins.wp_builtin ?f ?ty vs
  (λ v : val,
  match v with
  | Vptr obj_ptr =>
  if bool_decide (obj_ptr = nullptr)
  then wp_delete_null ?default_delete0 ?destroyed_type0 (?Q0 Vvoid free)
  else
  new_delete.wp_delete_dispatch.body ?default_delete0 ?destroyed_type0 obj_ptr
  (?Q0 Vvoid free)
  | _ => False
  end))
  | None => errors.Errors.ERROR.body "builtin does not have function type"%bs
  end ∗
  lock_addr
  |-> R 1$m
  [(?p, ?g, ?q,
  ::wpOperand
  ?ρ
  (Edelete false ?default_delete
  (Ecall (Ecast (Cbuiltin2fun (Tptr [...])) (Eglobal (Nglobal [...]) ?ty0)) ?es0)
  ?destroyed_type));
  (?p0, ?g0, ?q0,
  ::wpOperand
  ?ρ0
  (Edelete false ?default_delete0
  (Ecall (Ecast (Cbuiltin2fun (Tptr [...])) (Eglobal (Nglobal [...]) ?ty)) ?es)
  ?destroyed_type0))] ∗ mutex.locked ?g thr ?q ∗ mutex.locked ?g0 thr ?q0 ∗
  (?p
  |-> mutex.R ?g ?q$m
  (::wpOperand
  ?ρ
  (Edelete false ?default_delete
  (Ecall (Ecast (Cbuiltin2fun ([...])) (Eglobal ([...]) ?ty0)) ?es0)
  ?destroyed_type)) ∗ mutex.token ?g ?q ∗
  ?p0
  |-> mutex.R ?g0 ?q0$m
  (::wpOperand
  ?ρ0
  (Edelete false ?default_delete0
  (Ecall (Ecast (Cbuiltin2fun ([...])) (Eglobal ([...]) ?ty)) ?es)
  ?destroyed_type0)) ∗ mutex.token ?g0 ?q0 -∗
  interp source ((1 >*> FreeTemps.delete "std::mutex" m2_addr) >*>
  FreeTemps.delete "std::mutex" m1_addr)
  (∀ p : ptr, p |-> primR "void" 1$m Vvoid -∗ ▷ _PostPred_ p))
        *)
      Qed.
    End with_threads.
  End with_cpp.

End scoped_lock.
