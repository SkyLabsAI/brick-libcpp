Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.brick.libstdcpp.iostream_trace.spec.
Require Import skylabs.brick.libstdcpp.iostream_trace.inc_iostream_cpp.

(* The translated stream class has unsupported virtual-base layout and its
   generated size metadata is therefore unavailable. *)
Lemma translated_ostream_size_unknown :
  size_of {| genv_tu := source; member_pointer_bitsize := bitsize.W64 |}
    "std::basic_ostream<char, std::char_traits<char>>" = None.
Proof. vm_compute. reflexivity. Qed.

(* Unsupported declarations cannot acquire layout metadata in a compatible
   resolver. The typed stream contract therefore excludes this translation. *)
Lemma translated_ostream_size_unknown_compat (σ : genv) (Hσ : source ⊧ σ) :
  size_of σ "std::basic_ostream<char, std::char_traits<char>>" = None.
Proof.
  have E : exists msg,
    source.(types) !! ("std::basic_ostream<char, std::char_traits<char>>" : name) =
      Some (Gunsupported msg).
  { vm_compute. eexists. reflexivity. }
  destruct E as [msg E].
  destruct Hσ as [Hsub].
  apply (sub_module_preserves_globdecl Hsub) in E as [gd' [Hg' Hle]].
  cbn [size_of]. rewrite /glob_def Hg'.
  destruct gd'; cbn [GlobDecl_ler GlobDecl_le] in Hle;
    try contradiction; reflexivity.
Qed.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.

  (* The standard typing contract supplies reference information through shared
     hints, independently of any particular translated module. *)
  Lemma ostream_contract_reference (p : ptr) q state :
    (p |-> ostreamR q state)
    |-- reference_to "std::basic_ostream<char, std::char_traits<char>>" p.
  Proof. go. Qed.

  Lemma unsupported_ostream_type_ptr (Hσ : source ⊧ σ) (p : ptr) :
    (p |-> type_ptrR "std::basic_ostream<char, std::char_traits<char>>") |-- False.
  Proof.
    rewrite _at_type_ptrR type_ptr_size (translated_ostream_size_unknown_compat σ Hσ).
    iIntros "%Hsize". destruct Hsize as [sz Hsize]. discriminate Hsize.
  Qed.

  Lemma unsupported_ostream_contract (Hσ : source ⊧ σ) (p : ptr) q state :
    (p |-> ostreamR q state) |-- False.
  Proof.
    iIntros "H".
    iDestruct (observe (p |-> type_ptrR
      "std::basic_ostream<char, std::char_traits<char>>") with "H") as "#T".
    iApply (unsupported_ostream_type_ptr Hσ p). iExact "T".
  Qed.

  (* This checks the shared hints conditional on the library stream contract.
     It does not claim that the unsupported translated stream is inhabitable. *)
  Lemma cout_lvalue_from_stream (ρ : region) q state :
      [| source ⊧ σ |] ** (_global "std::cout" |-> ostreamR q state)
    |-- wp_lval source ρ
      (Eglobal "std::cout" "std::basic_ostream<char, std::char_traits<char>>")
      (fun _ _ => _global "std::cout" |-> ostreamR q state).
  Proof. go. Qed.
End with_cpp.
