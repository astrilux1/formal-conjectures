/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import Mathlib.Computability.TMComputable
public import Mathlib.Logic.Equiv.Bool
public import Mathlib.Tactic.DeriveFintype
public import FormalConjecturesForMathlib.Computability.Encoding

/-!
# API for polynomial-time Turing machine computability

This file develops API for `Turing.TM2ComputableInPolyTime` that is missing from Mathlib.

## Main definitions

- `Turing.TM2ComputableInPolyTime.not`: if `f : α → Bool` is computable in polynomial time,
  then so is `fun a => !(f a)`. The proof twists the output alphabet equivalence of the
  machine computing `f` by the negation equivalence on `Bool`; the machine itself is unchanged.
- `Turing.FinTM2.embedStmt` and friends: machinery to embed the execution of a Turing machine
  into a larger machine having additional stacks, labels and state, and to transport
  `Turing.EvalsTo` proofs along this embedding.
- `Turing.TM2ComputableInPolyTime.compFst`: if `f : List Bool → Bool` is computable in
  polynomial time, then so is `fun p => f p.1` on pairs (with respect to the pair encoding
  `finEncodingListBoolProdListBool`).  The machine for this function first moves the
  first component of its input onto an auxiliary stack (dropping the separator symbol and the
  second component), moves it back onto the input stack of the machine for `f` (thereby
  restoring the original order), and then runs the machine for `f`.

These are the two ingredients needed for the textbook facts `coP = P` and `P ⊆ NP`.
-/

@[expose] public section

open Computability

namespace Polynomial

/-- Evaluation of a polynomial with natural number coefficients is monotone
in its argument. -/
theorem eval_le_eval_of_le {m n : ℕ} (p : Polynomial ℕ) (h : m ≤ n) :
    p.eval m ≤ p.eval n := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [eval_add]; exact Nat.add_le_add hp hq
  | monomial i a =>
    simp only [eval_monomial]
    exact Nat.mul_le_mul_left a (Nat.pow_le_pow_left h i)

end Polynomial

namespace Turing

/-! ### Weakening the time bound of a run -/

/-- Weaken the upper bound on the number of steps of an `EvalsToInTime`. -/
def EvalsToInTime.mono {σ : Type*} {f : σ → Option σ} {a : σ} {b : Option σ} {m₁ m₂ : ℕ}
    (h : EvalsToInTime f a b m₁) (hm : m₁ ≤ m₂) : EvalsToInTime f a b m₂ :=
  ⟨h.toEvalsTo, h.steps_le_m.trans hm⟩

/-! ### Negating the output of a Turing machine

A Turing machine computing a Boolean function can be turned into a machine computing the
pointwise negation *without changing the machine at all*: it suffices to compose the output
alphabet equivalence with the negation equivalence of `Bool`.
-/

/-- If `f : α → Bool` is computable in polynomial time, then so is its pointwise negation.
The same machine works; only the output alphabet equivalence changes. -/
def TM2ComputableInPolyTime.not {α : Type} {ea : FinEncoding α} {f : α → Bool}
    (h : TM2ComputableInPolyTime ea finEncodingBoolBool f) :
    TM2ComputableInPolyTime ea finEncodingBoolBool fun a => !(f a) where
  tm := h.tm
  inputAlphabet := h.inputAlphabet
  outputAlphabet := h.outputAlphabet.trans .boolNot
  time := h.time
  outputsFun a := by
    have hlist : List.map (h.outputAlphabet.trans Equiv.boolNot).invFun [!(f a)] =
        List.map h.outputAlphabet.invFun [f a] := by
      simp [Equiv.boolNot, Function.Involutive.toPerm]
    show TM2OutputsInTime h.tm _
      (some (List.map (h.outputAlphabet.trans Equiv.boolNot).invFun [!(f a)])) _
    rw [hlist]
    exact h.outputsFun a

/-! ### Embedding a Turing machine into a larger machine

Given a machine `M` we build statements for a machine with stacks indexed by `KE ⊕ M.K`
(the `KE`-stacks are new auxiliary stacks with alphabets `ΓE`), labels indexed by
`ΛE ⊕ M.Λ` and states `E × M.σ`, in such a way that the embedded program behaves exactly
like `M` on the `M`-part of the configuration and never touches the rest.
-/

namespace FinTM2

variable {KE : Type} (ΓE : KE → Type) {ΛE E : Type} (M : FinTM2)

/-- Embed a statement of `M` into a machine with extra stacks (indexed by `KE`), extra labels
(indexed by `ΛE`) and an extra state component `E`.  The embedded statement acts on the
`M.σ`-component of the state and only refers to `M`'s stacks and labels. -/
def embedStmt : TM2.Stmt M.Γ M.Λ M.σ → TM2.Stmt (Sum.elim ΓE M.Γ) (ΛE ⊕ M.Λ) (E × M.σ)
  | .push k f q => .push (.inr k) (fun s => f s.2) (embedStmt q)
  | .peek k f q => .peek (.inr k) (fun s r => (s.1, f s.2 r)) (embedStmt q)
  | .pop k f q => .pop (.inr k) (fun s r => (s.1, f s.2 r)) (embedStmt q)
  | .load a q => .load (fun s => (s.1, a s.2)) (embedStmt q)
  | .branch f q₁ q₂ => .branch (fun s => f s.2) (embedStmt q₁) (embedStmt q₂)
  | .goto f => .goto fun s => .inr (f s.2)
  | .halt => .halt

/-- Lift a collection of stacks of `M` to the extended machine; the extra stacks are empty. -/
def embedStk (S : ∀ k, List (M.Γ k)) : ∀ k : KE ⊕ M.K, List (Sum.elim ΓE M.Γ k)
  | .inl _ => []
  | .inr k => S k

@[simp]
theorem embedStk_inl (S : ∀ k, List (M.Γ k)) (ke : KE) : embedStk ΓE M S (.inl ke) = [] := rfl

@[simp]
theorem embedStk_inr (S : ∀ k, List (M.Γ k)) (k : M.K) : embedStk ΓE M S (.inr k) = S k := rfl

/-- Lift a configuration of `M` to the extended machine.  The extra state component is `e` and
the extra stacks are empty. -/
def embedCfg (e : E) (c : TM2.Cfg M.Γ M.Λ M.σ) :
    TM2.Cfg (Sum.elim ΓE M.Γ) (ΛE ⊕ M.Λ) (E × M.σ) :=
  ⟨c.l.map .inr, (e, c.var), embedStk ΓE M c.stk⟩

section

variable [DecidableEq KE]

theorem embedStk_update (S : ∀ k, List (M.Γ k)) (k : M.K) (l : List (M.Γ k)) :
    Function.update (embedStk ΓE M S) (.inr k) l = embedStk ΓE M (Function.update S k l) := by
  funext k'
  match k' with
  | .inl ke => rw [Function.update_of_ne (by simp)]; rfl
  | .inr k'' =>
    by_cases hk : k'' = k
    · subst hk
      rw [Function.update_self, embedStk_inr, Function.update_self]
    · rw [Function.update_of_ne (by simp [hk]), embedStk_inr, embedStk_inr,
        Function.update_of_ne hk]

theorem embedStmt_stepAux (q : TM2.Stmt M.Γ M.Λ M.σ) (e : E) (v : M.σ)
    (S : ∀ k, List (M.Γ k)) :
    TM2.stepAux (embedStmt ΓE M (ΛE := ΛE) (E := E) q) (e, v) (embedStk ΓE M S) =
      embedCfg ΓE M e (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih =>
    show TM2.stepAux (embedStmt ΓE M q) (e, v)
        (Function.update (embedStk ΓE M S) (.inr k) (f v :: S k)) = _
    rw [show (f v :: S k : List (Sum.elim ΓE M.Γ (.inr k)))
        = f v :: S k from rfl, embedStk_update, ih]
    rfl
  | peek k f q ih => exact ih _ _
  | pop k f q ih =>
    show TM2.stepAux (embedStmt ΓE M q) (e, f v (S k).head?)
        (Function.update (embedStk ΓE M S) (.inr k) (S k).tail) = _
    rw [embedStk_update, ih]
    rfl
  | load a q ih => exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    show TM2.stepAux (.branch (fun s : E × M.σ => f s.2) _ _) (e, v) _ = _
    rcases hb : f v with _ | _ <;>
      simp only [TM2.stepAux, hb, cond_false, cond_true, ih₁, ih₂]
  | goto f => rfl
  | halt => rfl

variable (mE : ΛE → TM2.Stmt (Sum.elim ΓE M.Γ) (ΛE ⊕ M.Λ) (E × M.σ))

/-- The program of the extended machine: the extra labels are governed by `mE`, and the labels
of `M` run the embedded statements of `M`'s program. -/
def embedProg : ΛE ⊕ M.Λ → TM2.Stmt (Sum.elim ΓE M.Γ) (ΛE ⊕ M.Λ) (E × M.σ) :=
  Sum.elim mE fun l => embedStmt ΓE M (M.m l)

omit [DecidableEq KE] in
@[simp]
theorem embedProg_inl (le : ΛE) : embedProg ΓE M mE (.inl le) = mE le := rfl

omit [DecidableEq KE] in
@[simp]
theorem embedProg_inr (l : M.Λ) : embedProg ΓE M mE (.inr l) = embedStmt ΓE M (M.m l) := rfl

theorem embedProg_step (e : E) (c : TM2.Cfg M.Γ M.Λ M.σ) :
    TM2.step (embedProg ΓE M mE) (embedCfg ΓE M e c) =
      (TM2.step M.m c).map (embedCfg ΓE M e) := by
  obtain ⟨l, v, S⟩ := c
  cases l with
  | none => rfl
  | some l =>
    show some (TM2.stepAux (embedStmt ΓE M (M.m l)) (e, v) (embedStk ΓE M S)) = _
    rw [embedStmt_stepAux]
    rfl

theorem iterate_bind_map {σ₁ σ₂ : Type*} {f : σ₁ → Option σ₁} {g : σ₂ → Option σ₂}
    (φ : σ₁ → σ₂) (hcomm : ∀ c, g (φ c) = (f c).map φ) (n : ℕ) (o : Option σ₁) :
    (flip bind g)^[n] (o.map φ) = ((flip bind f)^[n] o).map φ := by
  induction n generalizing o with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    have hstep : (flip bind g) (o.map φ) = ((flip bind f) o).map φ := by
      cases o with
      | none => rfl
      | some c => exact hcomm c
    rw [hstep, ih]

/-- Transport a timed run of `M` along the embedding into the extended machine. -/
def embedEvalsToInTime (e : E) {c₁ c₂ : TM2.Cfg M.Γ M.Λ M.σ} {n : ℕ}
    (h : EvalsToInTime (TM2.step M.m) c₁ (some c₂) n) :
    EvalsToInTime (TM2.step (embedProg ΓE M mE)) (embedCfg ΓE M e c₁)
      (some (embedCfg ΓE M e c₂)) n :=
  ⟨⟨h.steps, by
    have := iterate_bind_map (f := TM2.step M.m) (g := TM2.step (embedProg ΓE M mE))
      (embedCfg ΓE M e) (embedProg_step ΓE M mE e) h.steps (some c₁)
    simp only [Option.map_some] at this
    rw [this, h.evals_in_steps]
    rfl⟩, h.steps_le_m⟩

end

end FinTM2

/-! ### Precomposition with the first projection

Given a machine `M` computing `f : List Bool → Bool` (with respect to the encodings
`finEncodingListBool` and `finEncodingBoolBool`), we construct a machine computing
`fun p => f p.1` on `List Bool × List Bool` with respect to the pair encoding
`finEncodingListBoolProdListBool`.

The machine has two extra stacks: its input stack (with alphabet `Option (M.Γ M.k₀)`,
matching the alphabet `Option Bool` of the pair encoding) and a buffer stack (with alphabet
`M.Γ M.k₀`).  It runs in four phases:

1. `strip`: pop elements off the input stack, pushing the payloads onto the buffer, until the
   separator symbol `none` is found;
2. `drain`: pop the remaining elements (the second component) off the input stack;
3. `transfer`: move the buffer contents onto `M`'s input stack (which restores the original
   order of the first component);
4. run (the embedded) `M`.
-/

namespace TM2ComputableInPolyTime

/-- The labels of the preprocessing phases of the machine constructed in
`Turing.TM2ComputableInPolyTime.compFst`. -/
inductive PrepLabel : Type
  | strip
  | drain
  | transfer
  deriving DecidableEq, Fintype, Inhabited

variable (M : FinTM2)

/-- The alphabets of the two auxiliary stacks used in
`Turing.TM2ComputableInPolyTime.compFst`: the new input stack (indexed by `false`) carries
`Option (M.Γ M.k₀)` and the buffer stack (indexed by `true`) carries `M.Γ M.k₀`. -/
def pairΓ : Bool → Type
  | false => Option (M.Γ M.k₀)
  | true => M.Γ M.k₀

open TM2.Stmt in
/-- The preprocessing program: strip the first component of the encoded pair onto the buffer
stack, drain the rest of the input, transfer the buffer onto `M`'s input stack, and hand over
control to `M`. -/
def prepProg (d : M.Γ M.k₀) : PrepLabel →
    TM2.Stmt (Sum.elim (pairΓ M) M.Γ) (PrepLabel ⊕ M.Λ) (Option (Option (M.Γ M.k₀)) × M.σ)
  | .strip =>
    pop (.inl false) (fun s r => (r, s.2)) <|
      branch (fun s => s.1.isSome)
        (branch (fun s => (s.1.getD none).isSome)
          (push (.inl true) (fun s => (s.1.getD none).getD d) <|
            load (fun s => (none, s.2)) <| goto fun _ => .inl .strip)
          (load (fun s => (none, s.2)) <| goto fun _ => .inl .drain))
        halt
  | .drain =>
    pop (.inl false) (fun s r => (r, s.2)) <|
      branch (fun s => s.1.isSome)
        (load (fun s => (none, s.2)) <| goto fun _ => .inl .drain)
        (load (fun s => (none, s.2)) <| goto fun _ => .inl .transfer)
  | .transfer =>
    pop (.inl true) (fun s r => (r.map some, s.2)) <|
      branch (fun s => s.1.isSome)
        (push (.inr M.k₀) (fun s => (s.1.getD none).getD d) <|
          load (fun s => (none, s.2)) <| goto fun _ => .inl .transfer)
        (goto fun _ => .inr M.main)

/-- The machine computing `fun p => f p.1` from a machine `M` computing `f`:
two auxiliary stacks (input and buffer), three preprocessing labels, an extra state component
remembering the most recently popped symbol, and a copy of `M`. -/
@[reducible] def verifierTM (d : M.Γ M.k₀) : FinTM2 :=
  letI := M.kFin
  letI := M.ΛFin
  letI := M.σFin
  letI := M.Γk₀Fin
  { K := Bool ⊕ M.K
    k₀ := .inl false
    k₁ := .inr M.k₁
    Γ := Sum.elim (pairΓ M) M.Γ
    Λ := PrepLabel ⊕ M.Λ
    main := .inl .strip
    σ := Option (Option (M.Γ M.k₀)) × M.σ
    initialState := (none, M.initialState)
    Γk₀Fin := inferInstanceAs (Fintype (Option (M.Γ M.k₀)))
    m := FinTM2.embedProg (pairΓ M) M (prepProg M d) }

variable {d : M.Γ M.k₀}

/-- The stacks of the machine `verifierTM M d`, given as the input stack, the buffer stack and
the stacks of `M`. -/
def pairStk (inp : List (Option (M.Γ M.k₀))) (buf : List (M.Γ M.k₀))
    (S : ∀ k, List (M.Γ k)) : ∀ k : Bool ⊕ M.K, List (Sum.elim (pairΓ M) M.Γ k)
  | .inl false => inp
  | .inl true => buf
  | .inr k => S k

@[simp]
theorem pairStk_inl_false (inp buf S) : pairStk M inp buf S (.inl false) = inp := rfl

@[simp]
theorem pairStk_inl_true (inp buf S) : pairStk M inp buf S (.inl true) = buf := rfl

@[simp]
theorem pairStk_inr (inp buf S) (k : M.K) : pairStk M inp buf S (.inr k) = S k := rfl

section StackLemmas

theorem pairStk_update_input (inp buf S) (l : List (Option (M.Γ M.k₀))) :
    Function.update (pairStk M inp buf S) (.inl false) l = pairStk M l buf S := by
  funext k'
  match k' with
  | .inl false => rw [Function.update_self]; rfl
  | .inl true => rw [Function.update_of_ne (by simp)]; rfl
  | .inr k => rw [Function.update_of_ne (by simp)]; rfl

theorem pairStk_update_buffer (inp buf S) (l : List (M.Γ M.k₀)) :
    Function.update (pairStk M inp buf S) (.inl true) l = pairStk M inp l S := by
  funext k'
  match k' with
  | .inl false => rw [Function.update_of_ne (by simp)]; rfl
  | .inl true => rw [Function.update_self]; rfl
  | .inr k => rw [Function.update_of_ne (by simp)]; rfl

theorem pairStk_update_mstack (inp buf S) (k : M.K) (l : List (M.Γ k)) :
    Function.update (pairStk M inp buf S) (.inr k) l =
      pairStk M inp buf (Function.update S k l) := by
  funext k'
  match k' with
  | .inl false => rw [Function.update_of_ne (by simp)]; rfl
  | .inl true => rw [Function.update_of_ne (by simp)]; rfl
  | .inr k'' =>
    by_cases hk : k'' = k
    · subst hk
      rw [Function.update_self, pairStk_inr, Function.update_self]
    · rw [Function.update_of_ne (by simp [hk]), pairStk_inr, pairStk_inr,
        Function.update_of_ne hk]

theorem pairStk_nil_nil (S) :
    pairStk M [] [] S = FinTM2.embedStk (pairΓ M) M S := by
  funext k'
  match k' with
  | .inl false => rfl
  | .inl true => rfl
  | .inr k => rfl

theorem initList_verifierTM_stk (l : List (Option (M.Γ M.k₀))) :
    (initList (verifierTM M d) l).stk = pairStk M l [] fun _ => [] := by
  funext k'
  show dite _ _ _ = _
  match k' with
  | .inl false => rfl
  | .inl true => rfl
  | .inr k => rfl

theorem initList_stk (tm : FinTM2) (l : List (tm.Γ tm.k₀)) :
    (initList tm l).stk =
      Function.update (fun _ => []) tm.k₀ l := by
  funext k
  show dite _ _ _ = _
  by_cases hk : k = tm.k₀
  · subst hk
    rw [dif_pos rfl, Function.update_self]
    rfl
  · rw [dif_neg hk, Function.update_of_ne hk]

theorem haltList_verifierTM_stk (l : List (M.Γ M.k₁)) :
    (haltList (verifierTM M d) l).stk =
      FinTM2.embedStk (pairΓ M) M (haltList M l).stk := by
  funext k'
  show dite _ _ _ = _
  match k' with
  | .inl false => rfl
  | .inl true => rfl
  | .inr k =>
    show dite _ _ _ = dite _ _ _
    by_cases hk : k = M.k₁
    · subst hk
      rw [dif_pos rfl, dif_pos rfl]
    · rw [dif_neg (by simp [hk]), dif_neg hk]

end StackLemmas

section PhaseLemmas

theorem flip_bind_some {σ : Type*} (g : σ → Option σ) (c : σ) :
    flip bind g (some c) = g c := rfl

/-- Phase 1: strip the first component of the pair onto the buffer stack. -/
theorem strip_iterate (xs : List (M.Γ M.k₀)) (ws : List (Option (M.Γ M.k₀)))
    (buf : List (M.Γ M.k₀)) (v : M.σ) (S : ∀ k, List (M.Γ k)) :
    (flip bind (verifierTM M d).step)^[xs.length + 1]
        (some ⟨some (.inl .strip), (none, v),
          pairStk M (xs.map some ++ none :: ws) buf S⟩) =
      some ⟨some (.inl .drain), (none, v), pairStk M ws (xs.reverse ++ buf) S⟩ := by
  induction xs generalizing buf with
  | nil =>
    simp only [List.length_nil, Nat.zero_add, Function.iterate_one, flip_bind_some]
    show some (TM2.stepAux (prepProg M d .strip) _ _) = _
    simp [prepProg, pairStk_update_input, TM2.stepAux]
  | cons b xs ih =>
    rw [show (b :: xs).length + 1 = (xs.length + 1) + 1 from rfl,
      Function.iterate_succ_apply, flip_bind_some]
    have hstep : (verifierTM M d).step
        ⟨some (.inl .strip), (none, v),
          pairStk M ((b :: xs).map some ++ none :: ws) buf S⟩ =
        some ⟨some (.inl .strip), (none, v),
          pairStk M (xs.map some ++ none :: ws) (b :: buf) S⟩ := by
      show some (TM2.stepAux (prepProg M d .strip) _ _) = _
      simp [prepProg, pairStk_update_input, pairStk_update_buffer, TM2.stepAux]
    rw [hstep, ih]
    simp [List.append_assoc]

/-- Phase 2: drain the remainder of the input stack. -/
theorem drain_iterate (ws : List (Option (M.Γ M.k₀))) (buf : List (M.Γ M.k₀))
    (v : M.σ) (S : ∀ k, List (M.Γ k)) :
    (flip bind (verifierTM M d).step)^[ws.length + 1]
        (some ⟨some (.inl .drain), (none, v), pairStk M ws buf S⟩) =
      some ⟨some (.inl .transfer), (none, v), pairStk M [] buf S⟩ := by
  induction ws with
  | nil =>
    simp only [List.length_nil, Nat.zero_add, Function.iterate_one, flip_bind_some]
    show some (TM2.stepAux (prepProg M d .drain) _ _) = _
    simp [prepProg, pairStk_update_input, TM2.stepAux]
  | cons w ws ih =>
    rw [show (w :: ws).length + 1 = (ws.length + 1) + 1 from rfl,
      Function.iterate_succ_apply, flip_bind_some]
    have hstep : (verifierTM M d).step
        ⟨some (.inl .drain), (none, v), pairStk M (w :: ws) buf S⟩ =
        some ⟨some (.inl .drain), (none, v), pairStk M ws buf S⟩ := by
      show some (TM2.stepAux (prepProg M d .drain) _ _) = _
      simp [prepProg, pairStk_update_input, TM2.stepAux]
    rw [hstep, ih]

/-- Phase 3: transfer the buffer onto `M`'s input stack, then hand over control to `M`. -/
theorem transfer_iterate (bs : List (M.Γ M.k₀)) (v : M.σ)
    (S : ∀ k, List (M.Γ k)) :
    (flip bind (verifierTM M d).step)^[bs.length + 1]
        (some ⟨some (.inl .transfer), (none, v), pairStk M [] bs S⟩) =
      some ⟨some (.inr M.main), (none, v),
        pairStk M [] []
          (Function.update S M.k₀ (bs.reverse ++ S M.k₀))⟩ := by
  induction bs generalizing S with
  | nil =>
    simp only [List.length_nil, Nat.zero_add, Function.iterate_one, flip_bind_some]
    show some (TM2.stepAux (prepProg M d .transfer) _ _) = _
    simp [prepProg, pairStk_update_buffer, TM2.stepAux, Function.update_eq_self]
  | cons g bs ih =>
    rw [show (g :: bs).length + 1 = (bs.length + 1) + 1 from rfl,
      Function.iterate_succ_apply, flip_bind_some]
    have hstep : (verifierTM M d).step
        ⟨some (.inl .transfer), (none, v), pairStk M [] (g :: bs) S⟩ =
        some ⟨some (.inl .transfer), (none, v),
          pairStk M [] bs (Function.update S M.k₀ (g :: S M.k₀))⟩ := by
      show some (TM2.stepAux (prepProg M d .transfer) _ _) = _
      simp [prepProg, pairStk_update_buffer, pairStk_update_mstack, TM2.stepAux]
    rw [hstep, ih]
    congr 2
    rw [Function.update_self, Function.update_idem]
    simp

end PhaseLemmas

open Polynomial in
/-- If `f : List Bool → Bool` is computable in polynomial time, then so is `fun p => f p.1` on
pairs of lists, with respect to the pair encoding `finEncodingListBoolProdListBool`.

This is the machine underlying the textbook proof that `P ⊆ NP`: a verifier may simply ignore
its witness and run the polynomial time decider on the instance. -/
noncomputable def compFst {f : List Bool → Bool}
    (h : TM2ComputableInPolyTime finEncodingListBool finEncodingBoolBool f) :
    TM2ComputableInPolyTime finEncodingListBoolProdListBool finEncodingBoolBool
      fun p => f p.1 where
  tm := verifierTM h.tm (h.inputAlphabet.symm false)
  inputAlphabet := h.inputAlphabet.optionCongr
  outputAlphabet := h.outputAlphabet
  time := h.time + C 2 * X + C 3
  outputsFun := by
    rintro ⟨x, w⟩
    set M := h.tm with hM
    set d : M.Γ M.k₀ := h.inputAlphabet.symm false with hd
    set xs : List (M.Γ M.k₀) := x.map h.inputAlphabet.symm with hxs
    set ws : List (Option (M.Γ M.k₀)) := (w.map h.inputAlphabet.symm).map some with hws
    -- The encoded input, as seen on the input stack of the verifier machine.
    have hinput : List.map (h.inputAlphabet.optionCongr).invFun
        (finEncodingListBoolProdListBool.encode (x, w)) = xs.map some ++ none :: ws := by
      simp only [finEncodingListBoolProdListBool, hxs, hws, Equiv.optionCongr,
        Equiv.invFun_as_coe, Equiv.coe_fn_symm_mk, List.map_append, List.map_map,
        List.map_cons, Function.comp_def, List.append_assoc,
        List.singleton_append]
      rfl
    -- Phase 1-3: preprocessing.
    have e₁ : EvalsToInTime (verifierTM M d).step
        (initList (verifierTM M d) (List.map (h.inputAlphabet.optionCongr).invFun
          (finEncodingListBoolProdListBool.encode (x, w))))
        (some ⟨some (.inl .drain), (none, M.initialState),
          pairStk M ws xs.reverse (fun _ => [])⟩) (x.length + 1) := by
      refine ⟨⟨xs.length + 1, ?_⟩, ?_⟩
      · have hinit : initList (verifierTM M d) (List.map (h.inputAlphabet.optionCongr).invFun
            (finEncodingListBoolProdListBool.encode (x, w))) =
            ⟨some (.inl .strip), (none, M.initialState),
              pairStk M (xs.map some ++ none :: ws) [] fun _ => []⟩ := by
          rw [show (initList (verifierTM M d) _ : TM2.Cfg _ _ _) =
            ⟨some (.inl .strip), (none, M.initialState), (initList (verifierTM M d) _).stk⟩
            from rfl, initList_verifierTM_stk, hinput]
        rw [hinit]
        simpa using strip_iterate M (d := d) xs ws [] M.initialState fun _ => []
      · simp [hxs]
    have e₂ : EvalsToInTime (verifierTM M d).step
        (⟨some (.inl .drain), (none, M.initialState),
          pairStk M ws xs.reverse (fun _ => [])⟩ : TM2.Cfg _ _ _)
        (some ⟨some (.inl .transfer), (none, M.initialState),
          pairStk M [] xs.reverse (fun _ => [])⟩) (w.length + 1) :=
      ⟨⟨ws.length + 1, drain_iterate M ws xs.reverse M.initialState fun _ => []⟩,
        by simp [hws]⟩
    have e₃ : EvalsToInTime (verifierTM M d).step
        (⟨some (.inl .transfer), (none, M.initialState),
          pairStk M [] xs.reverse (fun _ => [])⟩ : TM2.Cfg _ _ _)
        (some ⟨some (.inr M.main), (none, M.initialState),
          pairStk M [] [] (Function.update (fun _ => []) M.k₀ xs)⟩) (x.length + 1) := by
      have hiter := transfer_iterate M (d := d) xs.reverse M.initialState fun _ => []
      simp only [List.reverse_reverse, List.append_nil] at hiter
      exact ⟨⟨xs.reverse.length + 1, hiter⟩, by simp [hxs]⟩
    -- Phase 4: the embedded run of `M`.
    have e₄ : EvalsToInTime (verifierTM M d).step
        (⟨some (.inr M.main), (none, M.initialState),
          pairStk M [] [] (Function.update (fun _ => []) M.k₀ xs)⟩ : TM2.Cfg _ _ _)
        (some (haltList (verifierTM M d)
          (List.map h.outputAlphabet.invFun (finEncodingBoolBool.encode (f x)))))
        (h.time.eval x.length) := by
      have hstart : FinTM2.embedCfg (ΛE := PrepLabel) (E := Option (Option (M.Γ M.k₀)))
          (pairΓ M) M none
          (initList M (List.map h.inputAlphabet.invFun (finEncodingListBool.encode x))) =
          (⟨some (.inr M.main), (none, M.initialState),
            pairStk M [] [] (Function.update (fun _ => []) M.k₀ xs)⟩ : TM2.Cfg _ _ _) := by
        rw [FinTM2.embedCfg]
        congr 1
        rw [pairStk_nil_nil]
        congr 1
        rw [initList_stk]
        rfl
      have hend : FinTM2.embedCfg (ΛE := PrepLabel) (E := Option (Option (M.Γ M.k₀)))
          (pairΓ M) M none
          (haltList M (List.map h.outputAlphabet.invFun (finEncodingBoolBool.encode (f x)))) =
          haltList (verifierTM M d)
            (List.map h.outputAlphabet.invFun (finEncodingBoolBool.encode (f x))) := by
        rw [FinTM2.embedCfg]
        rw [show (haltList (verifierTM M d) (List.map h.outputAlphabet.invFun
            (finEncodingBoolBool.encode (f x))) : TM2.Cfg _ _ _) =
          ⟨none, (none, M.initialState), (haltList (verifierTM M d)
            (List.map h.outputAlphabet.invFun (finEncodingBoolBool.encode (f x)))).stk⟩
          from rfl, haltList_verifierTM_stk]
        rfl
      rw [← hstart, ← hend]
      exact FinTM2.embedEvalsToInTime (pairΓ M) M (prepProg M d) none (h.outputsFun x)
    -- Compose the phases and account for the time.
    have total := EvalsToInTime.trans _ _ _ _ _ _
      (EvalsToInTime.trans _ _ _ _ _ _
        (EvalsToInTime.trans _ _ _ _ _ _ e₁ e₂) e₃) e₄
    refine total.mono ?_
    have hlen : (finEncodingListBoolProdListBool.encode (x, w)).length
        = x.length + w.length + 1 := by
      simp [finEncodingListBoolProdListBool]
      try omega
    rw [hlen]
    have hmono : h.time.eval x.length ≤ h.time.eval (x.length + w.length + 1) :=
      h.time.eval_le_eval_of_le (by omega)
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X]
    omega

end TM2ComputableInPolyTime

end Turing
