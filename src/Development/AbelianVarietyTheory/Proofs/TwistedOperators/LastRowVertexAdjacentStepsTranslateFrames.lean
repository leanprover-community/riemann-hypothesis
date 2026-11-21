import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ValuationGdetKapAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StepLin
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SecondCountableLocal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralCompBlocks
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInverseUnipotentVolumeConjDiagonalEq

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv GlobalTheory.StepLeft Classical

noncomputable section
namespace GlobalTheory.StepLeft

section Shape
variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

omit [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] in

theorem basePt_eq_zero_of_stepVar (y : Matrix n n' k) {r : n ⊕ Fin c} {s : n' ⊕ Fin (c + 1)}
    (h : Free (c / 2 + 1) (r, s) ∨ Kept (r, s)) : basePt c y r s = 0 := by
  rcases r with r | r <;> rcases s with s | s <;> simp only [Free, Kept, or_false, false_or] at h <;>
    simp only [basePt, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
      Matrix.zero_apply, of_apply]
  rw [if_neg (by omega)]

omit [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] in

theorem stepVar_fixed_of_ordL_lt (y : Matrix n n' k) {r t : n ⊕ Fin c} {s : n' ⊕ Fin (c + 1)}
    (hv : ¬ (Free (c / 2 + 1) (r, s) ∨ Kept (r, s))) (hlt : GlobalTheory.DiagVol.ordL c r < GlobalTheory.DiagVol.ordL c t) :
    ¬ (Free (c / 2 + 1) (t, s) ∨ Kept (t, s)) ∧ basePt c y t s = 0 := by
  rcases r with r | r <;> rcases t with t | t <;> rcases s with s | s <;>
    simp only [Free, Kept, GlobalTheory.DiagVol.ordL, Sum.elim_inl, Sum.elim_inr, basePt, fromBlocks_apply₁₁,
      fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.zero_apply, of_apply, not_or,
      Nat.even_iff, Nat.odd_iff, not_and, true_and, and_true, not_false_eq_true, not_true_eq_false] at hv hlt ⊢
  all_goals first | omega | (refine ⟨⟨by omega, by omega⟩, ?_⟩; rw [if_neg (by omega)]) | (refine ⟨by omega, ?_⟩; rw [if_neg (by omega)]) | skip

end Shape

section Shape2
variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

omit [Fintype n'] [DecidableEq n'] in

theorem unipSub_mul_fixed {u : GL (n ⊕ Fin c) k} (hu : u ∈ GlobalTheory.DiagVol.unipSub (GlobalTheory.DiagVol.ordL c))
    (y : Matrix n n' k) (M : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)
    (hM : ∀ r s, ¬ (Free (c / 2 + 1) (r, s) ∨ Kept (r, s)) → M r s = basePt c y r s) :
    ∀ r s, ¬ (Free (c / 2 + 1) (r, s) ∨ Kept (r, s)) → (u.val * M) r s = basePt c y r s := by
  intro r s hv
  have hu' : ∀ r t, GlobalTheory.DiagVol.ordL c t ≤ GlobalTheory.DiagVol.ordL c r →
      u.val r t = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r t := hu
  rw [Matrix.mul_apply, Finset.sum_eq_single r]
  · rw [hu' r r le_rfl, Matrix.one_apply_eq, one_mul, hM r s hv]
  · intro t _ htr
    by_cases h : GlobalTheory.DiagVol.ordL c t ≤ GlobalTheory.DiagVol.ordL c r
    · rw [hu' r t h, Matrix.one_apply_ne (Ne.symm htr), zero_mul]
    · obtain ⟨h1, h2⟩ := stepVar_fixed_of_ordL_lt y hv (not_le.1 h)
      rw [hM t s h1, h2, mul_zero]
  · simp

omit [Fintype n'] [DecidableEq n'] in

theorem embX_mul_fixed (κ : GL n k) (y : Matrix n n' k) (M : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)
    (hM : ∀ r s, ¬ (Free (c / 2 + 1) (r, s) ∨ Kept (r, s)) → M r s = basePt c y r s) :
    ∀ r s, ¬ (Free (c / 2 + 1) (r, s) ∨ Kept (r, s)) →
      ((embX c κ).val * M) r s = basePt c (κ.val * y) r s := by
  intro r s hv
  have hE : (embX c κ).val = (fromBlocks κ.val 0 0 1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) := rfl
  rw [hE, Matrix.mul_apply, Fintype.sum_sum_type]
  rcases r with a | l
  · simp only [fromBlocks_apply₁₁, fromBlocks_apply₁₂, Matrix.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
    have hb : ∀ b, M (Sum.inl b) s = basePt c y (Sum.inl b) s := fun b =>
      hM _ _ (by rcases s with s | s <;> simpa only [Free, Kept] using hv)
    simp only [hb]
    rcases s with s | s <;> simp [basePt, Matrix.mul_apply]
  · simp only [fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.zero_apply, zero_mul, Finset.sum_const_zero, zero_add]
    rw [Finset.sum_eq_single l (fun j _ hj => by rw [Matrix.one_apply_ne (Ne.symm hj), zero_mul]) (by simp),
      Matrix.one_apply_eq, one_mul, hM _ _ hv]
    rcases s with s | s <;> simp [basePt]

end Shape2

theorem inv_mul_stepPt_shape : ∀ {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ} (v : GL (n ⊕ Fin c) k), v ∈ symN k n c → ∀ (κ : GL n k) (x₀ : Matrix n n' k) (e : StepVar n c n' → k), ((v * embX c κ)⁻¹).val * stepPt x₀ e = stepPt ((κ⁻¹).val * x₀) (fun a => (((v * embX c κ)⁻¹).val * stepPt x₀ e : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) a.1.1 a.1.2) := by
  intro k _ n n' _ _ _ _ c v hv κ x₀ e
  have hg : ((v * embX c κ)⁻¹).val = (embX c κ⁻¹).val * (v⁻¹).val := by
    rw [_root_.mul_inv_rev, map_inv, Units.val_mul]
  have hu : v⁻¹ ∈ GlobalTheory.DiagVol.unipSub (GlobalTheory.DiagVol.ordL c) := GlobalTheory.DiagVol.symN_le_unipSub (inv_mem hv)
  have hM : ∀ r s, ¬ (Free (c / 2 + 1) (r, s) ∨ Kept (r, s)) → stepPt x₀ e r s = basePt c x₀ r s :=
    fun r s h => by rw [stepPt, Matrix.add_apply, of_apply, dif_neg h, add_zero]
  have hA := embX_mul_fixed κ⁻¹ x₀ _ (unipSub_mul_fixed hu x₀ _ hM)
  have hR : ∀ (y : Matrix n n' k) (e' : StepVar n c n' → k) r s, stepPt y e' r s =
      basePt c y r s + (if h : Free (c / 2 + 1) (r, s) ∨ Kept (r, s) then e' ⟨(r, s), h⟩ else 0) :=
    fun _ _ _ _ => rfl
  ext r s
  by_cases h : Free (c / 2 + 1) (r, s) ∨ Kept (r, s)
  · conv_rhs => rw [hR, dif_pos h, basePt_eq_zero_of_stepVar _ h, zero_add]
  · conv_rhs => rw [hR, dif_neg h, add_zero]
    rw [hg, Matrix.mul_assoc, hA r s h]

end GlobalTheory.StepLeft
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv GlobalTheory.StepLeft Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodStep_inv_mul_point_shape : ∀ {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ} (v : GL (n ⊕ Fin c) k), v ∈ symN k n c → ∀ (κ : GL n k) (x₀ : Matrix n n' k) (e : StepVar n c n' → k), ((v * embX c κ)⁻¹).val * stepPt x₀ e = stepPt ((κ⁻¹).val * x₀) (fun a => (((v * embX c κ)⁻¹).val * stepPt x₀ e : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) a.1.1 a.1.2) := by
  atlas_forward_decl GlobalTheory.StepLeft.inv_mul_stepPt_shape
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv GlobalTheory.StepLeft Classical

noncomputable section
namespace GlobalTheory.StepLeft

def splitVar {n m σ : Type} (P : (n ⊕ m) × σ → Prop) (Q : σ → Prop) (h : ∀ r s, P (Sum.inl r, s) ↔ Q s) :
    (n × {s // Q s}) ⊕ {ls : m × σ // P (Sum.inr ls.1, ls.2)} ≃ {rs // P rs} where
  toFun := Sum.elim (fun a => ⟨(Sum.inl a.1, a.2.1), (h _ _).2 a.2.2⟩) (fun a => ⟨(Sum.inr a.1.1, a.1.2), a.2⟩)
  invFun := fun a => match a with
    | ⟨(Sum.inl r, s), hs⟩ => Sum.inl (r, ⟨s, (h _ _).1 hs⟩)
    | ⟨(Sum.inr l, s), hs⟩ => Sum.inr ⟨(l, s), hs⟩
  left_inv := by rintro (⟨r, s, hs⟩ | ⟨⟨l, s⟩, hs⟩) <;> rfl
  right_inv := by rintro ⟨⟨r | r, s⟩, hs⟩ <;> rfl

theorem det_colwise_fromBlocks {k : Type} [CommRing k] {n m σ : Type} [Fintype n] [DecidableEq n] [Fintype m]
    [DecidableEq m] [Fintype σ] (P : (n ⊕ m) × σ → Prop) (Q : σ → Prop) (h : ∀ r s, P (Sum.inl r, s) ↔ Q s)
    [Fintype {rs // P rs}] [DecidableEq {rs // P rs}] (κ : Matrix n n k)
    (M : Matrix {rs // P rs} {rs // P rs} k)
    (hM : ∀ a b, M a b = if a.1.2 = b.1.2 then (fromBlocks κ 0 0 1 : Matrix (n ⊕ m) (n ⊕ m) k) a.1.1 b.1.1 else 0) :
    M.det = κ.det ^ Fintype.card {s // Q s} := by
  rw [← det_submatrix_equiv_self (splitVar P Q h) M]
  have : M.submatrix (splitVar P Q h) (splitVar P Q h) =
      fromBlocks (blockDiagonal fun _ : {s // Q s} => κ) 0 0 1 := by
    ext a b
    rcases a with (⟨r, s, hs⟩ | ⟨⟨l, s⟩, hs⟩) <;> rcases b with (⟨r', s', hs'⟩ | ⟨⟨l', s'⟩, hs'⟩) <;>
      simp [hM, splitVar, blockDiagonal_apply, one_apply]
    by_cases h1 : s = s' <;> by_cases h2 : l = l' <;> simp [h1, h2]
  rw [this, det_fromBlocks_zero₂₁, det_blockDiagonal]
  simp

theorem valuation_det_stepLin_embX : ∀ {k : Type} [Field k] [ValuativeRel k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ} (κ : GL n k), valuation k (gdet κ : k) = 1 → valuation k (stepLin n' (embX c κ).val).det = 1 := by
  intro k _ _ n n' _ _ _ _ c κ hκ
  let Q : n' ⊕ Fin (c + 1) → Prop := Sum.elim (fun _ => False)
    (fun i => c / 2 + 1 < i.val + 1 ∨ (Even c ∧ i.val = c / 2))
  have h : ∀ (r : n) s, (Free (c := c) (c / 2 + 1) (Sum.inl r, s) ∨ Kept (c := c) (Sum.inl r, s)) ↔ Q s := by
    rintro r (s | s) <;> simp [Q, Free, Kept]
  rw [det_colwise_fromBlocks (fun rs => Free (c / 2 + 1) rs ∨ Kept rs) Q h κ.val _ (fun a b => by
    simp only [stepLin, of_apply]; split_ifs <;> rfl), map_pow]
  have : valuation k κ.val.det = 1 := hκ
  rw [this, one_pow]

end GlobalTheory.StepLeft
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv GlobalTheory.StepLeft Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_det_stageVariables_embedGL_eq_one : ∀ {k : Type} [Field k] [ValuativeRel k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ} (κ : GL n k), valuation k (gdet κ : k) = 1 → valuation k (stepLin n' (embX c κ).val).det = 1 := by
  atlas_forward_decl GlobalTheory.StepLeft.valuation_det_stepLin_embX
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

noncomputable section
namespace GlobalTheory.StepLeft
open Classical

theorem affine {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
    (g : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (x₀ : Matrix n n' k) (e : StepVar n c n' → k) :
    (fun a : StepVar n c n' => (g * stepPt x₀ e) a.1.1 a.1.2) =
      (stepLin n' g).mulVec e + fun a => (g * stepPt x₀ (0 : StepVar n c n' → k) : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) a.1.1 a.1.2 := by
  funext a
  obtain ⟨⟨r, s⟩, ha⟩ := a
  have h1 : (stepLin n' g).mulVec e ⟨(r, s), ha⟩ =
      ∑ t, g r t * (if h : (Free (c / 2 + 1) (t, s) ∨ Kept (t, s)) then e ⟨(t, s), h⟩ else 0) := by
    have h2 : (stepLin n' g).mulVec e ⟨(r, s), ha⟩ = ∑ b : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)),
        (if s = b.2 then g r b.1 else 0) * (if h : (Free (c / 2 + 1) b ∨ Kept b) then e ⟨b, h⟩ else 0) := by
      rw [← Fintype.sum_subtype_add_sum_subtype (fun b => Free (c / 2 + 1) b ∨ Kept b)]
      rw [Finset.sum_eq_zero (s := Finset.univ) (f := fun b : {b // ¬ (Free (c / 2 + 1) b ∨ Kept b)} => _)
        (fun b _ => by rw [dif_neg b.2, mul_zero]), add_zero]
      simp only [Matrix.mulVec, dotProduct, stepLin, of_apply]
      refine Finset.sum_congr rfl fun b _ => by rw [dif_pos b.2]
    rw [h2, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.sum_eq_single s]
    · simp
    · intro s' _ hs
      simp [Ne.symm hs]
    · simp
  simp only [Pi.add_apply]
  rw [h1]
  simp only [stepPt, Matrix.mul_apply, Matrix.add_apply, of_apply, mul_add, Finset.sum_add_distrib, Pi.zero_apply,
    dite_eq_ite, ite_self, mul_zero, Finset.sum_const_zero, add_zero]
  ring

theorem det_unip {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
    (u : GL (n ⊕ Fin c) k) (hu : u ∈ symN k n c) : (stepLin n' u.val).det = 1 := by
  apply GlobalTheory.RootExSource.det_eq_one_of_unip (fun a : StepVar n c n' => GlobalTheory.DiagVol.ordL c a.1.1)
  intro a b hab
  have hu' : u.val a.1.1 b.1.1 = (1 : Matrix _ _ k) a.1.1 b.1.1 := GlobalTheory.DiagVol.symN_le_unipSub hu a.1.1 b.1.1 hab
  simp only [stepLin, of_apply]
  by_cases hab' : a = b
  · subst hab'; simp [hu']
  · rw [Matrix.one_apply_ne hab']
    split_ifs with h
    · rw [hu', Matrix.one_apply_ne]
      intro hr
      exact hab' (Subtype.ext (Prod.ext hr h))
    · rfl

theorem var_inl_iff {n n' : Type} {c : ℕ} (r t : n) (s : n' ⊕ Fin (c + 1)) :
    (Free (c / 2 + 1) ((Sum.inl r : n ⊕ Fin c), s) ∨ Kept ((Sum.inl r : n ⊕ Fin c), s)) ↔
      (Free (c / 2 + 1) ((Sum.inl t : n ⊕ Fin c), s) ∨ Kept ((Sum.inl t : n ⊕ Fin c), s)) := by
  rcases s with s | s <;> simp [Free, Kept]

theorem embX_apply_eq_zero {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] {c : ℕ} (κ : GL n k)
    (r t : n ⊕ Fin c) (s : n' ⊕ Fin (c + 1)) (hr : Free (c / 2 + 1) (r, s) ∨ Kept (r, s))
    (ht : ¬ (Free (c / 2 + 1) (t, s) ∨ Kept (t, s))) : (embX c κ).val r t = 0 := by
  change (fromBlocks κ.val 0 0 1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r t = 0
  rcases r with r | r <;> rcases t with t | t
  · exact absurd ((var_inl_iff r t s).1 hr) ht
  · rfl
  · rfl
  · simp only [fromBlocks_apply₂₂]
    rw [Matrix.one_apply_ne]
    rintro rfl
    exact ht hr

theorem mul_embX {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
    (κ : GL n k) (g : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) :
    stepLin n' ((embX c κ).val * g) = stepLin n' (embX c κ).val * stepLin n' g := by
  ext a b
  obtain ⟨⟨r, s⟩, ha⟩ := a
  obtain ⟨⟨r', s'⟩, hb⟩ := b
  set E := (embX c κ).val
  set F : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) → k := fun d =>
    (if s = d.2 then E r d.1 else 0) * (if d.2 = s' then g d.1 r' else 0) with hF
  have hF0 : ∀ d : {d : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // ¬ (Free (c / 2 + 1) d ∨ Kept d)}, F d.1 = 0 := by
    rintro ⟨⟨t, s''⟩, hd⟩
    by_cases h1 : s = s''
    · subst h1
      have hz : E r t = 0 := embX_apply_eq_zero κ r t s ha hd
      simp [hF, hz]
    · simp [hF, h1]
  have hR : (stepLin n' E * stepLin n' g) ⟨(r, s), ha⟩ ⟨(r', s'), hb⟩ = ∑ d, F d := by
    rw [← Fintype.sum_subtype_add_sum_subtype (fun d => Free (c / 2 + 1) d ∨ Kept d),
      Finset.sum_eq_zero (s := Finset.univ) (fun d _ => hF0 d), add_zero]
    simp only [Matrix.mul_apply, stepLin, of_apply, hF]
  rw [hR, Fintype.sum_prod_type, Finset.sum_comm, Finset.sum_eq_single s]
  · simp only [stepLin, of_apply, hF, Matrix.mul_apply]
    split_ifs with h
    · simp
    · simp [h]
  · intro s'' _ hs
    refine Finset.sum_eq_zero fun t _ => ?_
    simp [hF, Ne.symm hs]
  · simp

theorem mp_affine {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι k) (hM : valuation k M.det = 1) (b : ι → k) :
    MeasurePreserving (fun e => M.mulVec e + b) (Measure.pi fun _ : ι => ν) (Measure.pi fun _ : ι => ν) := by
  haveI := GlobalTheory.SplitWeil.secondCountable k
  have hU : IsUnit M.det := isUnit_iff_ne_zero.2 fun h => by rw [h, map_zero] at hM; exact zero_ne_one hM
  have h1 := GlobalTheory.WeilM.smul_map_mulVec_pi ν M hU.unit hU.unit_spec
  have h2 : distribHaarChar k hU.unit = 1 := by
    have := nabs_of_valuation_eq_one (k := k) (x := hU.unit) (by rw [hU.unit_spec]; exact hM)
    exact NNReal.coe_eq_one.1 this
  rw [h2, ENNReal.coe_one, one_smul] at h1
  have hm : Measurable M.mulVec := (continuous_const.matrix_mulVec continuous_id).measurable
  exact (measurePreserving_add_right (Measure.pi fun _ : ι => ν) b).comp ⟨hm, h1⟩

end GlobalTheory.StepLeft

namespace GlobalTheory.StepLeft
open Classical

theorem left_change : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ} (ν : Measure k) [ν.IsAddHaarMeasure],
    ∀ v ∈ symN k n c, ∀ κ : GL n k, valuation k (gdet κ : k) = 1 → ∀ x₀ : Matrix n n' k,
      ∃ φ : (StepVar n c n' → k) ≃ᵐ (StepVar n c n' → k), MeasurePreserving φ (stepVol ν n c n') (stepVol ν n c n') ∧
        ∀ e, ((v * embX c κ)⁻¹).val * stepPt x₀ e = stepPt ((κ⁻¹).val * x₀) (φ e) := by
  intro k _ _ _ _ _ _ n n' _ _ _ _ c ν _ v hv κ hκ x₀
  haveI := GlobalTheory.SplitWeil.secondCountable k
  set g := ((v * embX c κ)⁻¹).val with hgdef
  set M := stepLin n' g with hMdef
  set b : StepVar n c n' → k := fun a =>
    (g * stepPt x₀ (0 : StepVar n c n' → k) : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) a.1.1 a.1.2 with hb
  have hg : g = (embX c κ⁻¹).val * (v⁻¹).val := by
    rw [hgdef, _root_.mul_inv_rev, map_inv, Units.val_mul]
  have hκ' : valuation k (gdet κ⁻¹ : k) = 1 := by
    rw [gdet, map_inv, Units.val_inv_eq_inv_val, map_inv₀]
    exact (congrArg (·⁻¹) hκ).trans inv_one
  have hdet : valuation k M.det = 1 := by
    rw [hMdef, hg, mul_embX, det_mul, map_mul, det_unip _ (inv_mem hv), map_one, mul_one]
    exact GlobalTheory.T.valuation_det_stageVariables_embedGL_eq_one (n' := n') (c := c) κ⁻¹ hκ'
  have hM0 : IsUnit M.det := isUnit_iff_ne_zero.2 fun h => by rw [h, map_zero] at hdet; exact zero_ne_one hdet
  have hcont : ∀ (A : Matrix (StepVar n c n') (StepVar n c n') k) (w : StepVar n c n' → k),
      Continuous fun e : StepVar n c n' → k => A.mulVec e + w := fun A w =>
    (continuous_const.matrix_mulVec continuous_id).add continuous_const
  let φ : (StepVar n c n' → k) ≃ᵐ (StepVar n c n' → k) :=
    { toFun := fun e => M.mulVec e + b
      invFun := fun e => M⁻¹.mulVec e + M⁻¹.mulVec (-b)
      left_inv := fun e => by
        simp only [mulVec_add, mulVec_mulVec, nonsing_inv_mul _ hM0, one_mulVec, mulVec_neg, add_neg_cancel_right]
      right_inv := fun e => by
        simp only [mulVec_add, mulVec_mulVec, mul_nonsing_inv _ hM0, one_mulVec, mulVec_neg, neg_add_cancel_right]
      measurable_toFun := (hcont M b).measurable
      measurable_invFun := (hcont M⁻¹ _).measurable }
  refine ⟨φ, mp_affine ν M hdet b, fun e => ?_⟩
  change g * stepPt x₀ e = stepPt ((κ⁻¹).val * x₀) (M.mulVec e + b)
  rw [hMdef, hb, ← affine]
  exact GlobalTheory.T.periodStep_inv_mul_point_shape v hv κ x₀ e

end GlobalTheory.StepLeft

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierJacobiStep_leftChange_measurePreserving : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ} (ν : Measure k) [ν.IsAddHaarMeasure],
    ∀ v ∈ symN k n c, ∀ κ : GL n k, valuation k (gdet κ : k) = 1 → ∀ x₀ : Matrix n n' k,
      ∃ φ : (StepVar n c n' → k) ≃ᵐ (StepVar n c n' → k), MeasurePreserving φ (stepVol ν n c n') (stepVol ν n c n') ∧
        ∀ e, ((v * embX c κ)⁻¹).val * stepPt x₀ e = stepPt ((κ⁻¹).val * x₀) (φ e) := by
  atlas_forward_decl GlobalTheory.StepLeft.left_change
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

noncomputable section

namespace GlobalTheory.TopLevelInv
namespace StepMove

section Alg

variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

open Classical in

def varPart (e : StepVar n c n' → k) : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k :=
  Matrix.of fun r s => if h : Free (c / 2 + 1) (r, s) ∨ Kept (r, s) then e ⟨(r, s), h⟩ else 0

omit [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] in
theorem stepPt_eq_add (x₀ : Matrix n n' k) (e : StepVar n c n' → k) : stepPt x₀ e = basePt c x₀ + varPart e := rfl

omit [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] in
theorem varPart_var (e : StepVar n c n' → k) (a : StepVar n c n') : varPart e a.1.1 a.1.2 = e a := by
  simp [varPart, a.2]

omit [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] in
theorem varPart_nonvar (e : StepVar n c n' → k) {r : n ⊕ Fin c} {s : n' ⊕ Fin (c + 1)}
    (h : ¬ (Free (c / 2 + 1) (r, s) ∨ Kept (r, s))) : varPart e r s = 0 := by
  simp [varPart, h]

omit [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] in

theorem basePt_var (x₀ : Matrix n n' k) {r : n ⊕ Fin c} {s : n' ⊕ Fin (c + 1)}
    (h : Free (c / 2 + 1) (r, s) ∨ Kept (r, s)) : basePt c x₀ r s = 0 := by
  rcases r with r | r <;> rcases s with s | s <;> simp [Free, Kept, basePt] at h ⊢
  all_goals omega

omit [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] in

theorem eq_stepPt_of (x₀ : Matrix n n' k) (Y : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)
    (h : ∀ r s, ¬ (Free (c / 2 + 1) (r, s) ∨ Kept (r, s)) → Y r s = basePt c x₀ r s) :
    Y = stepPt x₀ (fun a => Y a.1.1 a.1.2) := by
  ext r s
  by_cases hv : Free (c / 2 + 1) (r, s) ∨ Kept (r, s)
  · rw [stepPt_eq_add, Matrix.add_apply, basePt_var x₀ hv, zero_add]
    exact (varPart_var (fun a => Y a.1.1 a.1.2) ⟨(r, s), hv⟩).symm
  · rw [stepPt_eq_add, Matrix.add_apply, varPart_nonvar _ hv, add_zero, h r s hv]

def linV (g : Matrix (n' ⊕ Fin (c + 1)) (n' ⊕ Fin (c + 1)) k) : Matrix (StepVar n c n') (StepVar n c n') k :=
  Matrix.of fun a b => if b.1.1 = a.1.1 then g b.1.2 a.1.2 else 0

open Classical in
theorem varPart_mul_apply (e : StepVar n c n' → k) (g : Matrix (n' ⊕ Fin (c + 1)) (n' ⊕ Fin (c + 1)) k)
    (a : StepVar n c n') : (varPart e * g) a.1.1 a.1.2 = (linV g).mulVec e a := by
  have h1 : (linV g).mulVec e a = ∑ b : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)),
      (if b.1 = a.1.1 then g b.2 a.1.2 else 0) * varPart e b.1 b.2 := by
    rw [← Fintype.sum_subtype_add_sum_subtype (fun b => Free (c / 2 + 1) b ∨ Kept b)]
    rw [Finset.sum_eq_zero (s := Finset.univ) (f := fun b : {b // ¬ (Free (c / 2 + 1) b ∨ Kept b)} => _)
      (fun b _ => by rw [varPart_nonvar _ b.2, mul_zero]), add_zero]
    simp only [Matrix.mulVec, dotProduct, linV, of_apply]
    exact Finset.sum_congr rfl fun b _ => by rw [varPart_var]
  rw [h1, Fintype.sum_prod_type, Finset.sum_eq_single a.1.1]
  · simp [Matrix.mul_apply, mul_comm]
  · intro r' _ hr
    simp [hr]
  · simp

open Classical in

theorem det_linV {q : ℕ} {g : GL (n' ⊕ Fin (c + 1)) k} (hg : InN q g) : (linV (n := n) g.val).det = 1 := by
  rw [← det_transpose]
  refine GlobalTheory.RootExSource.det_eq_one_of_unip (fun a => lev q a.1.2) _ fun a b hab => ?_
  rcases a with ⟨⟨r, s⟩, ha⟩
  rcases b with ⟨⟨r', s'⟩, hb⟩
  simp only [linV, transpose_apply, of_apply]
  rw [hg _ _ hab]
  by_cases h1 : r = r' <;> by_cases h2 : s = s' <;> simp [Matrix.one_apply, h1, h2]

omit [Fintype n] [DecidableEq n] in

theorem mul_gen_nonvar {q : ℕ} (hq : q = c / 2 + 1 ∨ (c % 2 = 1 ∧ q = c / 2 + 2)) {g : GL (n' ⊕ Fin (c + 1)) k}
    (hg : InN q g) (x₀ : Matrix n n' k) (e : StepVar n c n' → k) (r : n ⊕ Fin c) (s : n' ⊕ Fin (c + 1))
    (hv : ¬ (Free (c / 2 + 1) (r, s) ∨ Kept (r, s))) : (stepPt x₀ e * g.val) r s = basePt c x₀ r s := by
  rw [GlobalTheory.RootExSource.mul_apply_of_inN hg, stepPt_eq_add, Matrix.add_apply, varPart_nonvar _ hv, add_zero,
    Finset.sum_eq_zero, add_zero]
  intro s' _
  split_ifs with h'
  · have : ¬ (Free (c / 2 + 1) (r, s') ∨ Kept (r, s')) ∧ basePt c x₀ r s' = 0 := by
      rcases r with r | r <;> rcases s with s | s <;> rcases s' with s' | s' <;>
        simp [Free, Kept, GlobalTheory.RootEx.lev, basePt, Nat.even_iff, Nat.odd_iff, Fin.ext_iff] at hv h' ⊢ <;> omega
    rw [Matrix.add_apply, varPart_nonvar _ this.1, this.2, add_zero, zero_mul]
  · rfl

end Alg

section Meas

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]

theorem exists_affine_mp {ι : Type} [Fintype ι] [DecidableEq ι] (ν : Measure k) [ν.IsAddHaarMeasure]
    (M : Matrix ι ι k) (u : kˣ) (hu : (u : k) = M.det) (hv : valuation k (u : k) = 1) (b : ι → k) :
    ∃ φ : (ι → k) ≃ᵐ (ι → k), MeasurePreserving φ (Measure.pi fun _ => ν) (Measure.pi fun _ => ν) ∧
      ∀ e, φ e = M.mulVec e + b := by
  haveI := GlobalTheory.SplitWeil.secondCountable k
  have hm : ∀ A : Matrix ι ι k, Measurable A.mulVec := fun A =>
    (continuous_const.matrix_mulVec continuous_id).measurable
  have hdet : IsUnit M.det := hu ▸ u.isUnit
  let φ : (ι → k) ≃ᵐ (ι → k) :=
    { toFun := fun e => M.mulVec e + b
      invFun := fun e => M⁻¹.mulVec (e - b)
      left_inv := fun e => by simp [mulVec_mulVec, nonsing_inv_mul _ hdet]
      right_inv := fun e => by simp [mulVec_mulVec, mul_nonsing_inv _ hdet]
      measurable_toFun := (hm M).add_const b
      measurable_invFun := (hm _).comp (measurable_id.sub_const b) }
  refine ⟨φ, ⟨φ.measurable, ?_⟩, fun e => rfl⟩
  have h1 : distribHaarChar k u = 1 := by
    have := GlobalTheory.SplitWeil.nabs_eq_one_of_valuation_eq_one hv
    unfold nabs at this
    exact_mod_cast this
  have h2 := GlobalTheory.WeilM.smul_map_mulVec_pi ν M u hu
  rw [h1, ENNReal.coe_one, one_smul] at h2
  have e1 : (φ : (ι → k) → (ι → k)) = (fun e => b + e) ∘ M.mulVec := by
    funext e; exact add_comm _ _
  rw [e1, ← Measure.map_map (measurable_const_add b) (hm M), h2]
  exact map_add_left_eq_self _ b

theorem exists_blocks_mp {F m J : Type} [Fintype F] [Fintype m] [DecidableEq m] [Fintype J]
    (ν : Measure k) [ν.IsAddHaarMeasure] (ι : m × J → F) (hι : Function.Injective ι)
    (A : Matrix m m k) (u : kˣ) (hu : A.det = u) (hv : valuation k (u : k) = 1) (T : (F → k) → (F → k))
    (h1 : ∀ e r j, T e (ι (r, j)) = ∑ s, A r s * e (ι (s, j)))
    (h2 : ∀ e f, f ∉ Set.range ι → T e f = e f) :
    ∃ φ : (F → k) ≃ᵐ (F → k), MeasurePreserving φ (Measure.pi fun _ => ν) (Measure.pi fun _ => ν) ∧
      ∀ e, φ e = T e := by
  classical
  let σ : (m × J) ⊕ {f // f ∉ Set.range ι} ≃ F :=
    (Equiv.sumCongr (Equiv.ofInjective ι hι) (Equiv.refl _)).trans (Equiv.sumCompl (· ∈ Set.range ι))
  have σl : ∀ x, σ (Sum.inl x) = ι x := fun x => rfl
  have σr : ∀ x, σ (Sum.inr x) = x.1 := fun x => rfl
  let G : Matrix F F k := Matrix.reindex σ σ (fromBlocks (blockDiagonal fun _ : J => A) 0 0 1)
  have hG : G.det = (u ^ Fintype.card J : kˣ) := by
    simp [G, det_blockDiagonal, hu]
  have hT : ∀ e, T e = G.mulVec e := by
    intro e
    funext x
    obtain ⟨y, rfl⟩ := σ.surjective x
    rw [Matrix.mulVec, dotProduct, ← σ.sum_comp]
    rcases y with ⟨r, j⟩ | y
    · have : σ.symm (ι (r, j)) = Sum.inl (r, j) := by rw [← σl]; simp
      simp [G, this, σl, σr, h1, Fintype.sum_sum_type, Fintype.sum_prod_type, blockDiagonal_apply]
    · rw [σr, h2 _ _ y.2]
      have : σ.symm y.1 = Sum.inr y := by rw [← σr]; simp
      simp [G, this, Fintype.sum_sum_type, Matrix.one_apply, σr]
  obtain ⟨φ, hφ, hφe⟩ := exists_affine_mp ν G (u ^ Fintype.card J) hG.symm
    (by rw [Units.val_pow_eq_pow_val, map_pow, hv, one_pow]) 0
  exact ⟨φ, hφ, fun e => by rw [hφe, add_zero, hT]⟩

end Meas

section Step

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure]
  (n : Type) [Fintype n] [DecidableEq n] (c : ℕ) (n' : Type) [Fintype n'] [DecidableEq n']

def movers : Subgroup (GL (n' ⊕ Fin (c + 1)) k) where
  carrier := {g | ∀ x₀ : Matrix n n' k, ∃ φ : (StepVar n c n' → k) ≃ᵐ (StepVar n c n' → k),
    MeasurePreserving φ (stepVol ν n c n') (stepVol ν n c n') ∧ ∀ e, stepPt x₀ e * g.val = stepPt x₀ (φ e)}
  one_mem' x₀ := ⟨MeasurableEquiv.refl _, MeasurePreserving.id _, fun e => by simp⟩
  mul_mem' {g h} hg hh x₀ := by
    obtain ⟨φ, hφ, hφe⟩ := hg x₀
    obtain ⟨χ, hχ, hχe⟩ := hh x₀
    exact ⟨φ.trans χ, hχ.comp hφ, fun e => by
      rw [Units.val_mul, ← Matrix.mul_assoc, hφe, hχe]; rfl⟩
  inv_mem' {g} hg x₀ := by
    obtain ⟨φ, hφ, hφe⟩ := hg x₀
    refine ⟨φ.symm, hφ.symm φ, fun e => ?_⟩
    conv_lhs => rw [← φ.apply_symm_apply e, ← hφe]
    rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

variable {ν n c n'}

open Classical in
theorem mem_movers_of_inN {q : ℕ} (hq : q = c / 2 + 1 ∨ (c % 2 = 1 ∧ q = c / 2 + 2))
    {g : GL (n' ⊕ Fin (c + 1)) k} (hg : InN q g) : g ∈ movers ν n c n' := by
  intro x₀
  obtain ⟨φ, hφ, hφe⟩ := exists_affine_mp ν (linV (n := n) g.val) 1 (by rw [det_linV hg]; rfl)
    (by simp) (fun a => (basePt c x₀ * g.val) a.1.1 a.1.2)
  refine ⟨φ, hφ, fun e => ?_⟩
  rw [eq_stepPt_of x₀ (stepPt x₀ e * g.val) (mul_gen_nonvar hq hg x₀ e)]
  congr 1
  funext a
  rw [hφe, stepPt_eq_add, Matrix.add_mul, Matrix.add_apply, varPart_mul_apply, Pi.add_apply, add_comm]

theorem symN_le_movers : symN k n' (c + 1) ≤ movers ν n c n' := by
  refine sup_le ((Subgroup.closure_le _).2 fun g hg => mem_movers_of_inN ?_ hg)
    ((Subgroup.closure_le _).2 fun g hg => mem_movers_of_inN ?_ hg)
  · omega
  · omega

open Classical in

theorem exists_embX_mp (κ : GL n' k) (hκ : valuation k (gdet κ : k) = 1) (x₀ : Matrix n n' k) :
    ∃ φ : (StepVar n c n' → k) ≃ᵐ (StepVar n c n' → k), MeasurePreserving φ (stepVol ν n c n') (stepVol ν n c n') ∧
      ∀ e, stepPt x₀ e * (embX (c + 1) κ).val = stepPt (x₀ * κ.val) (φ e) := by
  have hgv : (embX (c + 1) κ).val = fromBlocks κ.val 0 0 1 := rfl
  let ι : n' × {l : Fin c // l.val + 1 < c / 2 + 1 ∨ (Odd c ∧ l.val = c / 2)} → StepVar n c n' :=
    fun x => ⟨(Sum.inr x.2.1, Sum.inl x.1), x.2.2⟩
  have hι : Function.Injective ι := by
    rintro ⟨a, b, hb⟩ ⟨a', b', hb'⟩ h
    have h' := congrArg Subtype.val h
    simp only [ι, Prod.mk.injEq, Sum.inl.injEq, Sum.inr.injEq] at h'
    obtain ⟨rfl, rfl⟩ := h'
    rfl
  let T : (StepVar n c n' → k) → (StepVar n c n' → k) := fun e a => (varPart e * (embX (c + 1) κ).val) a.1.1 a.1.2
  obtain ⟨φ, hφ, hφe⟩ := exists_blocks_mp ν ι hι κ.valᵀ (gdet κ) (by rw [det_transpose]; rfl) hκ T
    (fun e r j => by
      simp only [T, ι, hgv, GlobalTheory.RootEx.OpELevi.right_inl]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [varPart_var e ⟨(Sum.inr j.1, Sum.inl t), j.2⟩])
    (fun e f hf => by
      rcases f with ⟨⟨r, s | s⟩, hrs⟩
      · rcases r with r | r
        · exact (hrs.elim (fun h => h.elim) (fun h => h.elim))
        · exact (hf ⟨(s, ⟨r, hrs⟩), rfl⟩).elim
      · simp only [T, hgv, GlobalTheory.RootEx.OpELevi.right_inr]
        exact varPart_var e ⟨(r, Sum.inr s), hrs⟩)
  refine ⟨φ, hφ, fun e => ?_⟩
  have hb : basePt c x₀ * (embX (c + 1) κ).val = basePt c (x₀ * κ.val) := by
    simp [hgv, basePt, fromBlocks_multiply]
  have hnv : ∀ r s, ¬ (Free (c / 2 + 1) (r, s) ∨ Kept (r, s)) → (varPart e * (embX (c + 1) κ).val) r s = 0 := by
    intro r s hv
    rcases s with s | s
    · rw [hgv, GlobalTheory.RootEx.OpELevi.right_inl]
      refine Finset.sum_eq_zero fun t _ => ?_
      rw [varPart_nonvar, mul_zero]
      rcases r with r | r
      · exact hv
      · exact hv
    · rw [hgv, GlobalTheory.RootEx.OpELevi.right_inr, varPart_nonvar _ hv]
  rw [eq_stepPt_of (x₀ * κ.val) (stepPt x₀ e * (embX (c + 1) κ).val) (fun r s hv => by
    rw [stepPt_eq_add, Matrix.add_mul, Matrix.add_apply, hb, hnv r s hv, add_zero])]
  congr 1
  funext a
  rw [hφe, stepPt_eq_add, Matrix.add_mul, Matrix.add_apply, hb, basePt_var _ a.2, zero_add]

end Step

end StepMove

theorem stepPt_mul_symN_embX : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ} (ν : Measure k) [ν.IsAddHaarMeasure],
    ∀ v ∈ symN k n' (c + 1), ∀ κ : GL n' k, valuation k (gdet κ : k) = 1 → ∀ x₀ : Matrix n n' k,
      ∃ φ : (StepVar n c n' → k) ≃ᵐ (StepVar n c n' → k), MeasurePreserving φ (stepVol ν n c n') (stepVol ν n c n') ∧
        ∀ e, stepPt x₀ e * (v * embX (c + 1) κ).val = stepPt (x₀ * κ.val) (φ e) := by
  intro k _ _ _ _ _ _ n n' _ _ _ _ c ν _ v hv κ hκ x₀
  obtain ⟨φ, hφ, hφe⟩ := StepMove.symN_le_movers (ν := ν) (n := n) hv x₀
  obtain ⟨χ, hχ, hχe⟩ := StepMove.exists_embX_mp (ν := ν) (c := c) κ hκ x₀
  exact ⟨φ.trans χ, hχ.comp hφ, fun e => by
    rw [Units.val_mul, ← Matrix.mul_assoc, hφe, hχe]; rfl⟩

end GlobalTheory.TopLevelInv
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stepPoint_mul_periodUnipotent_GL_measurePreserving : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ} (ν : Measure k) [ν.IsAddHaarMeasure],
    ∀ v ∈ symN k n' (c + 1), ∀ κ : GL n' k, valuation k (gdet κ : k) = 1 → ∀ x₀ : Matrix n n' k,
      ∃ φ : (StepVar n c n' → k) ≃ᵐ (StepVar n c n' → k), MeasurePreserving φ (stepVol ν n c n') (stepVol ν n c n') ∧
        ∀ e, stepPt x₀ e * (v * embX (c + 1) κ).val = stepPt (x₀ * κ.val) (φ e) := by
  first | exact @GlobalTheory.TopLevelInv.stepPt_mul_symN_embX | exact GlobalTheory.TopLevelInv.stepPt_mul_symN_embX | (intros; apply GlobalTheory.TopLevelInv.stepPt_mul_symN_embX <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

noncomputable section
namespace GlobalTheory.PhaseStep

open GlobalTheory.DiagVol

section Shape
variable {k : Type} [Field k] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem mul_apply_of_shape {β : Type} {ℓ : ι → ℕ} {M : Matrix ι ι k}
    (hM : ∀ r s, ℓ s ≤ ℓ r → M r s = (1 : Matrix ι ι k) r s) (D : Matrix ι β k) (r : ι) (s : β) :
    (M * D) r s = D r s + ∑ t, if ℓ r < ℓ t then M r t * D t s else 0 := by
  rw [Matrix.mul_apply]
  have h : ∀ t, M r t * D t s = (if t = r then D t s else 0) + (if ℓ r < ℓ t then M r t * D t s else 0) := by
    intro t
    by_cases ht : ℓ r < ℓ t
    · have : t ≠ r := by rintro rfl; exact lt_irrefl _ ht
      simp [ht, this]
    · rw [hM r t (by omega), if_neg ht, add_zero]
      by_cases htr : t = r
      · subst htr; simp
      · rw [Matrix.one_apply_ne (Ne.symm htr), if_neg htr, zero_mul]
  rw [Finset.sum_congr rfl fun t _ => h t, Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp

theorem apply_mul_of_shape {α : Type} {ℓ : ι → ℕ} {M : Matrix ι ι k}
    (hM : ∀ r s, ℓ s ≤ ℓ r → M r s = (1 : Matrix ι ι k) r s) (D : Matrix α ι k) (r : α) (s : ι) :
    (D * M) r s = D r s + ∑ t, if ℓ t < ℓ s then D r t * M t s else 0 := by
  rw [Matrix.mul_apply]
  have h : ∀ t, D r t * M t s = (if t = s then D r t else 0) + (if ℓ t < ℓ s then D r t * M t s else 0) := by
    intro t
    by_cases ht : ℓ t < ℓ s
    · have : t ≠ s := by rintro rfl; exact lt_irrefl _ ht
      simp [ht, this]
    · rw [hM t s (by omega), if_neg ht, add_zero]
      by_cases htr : t = s
      · subst htr; simp
      · rw [Matrix.one_apply_ne htr, if_neg htr, mul_zero]
  rw [Finset.sum_congr rfl fun t _ => h t, Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp

end Shape

section Step
variable {k : Type} [Field k] {n n' : Type} {c : ℕ}

theorem stepPt_rr_lt (x₀ : Matrix n n' k) (e : StepVar n c n' → k) (l : Fin c) (i : Fin (c + 1))
    (h : i.val < l.val) : stepPt x₀ e (.inr l) (.inr i) = 0 := by
  have h1 : ¬ (Free (c / 2 + 1) ((Sum.inr l : n ⊕ Fin c), (Sum.inr i : n' ⊕ Fin (c + 1))) ∨
      Kept ((Sum.inr l : n ⊕ Fin c), (Sum.inr i : n' ⊕ Fin (c + 1)))) := by
    simp only [Free, Kept, or_false]; omega
  rw [stepPt, Matrix.add_apply, Matrix.of_apply, dif_neg h1, add_zero, basePt, fromBlocks_apply₂₂,
    Matrix.of_apply, if_neg (by omega)]

theorem stepPt_rr_eq (x₀ : Matrix n n' k) (e : StepVar n c n' → k) (l : Fin c) (i : Fin (c + 1))
    (h : l.val = i.val) : stepPt x₀ e (.inr l) (.inr i) = 1 := by
  have h1 : ¬ (Free (c / 2 + 1) ((Sum.inr l : n ⊕ Fin c), (Sum.inr i : n' ⊕ Fin (c + 1))) ∨
      Kept ((Sum.inr l : n ⊕ Fin c), (Sum.inr i : n' ⊕ Fin (c + 1)))) := by
    simp only [Free, Kept, or_false]; omega
  rw [stepPt, Matrix.add_apply, Matrix.of_apply, dif_neg h1, add_zero, basePt, fromBlocks_apply₂₂,
    Matrix.of_apply, if_pos h]

theorem stepPt_lr_zero (x₀ : Matrix n n' k) (e : StepVar n c n' → k) (r : n) (i : Fin (c + 1))
    (h : i.val < c / 2 ∨ (i.val = c / 2 ∧ c % 2 = 1)) : stepPt x₀ e (.inl r) (.inr i) = 0 := by
  have h1 : ¬ (Free (c / 2 + 1) ((Sum.inl r : n ⊕ Fin c), (Sum.inr i : n' ⊕ Fin (c + 1))) ∨
      Kept ((Sum.inl r : n ⊕ Fin c), (Sum.inr i : n' ⊕ Fin (c + 1)))) := by
    simp only [Free, Kept, Nat.even_iff]; omega
  rw [stepPt, Matrix.add_apply, Matrix.of_apply, dif_neg h1, add_zero, basePt, fromBlocks_apply₁₂,
    Matrix.zero_apply]

theorem stepPt_rl_zero (x₀ : Matrix n n' k) (e : StepVar n c n' → k) (l : Fin c) (s : n')
    (h : c / 2 < l.val ∨ (l.val = c / 2 ∧ c % 2 = 0)) : stepPt x₀ e (.inr l) (.inl s) = 0 := by
  have h1 : ¬ (Free (c / 2 + 1) ((Sum.inr l : n ⊕ Fin c), (Sum.inl s : n' ⊕ Fin (c + 1))) ∨
      Kept ((Sum.inr l : n ⊕ Fin c), (Sum.inl s : n' ⊕ Fin (c + 1)))) := by
    simp only [Free, Kept, Nat.odd_iff]; omega
  rw [stepPt, Matrix.add_apply, Matrix.of_apply, dif_neg h1, add_zero, basePt, fromBlocks_apply₂₁,
    Matrix.zero_apply]

end Step

section Ch
variable {k : Type} [Field k] {n n₀ n₂ : Type} [Fintype n₀] [DecidableEq n₀] [Fintype n] [DecidableEq n]
  [Fintype n₂] [DecidableEq n₂] {c : ℕ}

theorem sum_succ_eq (f : Fin (c + 1) → Fin (c + 1) → k) :
    (∑ i : Fin (c + 1), ∑ j : Fin (c + 1), if j.val = i.val + 1 then f i j else 0) =
      ∑ l : Fin c, f l.castSucc l.succ := by
  rw [Fin.sum_univ_castSucc]
  have h0 : (∑ j : Fin (c + 1), if j.val = (Fin.last c).val + 1 then f (Fin.last c) j else 0) = 0 :=
    Finset.sum_eq_zero fun j _ => if_neg (by simp; omega)
  rw [h0, add_zero]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_eq_single l.succ]
  · rw [if_pos (by simp)]
  · intro j _ hj; rw [if_neg]; intro h; exact hj (Fin.ext (by simp at h ⊢; omega))
  · simp

theorem ch_shape_mul {M : Matrix (n ⊕ Fin (c + 1)) (n ⊕ Fin (c + 1)) k}
    (hM : ∀ r s, ordL (c + 1) s ≤ ordL (c + 1) r → M r s = (1 : Matrix _ _ k) r s)
    (x₀ : Matrix n n₀ k) (e₀ : StepVar n (c + 1) n₀ → k) :
    ch (M * stepPt x₀ e₀) = ch (stepPt x₀ e₀) + ∑ l : Fin c, M (.inr l.castSucc) (.inr l.succ) +
      ∑ i : Fin (c + 1), if 2 * i.val + 1 = c then
        ∑ x, M (.inr i) (.inl x) * stepPt x₀ e₀ (.inl x) (.inr i.succ) else 0 := by
  unfold ch
  rw [Finset.sum_congr rfl fun i _ => mul_apply_of_shape hM (stepPt x₀ e₀) _ _, Finset.sum_add_distrib]
  refine Eq.trans (congrArg (_ + ·) ?_) (add_assoc _ _ _).symm
  have key : ∀ i : Fin (c + 1), (∑ t : n ⊕ Fin (c + 1), if ordL (c + 1) (Sum.inr i : n ⊕ Fin (c + 1)) < ordL (c + 1) t then
      M (.inr i) t * stepPt x₀ e₀ t (.inr i.succ) else 0) =
      (∑ j : Fin (c + 1), if j.val = i.val + 1 then M (.inr i) (.inr j) else 0) +
      (if 2 * i.val + 1 = c then ∑ x, M (.inr i) (.inl x) * stepPt x₀ e₀ (.inl x) (.inr i.succ) else 0) := by
    intro i
    rw [Fintype.sum_sum_type, add_comm]
    congr 1
    · refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hj : j.val = i.val + 1
      · rw [if_pos (by simp [ordL]; omega), if_pos hj, stepPt_rr_eq _ _ _ _ (by simp [hj]), mul_one]
      · rw [if_neg hj]
        split_ifs with h
        · rw [stepPt_rr_lt _ _ _ _ (by simp [ordL] at h; simp; omega), mul_zero]
        · rfl
    · by_cases hc : 2 * i.val + 1 = c
      · rw [if_pos hc]
        exact Finset.sum_congr rfl fun x _ => if_pos (by simp [ordL]; omega)
      · rw [if_neg hc]
        refine Finset.sum_eq_zero fun x _ => ?_
        split_ifs with h
        · rw [stepPt_lr_zero _ _ _ _ (by simp [ordL] at h; simp; omega), mul_zero]
        · rfl
  rw [Finset.sum_congr rfl fun i _ => key i, Finset.sum_add_distrib, sum_succ_eq]

theorem ch_mul_shape {M : Matrix (n ⊕ Fin (c + 1)) (n ⊕ Fin (c + 1)) k}
    (hM : ∀ r s, ordL (c + 1) s ≤ ordL (c + 1) r → M r s = (1 : Matrix _ _ k) r s)
    (x₁ : Matrix n₂ n k) (e₁ : StepVar n₂ c n → k) :
    ch (stepPt x₁ e₁ * M) = ch (stepPt x₁ e₁) + ∑ l : Fin c, M (.inr l.castSucc) (.inr l.succ) +
      ∑ l : Fin c, if 2 * l.val + 1 = c then
        ∑ x, stepPt x₁ e₁ (.inr l) (.inl x) * M (.inl x) (.inr l.succ) else 0 := by
  unfold ch
  rw [Finset.sum_congr rfl fun i _ => apply_mul_of_shape hM (stepPt x₁ e₁) _ _, Finset.sum_add_distrib]
  refine Eq.trans (congrArg (_ + ·) ?_) (add_assoc _ _ _).symm
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Fintype.sum_sum_type, add_comm]
  congr 1
  · rw [Finset.sum_eq_single l.castSucc]
    · rw [if_pos (by simp [ordL]), stepPt_rr_eq _ _ _ _ (by simp), one_mul]
    · intro j _ hj
      split_ifs with h
      · rw [stepPt_rr_lt _ _ _ _ ?_, zero_mul]
        simp [ordL] at h
        have : j.val ≠ l.val := fun h' => hj (Fin.ext (by simp [h']))
        omega
      · rfl
    · simp
  · by_cases hc : 2 * l.val + 1 = c
    · rw [if_pos hc]
      exact Finset.sum_congr rfl fun x _ => if_pos (by simp [ordL]; omega)
    · rw [if_neg hc]
      refine Finset.sum_eq_zero fun x _ => ?_
      split_ifs with h
      · rw [stepPt_rl_zero _ _ _ _ (by simp [ordL] at h; omega), zero_mul]
      · rfl

end Ch

section Rel
variable {k : Type} [Field k] {n n₀ n₂ : Type} [Fintype n₀] [DecidableEq n₀] [Fintype n] [DecidableEq n]
  [Fintype n₂] [DecidableEq n₂] {c : ℕ} {V W : Matrix (n ⊕ Fin (c + 1)) (n ⊕ Fin (c + 1)) k}

theorem simple_rel (hV : ∀ r s, ordL (c + 1) s ≤ ordL (c + 1) r → V r s = (1 : Matrix _ _ k) r s)
    (hW : ∀ r s, ordL (c + 1) s ≤ ordL (c + 1) r → W r s = (1 : Matrix _ _ k) r s) (hVW : V * W = 1) (l : Fin c) :
    V (.inr l.castSucc) (.inr l.succ) + W (.inr l.castSucc) (.inr l.succ) +
      (if 2 * l.val + 1 = c then ∑ x, V (.inr l.castSucc) (.inl x) * W (.inl x) (.inr l.succ) else 0) = 0 := by
  have h := congrFun (congrFun hVW (.inr l.castSucc)) (.inr l.succ)
  rw [mul_apply_of_shape hV W, Matrix.one_apply_ne (by simp [Fin.ext_iff]), Fintype.sum_sum_type] at h
  have h1 : (∑ j : Fin (c + 1), if ordL (c + 1) (Sum.inr l.castSucc : n ⊕ Fin (c + 1)) < ordL (c + 1) (Sum.inr j : n ⊕ Fin (c + 1)) then
      V (.inr l.castSucc) (.inr j) * W (.inr j) (.inr l.succ) else 0) = V (.inr l.castSucc) (.inr l.succ) := by
    rw [Finset.sum_eq_single l.succ]
    · rw [if_pos (by simp [ordL]), hW _ _ le_rfl, Matrix.one_apply_eq, mul_one]
    · intro j _ hj
      split_ifs with hc
      · rw [hW _ _ (by simp [ordL] at hc ⊢; omega), Matrix.one_apply_ne (by simpa using hj), mul_zero]
      · rfl
    · simp
  have h2 : (∑ x : n, if ordL (c + 1) (Sum.inr l.castSucc : n ⊕ Fin (c + 1)) < ordL (c + 1) (Sum.inl x : n ⊕ Fin (c + 1)) then
      V (.inr l.castSucc) (.inl x) * W (.inl x) (.inr l.succ) else 0) =
      (if 2 * l.val + 1 = c then ∑ x, V (.inr l.castSucc) (.inl x) * W (.inl x) (.inr l.succ) else 0) := by
    by_cases hc : 2 * l.val + 1 = c
    · rw [if_pos hc]
      exact Finset.sum_congr rfl fun x _ => if_pos (by simp [ordL]; omega)
    · rw [if_neg hc]
      refine Finset.sum_eq_zero fun x _ => ?_
      split_ifs with h'
      · rw [hW _ _ (by simp [ordL] at h' ⊢; omega), Matrix.one_apply_ne (by simp), mul_zero]
      · rfl
  rw [h1, h2] at h
  linear_combination h

theorem row_rel (hV : ∀ r s, ordL (c + 1) s ≤ ordL (c + 1) r → V r s = (1 : Matrix _ _ k) r s)
    (hW : ∀ r s, ordL (c + 1) s ≤ ordL (c + 1) r → W r s = (1 : Matrix _ _ k) r s) (hVW : V * W = 1)
    (hc : c % 2 = 1) (x : n) :
    V (.inr ⟨c / 2, by omega⟩) (.inl x) + W (.inr ⟨c / 2, by omega⟩) (.inl x) = 0 := by
  have h := congrFun (congrFun hVW (.inr ⟨c / 2, by omega⟩)) (.inl x)
  rw [mul_apply_of_shape hV W, Matrix.one_apply_ne (by simp), Fintype.sum_sum_type] at h
  have h1 : (∑ j : Fin (c + 1), if ordL (c + 1) (Sum.inr ⟨c / 2, by omega⟩ : n ⊕ Fin (c + 1)) < ordL (c + 1) (Sum.inr j : n ⊕ Fin (c + 1)) then
      V (.inr ⟨c / 2, by omega⟩) (.inr j) * W (.inr j) (.inl x) else 0) = 0 := by
    refine Finset.sum_eq_zero fun j _ => ?_
    split_ifs with h'
    · rw [hW _ _ (by simp [ordL] at h' ⊢; omega), Matrix.one_apply_ne (by simp), mul_zero]
    · rfl
  have h2 : (∑ y : n, if ordL (c + 1) (Sum.inr ⟨c / 2, by omega⟩ : n ⊕ Fin (c + 1)) < ordL (c + 1) (Sum.inl y : n ⊕ Fin (c + 1)) then
      V (.inr ⟨c / 2, by omega⟩) (.inl y) * W (.inl y) (.inl x) else 0) = V (.inr ⟨c / 2, by omega⟩) (.inl x) := by
    rw [Finset.sum_eq_single x]
    · rw [if_pos (by simp [ordL]; omega), hW _ _ le_rfl, Matrix.one_apply_eq, mul_one]
    · intro y _ hy
      rw [hW _ _ (by simp [ordL]), Matrix.one_apply_ne (by simpa using hy)]
      simp
    · simp
  rw [h1, h2] at h
  linear_combination h

theorem col_rel (hV : ∀ r s, ordL (c + 1) s ≤ ordL (c + 1) r → V r s = (1 : Matrix _ _ k) r s)
    (hW : ∀ r s, ordL (c + 1) s ≤ ordL (c + 1) r → W r s = (1 : Matrix _ _ k) r s) (hVW : V * W = 1)
    (hc : c % 2 = 1) (x : n) :
    V (.inl x) (.inr ⟨(c + 1) / 2, by omega⟩) + W (.inl x) (.inr ⟨(c + 1) / 2, by omega⟩) = 0 := by
  have h := congrFun (congrFun hVW (.inl x)) (.inr ⟨(c + 1) / 2, by omega⟩)
  rw [mul_apply_of_shape hV W, Matrix.one_apply_ne (by simp), Fintype.sum_sum_type] at h
  have h1 : (∑ j : Fin (c + 1), if ordL (c + 1) (Sum.inl x : n ⊕ Fin (c + 1)) < ordL (c + 1) (Sum.inr j : n ⊕ Fin (c + 1)) then
      V (.inl x) (.inr j) * W (.inr j) (.inr ⟨(c + 1) / 2, by omega⟩) else 0) = V (.inl x) (.inr ⟨(c + 1) / 2, by omega⟩) := by
    rw [Finset.sum_eq_single ⟨(c + 1) / 2, by omega⟩]
    · rw [if_pos (by simp [ordL]; omega), hW _ _ le_rfl, Matrix.one_apply_eq, mul_one]
    · intro j _ hj
      split_ifs with h'
      · rw [hW _ _ (by simp [ordL] at h' ⊢; omega), Matrix.one_apply_ne (by simpa using hj), mul_zero]
      · rfl
    · simp
  have h2 : (∑ y : n, if ordL (c + 1) (Sum.inl x : n ⊕ Fin (c + 1)) < ordL (c + 1) (Sum.inl y : n ⊕ Fin (c + 1)) then
      V (.inl x) (.inl y) * W (.inl y) (.inr ⟨(c + 1) / 2, by omega⟩) else 0) = 0 :=
    Finset.sum_eq_zero fun y _ => if_neg (by simp [ordL])
  rw [h1, h2] at h
  linear_combination h

theorem pair_right (hV : ∀ r s, ordL (c + 1) s ≤ ordL (c + 1) r → V r s = (1 : Matrix _ _ k) r s)
    (hc : c % 2 = 1) (x₁ : Matrix n₂ n k) (e₁ : StepVar n₂ c n → k) (x : n) :
    (stepPt x₁ e₁ * V) (.inr ⟨c / 2, by omega⟩) (.inl x) =
      stepPt x₁ e₁ (.inr ⟨c / 2, by omega⟩) (.inl x) + V (.inr ⟨c / 2, by omega⟩) (.inl x) := by
  rw [apply_mul_of_shape hV, Fintype.sum_sum_type]
  congr 1
  rw [Finset.sum_eq_zero fun y _ => if_neg (by simp [ordL]), zero_add, Finset.sum_eq_single ⟨c / 2, by omega⟩]
  · rw [if_pos (by simp [ordL]; omega), stepPt_rr_eq _ _ _ _ rfl, one_mul]
  · intro j _ hj
    split_ifs with h'
    · rw [stepPt_rr_lt _ _ _ _ ?_, zero_mul]
      simp [ordL] at h'
      have : j.val ≠ c / 2 := fun h => hj (Fin.ext h)
      simp
      omega
    · rfl
  · simp

theorem pair_left (hW : ∀ r s, ordL (c + 1) s ≤ ordL (c + 1) r → W r s = (1 : Matrix _ _ k) r s)
    (hc : c % 2 = 1) (x₀ : Matrix n n₀ k) (e₀ : StepVar n (c + 1) n₀ → k) (x : n) :
    (W * stepPt x₀ e₀) (.inl x) (.inr ⟨(c + 1) / 2, by omega⟩) =
      stepPt x₀ e₀ (.inl x) (.inr ⟨(c + 1) / 2, by omega⟩) + W (.inl x) (.inr ⟨(c + 1) / 2, by omega⟩) := by
  rw [mul_apply_of_shape hW, Fintype.sum_sum_type]
  congr 1
  rw [Finset.sum_eq_zero fun y _ => if_neg (by simp [ordL]), zero_add, Finset.sum_eq_single ⟨(c + 1) / 2, by omega⟩]
  · rw [if_pos (by simp [ordL]; omega), stepPt_rr_eq _ _ _ _ rfl, mul_one]
  · intro j _ hj
    split_ifs with h'
    · rw [stepPt_rr_lt _ _ _ _ ?_, mul_zero]
      simp [ordL] at h'
      have : j.val ≠ (c + 1) / 2 := fun h => hj (Fin.ext h)
      simp
      omega
    · rfl
  · simp

theorem row_left (hW : ∀ r s, ordL (c + 1) s ≤ ordL (c + 1) r → W r s = (1 : Matrix _ _ k) r s)
    (hc : c % 2 = 0) (x₀ : Matrix n n₀ k) (e₀ : StepVar n (c + 1) n₀ → k) (s : n₀) :
    (W * stepPt x₀ e₀) (.inr ⟨(c + 1) / 2, by omega⟩) (.inl s) = stepPt x₀ e₀ (.inr ⟨(c + 1) / 2, by omega⟩) (.inl s) := by
  rw [mul_apply_of_shape hW, Fintype.sum_sum_type,
    Finset.sum_eq_zero fun y _ => if_neg (by simp [ordL]; omega), zero_add]
  rw [Finset.sum_eq_zero, add_zero]
  intro j _
  split_ifs with h'
  · rw [stepPt_rl_zero _ _ _ _ (by simp [ordL] at h'; omega), mul_zero]
  · rfl

theorem row_right (hV : ∀ r s, ordL (c + 1) s ≤ ordL (c + 1) r → V r s = (1 : Matrix _ _ k) r s)
    (hc : c % 2 = 0) (x₁ : Matrix n₂ n k) (e₁ : StepVar n₂ c n → k) (r : n₂) :
    (stepPt x₁ e₁ * V) (.inl r) (.inr ⟨c / 2, by omega⟩) = stepPt x₁ e₁ (.inl r) (.inr ⟨c / 2, by omega⟩) := by
  rw [apply_mul_of_shape hV, Fintype.sum_sum_type,
    Finset.sum_eq_zero fun y _ => if_neg (by simp [ordL]; omega), zero_add]
  rw [Finset.sum_eq_zero, add_zero]
  intro j _
  split_ifs with h'
  · rw [stepPt_lr_zero _ _ _ _ (by simp [ordL] at h'; omega), zero_mul]
  · rfl

end Rel

section GlobalTheory
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {m : ℕ}

theorem blk_mul_inr {β : Type} (P : Matrix n n k) (M : Matrix (n ⊕ Fin m) β k) (i : Fin m) (s : β) :
    ((fromBlocks P 0 0 1 : Matrix (n ⊕ Fin m) (n ⊕ Fin m) k) * M) (.inr i) s = M (.inr i) s := by
  simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

theorem mul_blk_inr {α : Type} (P : Matrix n n k) (M : Matrix α (n ⊕ Fin m) k) (r : α) (j : Fin m) :
    (M * (fromBlocks P 0 0 1 : Matrix (n ⊕ Fin m) (n ⊕ Fin m) k)) r (.inr j) = M r (.inr j) := by
  simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

theorem pair_blk {α β : Type} (K K' : Matrix n n k) (hK : K * K' = 1) (A : Matrix α (n ⊕ Fin m) k)
    (B : Matrix (n ⊕ Fin m) β k) (a : α) (b : β) :
    ∑ r, (A * (fromBlocks K 0 0 1 : Matrix (n ⊕ Fin m) (n ⊕ Fin m) k)) a (.inl r) *
      ((fromBlocks K' 0 0 1 : Matrix (n ⊕ Fin m) (n ⊕ Fin m) k) * B) (.inl r) b =
      ∑ r, A a (.inl r) * B (.inl r) b := by
  have hE : (fromBlocks K 0 0 1 : Matrix (n ⊕ Fin m) (n ⊕ Fin m) k) * fromBlocks K' 0 0 1 = 1 := by
    rw [fromBlocks_multiply]; simp [hK]
  have h : ((A * (fromBlocks K 0 0 1 : Matrix (n ⊕ Fin m) (n ⊕ Fin m) k)) *
      ((fromBlocks K' 0 0 1 : Matrix (n ⊕ Fin m) (n ⊕ Fin m) k) * B)) a b = (A * B) a b := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (fromBlocks K 0 0 1), hE, Matrix.one_mul]
  rw [Matrix.mul_apply, Matrix.mul_apply, Fintype.sum_sum_type, Fintype.sum_sum_type] at h
  simp only [mul_blk_inr, blk_mul_inr] at h
  exact add_right_cancel h

end GlobalTheory

theorem phase_step_inv : ∀ {k : Type} [Field k] {n₀ n n₂ : Type} [Fintype n₀] [DecidableEq n₀] [Fintype n] [DecidableEq n] [Fintype n₂] [DecidableEq n₂] {c : ℕ},
    ∀ v ∈ symN k n (c + 1), ∀ (κ : GL n k) (x₀ : Matrix n n₀ k) (e₀ : StepVar n (c + 1) n₀ → k) (x₁ : Matrix n₂ n k) (e₁ : StepVar n₂ c n → k)
      (d₀ : Matrix (n ⊕ Fin (c + 1)) (n₀ ⊕ Fin (c + 1 + 1)) k) (d₁ : Matrix (n₂ ⊕ Fin c) (n ⊕ Fin (c + 1)) k),
      d₀ = ((v * embX (c + 1) κ)⁻¹).val * stepPt x₀ e₀ → d₁ = stepPt x₁ e₁ * (v * embX (c + 1) κ).val →
      (ch d₀ + ch d₁ + (if Even (c + 1) then ∑ r : n, (∑ l : Fin c, if l.val = c / 2 then d₁ (.inr l) (.inl r) else 0) *
          d₀ (.inl r) (.inr ⟨(c + 1) / 2, by omega⟩) else 0) =
        ch (stepPt x₀ e₀) + ch (stepPt x₁ e₁) + (if Even (c + 1) then ∑ r : n,
          (∑ l : Fin c, if l.val = c / 2 then stepPt x₁ e₁ (.inr l) (.inl r) else 0) *
            stepPt x₀ e₀ (.inl r) (.inr ⟨(c + 1) / 2, by omega⟩) else 0)) ∧
      (Odd (c + 1) → (∀ s : n₀, d₀ (.inr ⟨(c + 1) / 2, by omega⟩) (.inl s) = stepPt x₀ e₀ (.inr ⟨(c + 1) / 2, by omega⟩) (.inl s)) ∧
        ∀ r : n₂, d₁ (.inl r) (.inr ⟨c / 2, by omega⟩) = stepPt x₁ e₁ (.inl r) (.inr ⟨c / 2, by omega⟩)) := by
  intro k _ n₀ n n₂ _ _ _ _ _ _ c v hv κ x₀ e₀ x₁ e₁ d₀ d₁ h₀ h₁
  have hV : ∀ r s, ordL (c + 1) s ≤ ordL (c + 1) r → v.val r s = (1 : Matrix (n ⊕ Fin (c + 1)) _ k) r s :=
    GlobalTheory.DiagVol.symN_le_unipSub hv
  have hW : ∀ r s, ordL (c + 1) s ≤ ordL (c + 1) r → (v⁻¹).val r s = (1 : Matrix (n ⊕ Fin (c + 1)) _ k) r s :=
    GlobalTheory.DiagVol.symN_le_unipSub (inv_mem hv)
  have hVW : v.val * (v⁻¹).val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hK : κ.val * (κ⁻¹).val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have e₀' : d₀ = (fromBlocks (κ⁻¹).val 0 0 1 : Matrix (n ⊕ Fin (c + 1)) (n ⊕ Fin (c + 1)) k) * ((v⁻¹).val * stepPt x₀ e₀) := by
    rw [h₀, _root_.mul_inv_rev, Units.val_mul, ← map_inv, Matrix.mul_assoc]; rfl
  have e₁' : d₁ = (stepPt x₁ e₁ * v.val) * (fromBlocks κ.val 0 0 1 : Matrix (n ⊕ Fin (c + 1)) (n ⊕ Fin (c + 1)) k) := by
    rw [h₁, Units.val_mul, ← Matrix.mul_assoc]; rfl
  have hch₀ : ch d₀ = ch ((v⁻¹).val * stepPt x₀ e₀) := by
    rw [e₀']; unfold ch; simp only [blk_mul_inr]
  have hch₁ : ch d₁ = ch (stepPt x₁ e₁ * v.val) := by
    rw [e₁']; unfold ch; simp only [mul_blk_inr]
  rw [hch₀, hch₁, ch_shape_mul hW, ch_mul_shape hV]
  have hrel := fun l => simple_rel hV hW hVW l
  rcases Nat.even_or_odd (c + 1) with hc | hc
  · have hc' : c % 2 = 1 := by rcases hc with ⟨r, hr⟩; omega
    refine ⟨?_, fun h => absurd h (Nat.not_odd_iff_even.mpr hc)⟩
    rw [if_pos hc, if_pos hc]
    have hs0 : (⟨c / 2, by omega⟩ : Fin (c + 1)).succ = ⟨(c + 1) / 2, by omega⟩ := Fin.ext (by simp; omega)
    have hs1 : (⟨c / 2, by omega⟩ : Fin c).succ = ⟨(c + 1) / 2, by omega⟩ := Fin.ext (by simp; omega)
    have hcs : (⟨c / 2, by omega⟩ : Fin c).castSucc = ⟨c / 2, by omega⟩ := rfl
    have f0 : (∑ i : Fin (c + 1), if 2 * i.val + 1 = c then
        ∑ x, (v⁻¹).val (.inr i) (.inl x) * stepPt x₀ e₀ (.inl x) (.inr i.succ) else 0) =
        ∑ x, (v⁻¹).val (.inr ⟨c / 2, by omega⟩) (.inl x) * stepPt x₀ e₀ (.inl x) (.inr ⟨(c + 1) / 2, by omega⟩) := by
      rw [Finset.sum_eq_single ⟨c / 2, by omega⟩, if_pos (by simp; omega), hs0]
      · intro i _ hi; rw [if_neg]; intro h; exact hi (Fin.ext (by simp; omega))
      · simp
    have f1 : (∑ l : Fin c, if 2 * l.val + 1 = c then
        ∑ x, stepPt x₁ e₁ (.inr l) (.inl x) * v.val (.inl x) (.inr l.succ) else 0) =
        ∑ x, stepPt x₁ e₁ (.inr ⟨c / 2, by omega⟩) (.inl x) * v.val (.inl x) (.inr ⟨(c + 1) / 2, by omega⟩) := by
      rw [Finset.sum_eq_single ⟨c / 2, by omega⟩, if_pos (by simp; omega), hs1]
      · intro i _ hi; rw [if_neg]; intro h; exact hi (Fin.ext (by simp; omega))
      · simp
    have hS : ∑ l : Fin c, v.val (.inr l.castSucc) (.inr l.succ) + ∑ l : Fin c, (v⁻¹).val (.inr l.castSucc) (.inr l.succ) +
        ∑ x, v.val (.inr ⟨c / 2, by omega⟩) (.inl x) * (v⁻¹).val (.inl x) (.inr ⟨(c + 1) / 2, by omega⟩) = 0 := by
      have h := Finset.sum_eq_zero (s := Finset.univ) fun l _ => hrel l
      have f2 : (∑ l : Fin c, if 2 * l.val + 1 = c then
          ∑ x, v.val (.inr l.castSucc) (.inl x) * (v⁻¹).val (.inl x) (.inr l.succ) else 0) =
          ∑ x, v.val (.inr ⟨c / 2, by omega⟩) (.inl x) * (v⁻¹).val (.inl x) (.inr ⟨(c + 1) / 2, by omega⟩) := by
        rw [Finset.sum_eq_single ⟨c / 2, by omega⟩, if_pos (by simp; omega), hs1, hcs]
        · intro i _ hi; rw [if_neg]; intro h; exact hi (Fin.ext (by simp; omega))
        · simp
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, f2] at h
      exact h
    have hp : ∀ (D₁ : Matrix (n₂ ⊕ Fin c) (n ⊕ Fin (c + 1)) k) r,
        (∑ l : Fin c, if l.val = c / 2 then D₁ (.inr l) (.inl r) else 0) = D₁ (.inr ⟨c / 2, by omega⟩) (.inl r) := by
      intro D₁ r
      rw [Finset.sum_eq_single ⟨c / 2, by omega⟩, if_pos rfl]
      · intro i _ hi; rw [if_neg]; intro h; exact hi (Fin.ext h)
      · simp
    simp only [hp]
    rw [e₀', e₁', pair_blk _ _ hK, f0, f1]
    simp only [pair_right hV hc' x₁ e₁, pair_left hW hc' x₀ e₀]
    have hl : ∀ x, (v⁻¹).val (.inr ⟨c / 2, by omega⟩) (.inl x) = -v.val (.inr ⟨c / 2, by omega⟩) (.inl x) :=
      fun x => eq_neg_of_add_eq_zero_right (row_rel hV hW hVW hc' x)
    have hb : ∀ x, (v⁻¹).val (.inl x) (.inr ⟨(c + 1) / 2, by omega⟩) = -v.val (.inl x) (.inr ⟨(c + 1) / 2, by omega⟩) :=
      fun x => eq_neg_of_add_eq_zero_right (col_rel hV hW hVW hc' x)
    simp only [hl, hb] at hS ⊢
    simp only [add_mul, mul_add, neg_mul, mul_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib] at hS ⊢
    linear_combination hS
  · have hc' : c % 2 = 0 := by rcases hc with ⟨r, hr⟩; omega
    have hne : ¬ Even (c + 1) := Nat.not_even_iff_odd.mpr hc
    refine ⟨?_, fun _ => ⟨fun s => ?_, fun r => ?_⟩⟩
    · rw [if_neg hne, if_neg hne]
      have z0 : ∀ i : Fin (c + 1), ¬ (2 * i.val + 1 = c) := fun i => by omega
      have z1 : ∀ i : Fin c, ¬ (2 * i.val + 1 = c) := fun i => by omega
      simp only [z0, z1, if_false, Finset.sum_const_zero, add_zero]
      have hS : ∑ l : Fin c, v.val (.inr l.castSucc) (.inr l.succ) + ∑ l : Fin c, (v⁻¹).val (.inr l.castSucc) (.inr l.succ) = 0 := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_eq_zero fun l _ => by simpa [z1 l] using hrel l
      linear_combination hS
    · rw [e₀', blk_mul_inr, row_left hW hc']
    · rw [e₁', mul_blk_inr, row_right hV hc']

end GlobalTheory.PhaseStep
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierJacobiPhase_adjacentSteps_invariant_vertex : ∀ {k : Type} [Field k] {n₀ n n₂ : Type} [Fintype n₀] [DecidableEq n₀] [Fintype n] [DecidableEq n] [Fintype n₂] [DecidableEq n₂] {c : ℕ},
    ∀ v ∈ symN k n (c + 1), ∀ (κ : GL n k) (x₀ : Matrix n n₀ k) (e₀ : StepVar n (c + 1) n₀ → k) (x₁ : Matrix n₂ n k) (e₁ : StepVar n₂ c n → k)
      (d₀ : Matrix (n ⊕ Fin (c + 1)) (n₀ ⊕ Fin (c + 1 + 1)) k) (d₁ : Matrix (n₂ ⊕ Fin c) (n ⊕ Fin (c + 1)) k),
      d₀ = ((v * embX (c + 1) κ)⁻¹).val * stepPt x₀ e₀ → d₁ = stepPt x₁ e₁ * (v * embX (c + 1) κ).val →
      (ch d₀ + ch d₁ + (if Even (c + 1) then ∑ r : n, (∑ l : Fin c, if l.val = c / 2 then d₁ (.inr l) (.inl r) else 0) *
          d₀ (.inl r) (.inr ⟨(c + 1) / 2, by omega⟩) else 0) =
        ch (stepPt x₀ e₀) + ch (stepPt x₁ e₁) + (if Even (c + 1) then ∑ r : n,
          (∑ l : Fin c, if l.val = c / 2 then stepPt x₁ e₁ (.inr l) (.inl r) else 0) *
            stepPt x₀ e₀ (.inl r) (.inr ⟨(c + 1) / 2, by omega⟩) else 0)) ∧
      (Odd (c + 1) → (∀ s : n₀, d₀ (.inr ⟨(c + 1) / 2, by omega⟩) (.inl s) = stepPt x₀ e₀ (.inr ⟨(c + 1) / 2, by omega⟩) (.inl s)) ∧
        ∀ r : n₂, d₁ (.inl r) (.inr ⟨c / 2, by omega⟩) = stepPt x₁ e₁ (.inl r) (.inr ⟨c / 2, by omega⟩)) := by
  atlas_forward_decl GlobalTheory.PhaseStep.phase_step_inv
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
open GlobalTheory.FunObj.FiniteSupport

namespace GlobalTheory.FlatStepVertex

theorem mul_reindex_gen {k : Type} [Field k] {a c b : ℕ} {ι' ι : Type} (h : a + c = b) (f : ι' ≃ ι) (g : GL (Fin b) k)
    (D : Matrix (Fin a ⊕ Fin c) ι' k) :
    g.val * D.reindex (frame h) f = ((frameGL h g).val * D).reindex (frame h) f := by
  ext i j
  simp only [reindex_apply, submatrix_apply, mul_apply, frameGL_val]
  exact (Fintype.sum_equiv (frame h) _ _ (fun x => by simp)).symm

theorem reindex_mul_gen {k : Type} [Field k] {a c b : ℕ} {ι' ι : Type} (h : a + c = b) (f : ι' ≃ ι) (g : GL (Fin b) k)
    (D : Matrix ι' (Fin a ⊕ Fin c) k) :
    D.reindex f (frame h) * g.val = (D * (frameGL h g).val).reindex f (frame h) := by
  ext i j
  simp only [reindex_apply, submatrix_apply, mul_apply, frameGL_val]
  exact (Fintype.sum_equiv (frame h) _ _ (fun x => by simp)).symm

end GlobalTheory.FlatStepVertex

theorem GlobalTheory.flatStep_vertex : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {a₀ a₁ a₂ b c c₀ c' : ℕ} (ν : Measure k) [ν.IsAddHaarMeasure] (hc₀ : c₀ = c + 1) (hc' : c' = c + 1)
    (h₁ : a₁ + c₀ = b) (h₂ : a₁ + (c + 1) = b) (h' : a₁ + c' = b) (g : GL (Fin b) k) (κ : GL (Fin a₁) k),
    valuation k (gdet κ : k) = 1 → ∀ v ∈ symN k (Fin a₁) c', frameGL h' g = v * embX c' κ →
    ∀ (x₀ : Matrix (Fin a₁) (Fin a₀) k) (x₁ : Matrix (Fin a₂) (Fin a₁) k),
    ∃ φ₀ : (StepVar (Fin a₁) c₀ (Fin a₀) → k) ≃ᵐ (StepVar (Fin a₁) c₀ (Fin a₀) → k),
      MeasurePreserving φ₀ (stepVol ν (Fin a₁) c₀ (Fin a₀)) (stepVol ν (Fin a₁) c₀ (Fin a₀)) ∧
    ∃ φ₁ : (StepVar (Fin a₂) c (Fin a₁) → k) ≃ᵐ (StepVar (Fin a₂) c (Fin a₁) → k),
      MeasurePreserving φ₁ (stepVol ν (Fin a₂) c (Fin a₁)) (stepVol ν (Fin a₂) c (Fin a₁)) ∧
    ∀ e₀ e₁,
      (∀ {ι : Type} (f : Fin a₀ ⊕ Fin (c₀ + 1) ≃ ι), (g⁻¹).val * (stepPt x₀ e₀).reindex (frame h₁) f =
        (stepPt ((κ⁻¹).val * x₀) (φ₀ e₀)).reindex (frame h₁) f) ∧
      (∀ {ι : Type} (f : Fin a₂ ⊕ Fin c ≃ ι), (stepPt x₁ e₁).reindex f (frame h₂) * g.val =
        (stepPt (x₁ * κ.val) (φ₁ e₁)).reindex f (frame h₂)) ∧
      (ch (stepPt ((κ⁻¹).val * x₀) (φ₀ e₀)) + ch (stepPt (x₁ * κ.val) (φ₁ e₁)) + (if Even c₀ then ∑ r : Fin a₁,
          (∑ l : Fin c, if l.val = c / 2 then stepPt (x₁ * κ.val) (φ₁ e₁) (.inr l) (.inl r) else 0) *
            stepPt ((κ⁻¹).val * x₀) (φ₀ e₀) (.inl r) (.inr ⟨c₀ / 2, by omega⟩) else 0) =
        ch (stepPt x₀ e₀) + ch (stepPt x₁ e₁) + (if Even c₀ then ∑ r : Fin a₁,
          (∑ l : Fin c, if l.val = c / 2 then stepPt x₁ e₁ (.inr l) (.inl r) else 0) *
            stepPt x₀ e₀ (.inl r) (.inr ⟨c₀ / 2, by omega⟩) else 0)) ∧
      (Odd c₀ → ∀ (l : Fin c₀) (s : Fin a₀), l.val = c₀ / 2 →
        stepPt ((κ⁻¹).val * x₀) (φ₀ e₀) (.inr l) (.inl s) = stepPt x₀ e₀ (.inr l) (.inl s)) ∧
      (Odd c₀ → ∀ (r : Fin a₂) (i : Fin (c + 1)), i.val = c / 2 →
        stepPt (x₁ * κ.val) (φ₁ e₁) (.inl r) (.inr i) = stepPt x₁ e₁ (.inl r) (.inr i)) := by
  intro k _ _ _ _ _ _ a₀ a₁ a₂ b c c₀ c' ν _ hc₀ hc' h₁ h₂ h' g κ hκ v hv hg x₀ x₁
  subst hc₀ hc'
  obtain ⟨φ₀, hφ₀, H₀⟩ := GlobalTheory.T.fourierJacobiStep_leftChange_measurePreserving (n := Fin a₁) (n' := Fin a₀) (c := c + 1) ν v hv κ hκ x₀
  obtain ⟨φ₁, hφ₁, H₁⟩ := GlobalTheory.T.stepPoint_mul_periodUnipotent_GL_measurePreserving (n := Fin a₂) (n' := Fin a₁) (c := c) ν v hv κ hκ x₁
  refine ⟨φ₀, hφ₀, φ₁, hφ₁, fun e₀ e₁ => ?_⟩
  have hg₁ : frameGL h₁ g = v * embX (c + 1) κ := hg
  have hg₂ : frameGL h₂ g = v * embX (c + 1) κ := hg
  obtain ⟨A, B⟩ := GlobalTheory.T.fourierJacobiPhase_adjacentSteps_invariant_vertex (n₀ := Fin a₀) (n := Fin a₁) (n₂ := Fin a₂) (c := c) v hv κ x₀ e₀ x₁ e₁
    (stepPt ((κ⁻¹).val * x₀) (φ₀ e₀)) (stepPt (x₁ * κ.val) (φ₁ e₁)) (H₀ e₀).symm (H₁ e₁).symm
  refine ⟨fun f => ?_, fun f => ?_, A, fun ho l s hl => ?_, fun ho r i hi => ?_⟩
  · rw [GlobalTheory.FlatStepVertex.mul_reindex_gen, map_inv, hg₁, H₀]
  · rw [GlobalTheory.FlatStepVertex.reindex_mul_gen, hg₂, H₁]
  · rw [show l = ⟨(c + 1) / 2, by omega⟩ from Fin.ext hl]
    exact (B ho).1 s
  · rw [show i = ⟨c / 2, by omega⟩ from Fin.ext hi]
    exact (B ho).2 r
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
open GlobalTheory.FunObj.FiniteSupport
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastRowVertex_adjacentSteps_translate_frames : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {a₀ a₁ a₂ b c c₀ c' : ℕ} (ν : Measure k) [ν.IsAddHaarMeasure] (hc₀ : c₀ = c + 1) (hc' : c' = c + 1)
    (h₁ : a₁ + c₀ = b) (h₂ : a₁ + (c + 1) = b) (h' : a₁ + c' = b) (g : GL (Fin b) k) (κ : GL (Fin a₁) k),
    valuation k (gdet κ : k) = 1 → ∀ v ∈ symN k (Fin a₁) c', frameGL h' g = v * embX c' κ →
    ∀ (x₀ : Matrix (Fin a₁) (Fin a₀) k) (x₁ : Matrix (Fin a₂) (Fin a₁) k),
    ∃ φ₀ : (StepVar (Fin a₁) c₀ (Fin a₀) → k) ≃ᵐ (StepVar (Fin a₁) c₀ (Fin a₀) → k),
      MeasurePreserving φ₀ (stepVol ν (Fin a₁) c₀ (Fin a₀)) (stepVol ν (Fin a₁) c₀ (Fin a₀)) ∧
    ∃ φ₁ : (StepVar (Fin a₂) c (Fin a₁) → k) ≃ᵐ (StepVar (Fin a₂) c (Fin a₁) → k),
      MeasurePreserving φ₁ (stepVol ν (Fin a₂) c (Fin a₁)) (stepVol ν (Fin a₂) c (Fin a₁)) ∧
    ∀ e₀ e₁,
      (∀ {ι : Type} (f : Fin a₀ ⊕ Fin (c₀ + 1) ≃ ι), (g⁻¹).val * (stepPt x₀ e₀).reindex (frame h₁) f =
        (stepPt ((κ⁻¹).val * x₀) (φ₀ e₀)).reindex (frame h₁) f) ∧
      (∀ {ι : Type} (f : Fin a₂ ⊕ Fin c ≃ ι), (stepPt x₁ e₁).reindex f (frame h₂) * g.val =
        (stepPt (x₁ * κ.val) (φ₁ e₁)).reindex f (frame h₂)) ∧
      (ch (stepPt ((κ⁻¹).val * x₀) (φ₀ e₀)) + ch (stepPt (x₁ * κ.val) (φ₁ e₁)) + (if Even c₀ then ∑ r : Fin a₁,
          (∑ l : Fin c, if l.val = c / 2 then stepPt (x₁ * κ.val) (φ₁ e₁) (.inr l) (.inl r) else 0) *
            stepPt ((κ⁻¹).val * x₀) (φ₀ e₀) (.inl r) (.inr ⟨c₀ / 2, by omega⟩) else 0) =
        ch (stepPt x₀ e₀) + ch (stepPt x₁ e₁) + (if Even c₀ then ∑ r : Fin a₁,
          (∑ l : Fin c, if l.val = c / 2 then stepPt x₁ e₁ (.inr l) (.inl r) else 0) *
            stepPt x₀ e₀ (.inl r) (.inr ⟨c₀ / 2, by omega⟩) else 0)) ∧
      (Odd c₀ → ∀ (l : Fin c₀) (s : Fin a₀), l.val = c₀ / 2 →
        stepPt ((κ⁻¹).val * x₀) (φ₀ e₀) (.inr l) (.inl s) = stepPt x₀ e₀ (.inr l) (.inl s)) ∧
      (Odd c₀ → ∀ (r : Fin a₂) (i : Fin (c + 1)), i.val = c / 2 →
        stepPt (x₁ * κ.val) (φ₁ e₁) (.inl r) (.inr i) = stepPt x₁ e₁ (.inl r) (.inr i)) := by
  atlas_forward_decl GlobalTheory.flatStep_vertex
end
