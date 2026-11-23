module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StepLin
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairPtsClasses
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ValuationGdetKapAt

@[expose] public section

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
    by_cases h1 : s = s' <;> by_cases h2 : l = l' <;> simp [h1, h2, Matrix.one_apply, Subtype.ext_iff]
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
