module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LengthEqLengthInvariantsOfTorsionLevels
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped TensorProduct
open GlobalTheory.TateLimit

private theorem step (l : ℕ) [Fact l.Prime] (X : Type) [AddCommGroup X] [Module ℤ_[l] X] [Finite X]
    (c : ℕ) : Nat.card (X ⧸ lpow l X (c + 1)) ≤
      Nat.card (X ⧸ lpow l X 1) * Nat.card (X ⧸ lpow l X c) := by
  haveI : ∀ P : Submodule ℤ_[l] X, Finite (X ⧸ P) := fun P =>
    Finite.of_surjective _ P.mkQ_surjective
  let f : X →ₗ[ℤ_[l]] X ⧸ lpow l X (c + 1) :=
    (lpow l X (c + 1)).mkQ ∘ₗ LinearMap.lsmul ℤ_[l] X ((l : ℤ_[l]) ^ c)
  have hf : lpow l X 1 ≤ LinearMap.ker f := by
    rintro _ ⟨y, rfl⟩
    simp only [f, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, LinearMap.lsmul_apply]
    exact ⟨y, by rw [LinearMap.lsmul_apply, pow_add, mul_smul]⟩
  let g := (lpow l X 1).liftQ f hf
  let R := LinearMap.range g
  have h1 : Nat.card R ≤ Nat.card (X ⧸ lpow l X 1) :=
    Nat.card_le_card_of_surjective g.rangeRestrict g.surjective_rangeRestrict
  let p : X →ₗ[ℤ_[l]] (X ⧸ lpow l X (c + 1)) ⧸ R := R.mkQ ∘ₗ (lpow l X (c + 1)).mkQ
  have hp : lpow l X c ≤ LinearMap.ker p := by
    rintro _ ⟨y, rfl⟩
    simp only [p, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    exact ⟨Submodule.Quotient.mk y, rfl⟩
  have hps : Function.Surjective p :=
    R.mkQ_surjective.comp (lpow l X (c + 1)).mkQ_surjective
  have h2 : Nat.card ((X ⧸ lpow l X (c + 1)) ⧸ R) ≤ Nat.card (X ⧸ lpow l X c) := by
    refine Nat.card_le_card_of_surjective ((lpow l X c).liftQ p hp) fun z => ?_
    obtain ⟨x, rfl⟩ := hps z
    exact ⟨Submodule.Quotient.mk x, rfl⟩
  rw [Submodule.card_eq_card_quotient_mul_card R]
  first
    | exact Nat.mul_le_mul h1 h2
    | exact (Nat.mul_le_mul h2 h1).trans_eq (mul_comm _ _)
