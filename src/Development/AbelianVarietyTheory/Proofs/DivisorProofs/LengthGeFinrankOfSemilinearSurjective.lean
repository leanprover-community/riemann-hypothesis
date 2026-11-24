module

public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.WittVector.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.Teichmuller
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.KerIdealCompOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsAddEquivOfSurjectiveOfKerIff
import Mathlib.CategoryTheory.Preadditive.EndoFunctor
import Mathlib.RingTheory.Bialgebra.Basic

@[expose] public section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.Dieu

theorem length_ge_finrank_of_semilinear_surj (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    [PerfectRing k p] (N U : Type) [AddCommGroup N] [Module (WittVector p k) N] [AddCommGroup U]
    [Module k U] [Module.Finite k U] (e : (WittVector p k) ≃+* (WittVector p k)) (θ : N →+ U) :
    Function.Surjective θ → (∀ (a : (WittVector p k)) n, θ (e a • n) = WittVector.constantCoeff a • θ n) →
    ∀ L : Submodule (WittVector p k) N, ((∀ n ∈ L, θ n = 0) →
      (Module.finrank k U : ℕ∞) ≤ Module.length (WittVector p k) (N ⧸ L)) ∧
      ((∀ n, n ∈ L ↔ θ n = 0) → Module.length (WittVector p k) (N ⧸ L) = Module.finrank k U) := by
  intro hθ hsemi L
  let σ : WittVector p k →+* k := (WittVector.constantCoeff).comp e.symm.toRingHom
  have hσ : Function.Surjective σ := by
    intro x
    obtain ⟨a, ha⟩ : ∃ a : WittVector p k, WittVector.constantCoeff a = x :=
      ⟨WittVector.teichmuller p x, by simp⟩
    exact ⟨e a, by simp [σ, ha]⟩
  letI : Algebra (WittVector p k) k := σ.toAlgebra
  letI : Module (WittVector p k) U := Module.compHom U σ
  haveI : IsScalarTower (WittVector p k) k U :=
    ⟨fun a b u => by
      show (σ a * b) • u = σ a • (b • u)
      exact mul_smul _ _ _⟩
  have hlenU : Module.length (WittVector p k) U = Module.finrank k U := by
    rw [Module.length_eq_of_surjective (R := k) (S := WittVector p k) (M := U) hσ,
      Module.length_eq_finrank]
  let θl : N →ₗ[WittVector p k] U :=
    { toFun := θ
      map_add' := θ.map_add
      map_smul' := fun a n => by
        have h := hsemi (e.symm a) n
        rw [RingEquiv.apply_symm_apply] at h
        exact h }
  have hθl : Function.Surjective θl := hθ
  refine ⟨fun hL => ?_, fun hL => ?_⟩
  · have hle : L ≤ LinearMap.ker θl := fun n hn => hL n hn
    rw [← hlenU]
    exact Module.length_le_of_surjective (L.liftQ θl hle) (by
      intro u
      obtain ⟨n, rfl⟩ := hθl u
      exact ⟨Submodule.Quotient.mk n, rfl⟩)
  · have hK : L = LinearMap.ker θl := by
      ext n
      exact hL n
    rw [← hlenU, hK]
    exact (θl.quotKerEquivOfSurjective hθl).length_eq

end GlobalTheory.Dieu
