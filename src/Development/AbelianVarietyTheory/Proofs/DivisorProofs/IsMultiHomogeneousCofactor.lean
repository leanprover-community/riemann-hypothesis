module

public import ReciprocityTheory.SemistableReduction.SphereLogIntegrableStatement
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.SemistableReduction.AevalIsWeightedHomogeneous
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBoundedPolesGlobalData
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import Development.AbelianVarietyTheory.Definitions.Divisors.JoinCastSucc
import Development.AbelianVarietyTheory.Definitions.Divisors.LinearIndependentBasisCoords
import Development.AbelianVarietyTheory.Definitions.Divisors.MemSubPtsCutBaseChangeIff
import Development.AbelianVarietyTheory.Definitions.Divisors.PointHeight
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsAddEquivOfSurjectiveOfKerIff
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.EllipsoidStA

@[expose] public section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory.CofactorHom

theorem wcomp_mul_of_left {σ F : Type} [Field F] (w : σ → ℕ) (n : ℕ) {P : MvPolynomial σ F} {k : ℕ}
    (hP : IsWeightedHomogeneous w P k) (Q : MvPolynomial σ F) :
    weightedHomogeneousComponent w n (P * Q) =
      if k ≤ n then P * weightedHomogeneousComponent w (n - k) Q else 0 := by
  classical
  let := weightedGradedAlgebra F w
  have h := DirectSum.coe_decompose_mul_of_left_mem (weightedHomogeneousSubmodule F w) (a := P) (b := Q) n
    ((mem_weightedHomogeneousSubmodule F w k P).2 hP)
  have e : ∀ (m : ℕ) (R : MvPolynomial σ F),
      ((DirectSum.decompose (weightedHomogeneousSubmodule F w) R m : weightedHomogeneousSubmodule F w m) :
        MvPolynomial σ F) = weightedHomogeneousComponent w m R :=
    fun m R => weightedDecomposition.decompose'_apply F w R m
  rw [e, e] at h
  exact h

theorem weight_add_of_mul {σ F : Type} [Field F] (w : σ → ℕ) {P Q : MvPolynomial σ F} {k m : ℕ}
    (hPQ : P * Q ≠ 0) (hP : IsWeightedHomogeneous w P k) (hm : IsWeightedHomogeneous w (P * Q) m)
    (s : σ →₀ ℕ) (hs : s ∈ Q.support) : k + Finsupp.weight w s = m := by
  classical
  have hP0 : P ≠ 0 := left_ne_zero_of_mul hPQ
  set j := Finsupp.weight w s
  have hc : weightedHomogeneousComponent w j Q ≠ 0 := by
    intro h0
    have := congrArg (AddMonoidAlgebra.coeff · s) h0
    apply (mem_support_iff.mp hs)
    simpa only [coeff_weightedHomogeneousComponent, j, ite_true,
      AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] using this

  have hne : weightedHomogeneousComponent w (k + j) (P * Q) ≠ 0 := by
    simp only [wcomp_mul_of_left w (k + j) hP Q, Nat.le_add_right, ite_true,
      Nat.add_sub_cancel_left]
    exact mul_ne_zero hP0 hc
  by_contra hkm
  exact hne (hm.weightedHomogeneousComponent_ne (k + j) hkm)

end GlobalTheory.CofactorHom


open GlobalTheory.CofactorHom in
theorem GlobalTheory.HSShort.isMultiHomogeneous_cofactor :
    ∀ (F : Type) [Field F] (B N : ℕ) (a a₁ : Fin B → ℕ) (G G' : MvPolynomial (Fin B × Fin N) F),
      G * G' ≠ 0 → IsMultiHomogeneous a (G * G') → IsMultiHomogeneous a₁ G →
        ∃ a' : Fin B → ℕ, IsMultiHomogeneous a' G' ∧ ∀ i, a₁ i + a' i = a i := by
  intro F _ B N a a₁ G G' h0 ha ha₁
  rw [isMultiHomogeneous_iff_forall_weighted_lh0BlockWt] at ha ha₁
  have key : ∀ b, ∀ s ∈ G'.support, a₁ b + ∑ j : Fin N, s (b, j) = a b := fun b s hs => by
    rw [← weight_lh0BlockWt_apply]
    exact weight_add_of_mul _ h0 (ha₁ b) (ha b) s hs
  obtain ⟨s₀, hs₀⟩ : ∃ s, s ∈ G'.support := by
    by_contra hno
    push Not at hno
    apply h0
    rw [show G' = 0 from by
      ext s; by_contra hc; exact hno s (mem_support_iff.mpr hc), mul_zero]
  refine ⟨fun b => a b - a₁ b, fun s hs b => ?_, fun i => ?_⟩
  · have := key b s hs
    show _ = a b - a₁ b
    omega
  · have := key i s₀ hs₀
    show a₁ i + (a i - a₁ i) = a i
    omega
