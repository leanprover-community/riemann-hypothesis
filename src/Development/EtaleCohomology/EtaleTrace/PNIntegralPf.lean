module

public import Development.EtaleCohomology.EtaleTrace.PNBasicPf
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LateralTheory.EtaleTrace.Cov

theorem hl_reduced (k : Type) [Field k] (d : ℕ) (P : Ideal (MvPolynomial (Fin (d + 1)) k)) [P.IsPrime] :
    _root_.IsReduced (HomogeneousLocalization.AtPrime (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k) P) := by
  refine ⟨fun a ha => ?_⟩
  obtain ⟨n, hn⟩ := ha
  apply HomogeneousLocalization.val_injective
  have h : a.val ^ n = 0 := by
    rw [← HomogeneousLocalization.val_pow, hn, HomogeneousLocalization.val_zero]
  rw [HomogeneousLocalization.val_zero]
  exact IsReduced.eq_zero _ ⟨n, h⟩

theorem pn_reduced (k : Type) [Field k] (d : ℕ) : IsReduced (PN k d) := by
  have : ∀ x : PN k d, _root_.IsReduced ((PN k d).presheaf.stalk x) := by
    intro x
    haveI : x.asHomogeneousIdeal.toIdeal.IsPrime := x.isPrime
    haveI := hl_reduced k d x.asHomogeneousIdeal.toIdeal
    let e := Proj.stalkIso' (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k) x
    exact isReduced_of_injective e.toRingHom e.injective
  exact isReduced_of_isReduced_stalk _

theorem mvPolynomial_irrelevantIdeal_not_le_bot_projective (k : Type) [Field k] (d : ℕ) :
    ¬ HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k) ≤ ⊥ := by
  intro h
  have hm : (X 0 : MvPolynomial (Fin (d + 1)) k) ∈ HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k) := by
    rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply]
    exact DirectSum.decompose_of_mem_ne _ ((MvPolynomial.mem_homogeneousSubmodule _ _).2 (isHomogeneous_X k 0)) (by decide)
  have h2 : (X 0 : MvPolynomial (Fin (d + 1)) k) ∈ (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k)).toIdeal := h hm
  rw [HomogeneousIdeal.toIdeal_bot, Ideal.mem_bot] at h2
  exact X_ne_zero _ h2

def gen (k : Type) [Field k] (d : ℕ) : PN k d where
  asHomogeneousIdeal := ⊥
  isPrime := by
    show (⊥ : Ideal (MvPolynomial (Fin (d + 1)) k)).IsPrime
    exact Ideal.isPrime_bot
  not_irrelevant_le := mvPolynomial_irrelevantIdeal_not_le_bot_projective k d

theorem pn_irred (k : Type) [Field k] (d : ℕ) : IrreducibleSpace (PN k d) := by
  rw [irreducibleSpace_def]
  have : (Set.univ : Set (PN k d)) = closure {gen k d} := by
    ext y
    simp only [Set.mem_univ, true_iff]
    exact (ProjectiveSpectrum.le_iff_mem_closure (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k) (gen k d) y).1
      (show (gen k d).asHomogeneousIdeal ≤ y.asHomogeneousIdeal from bot_le)
  change IsIrreducible (Set.univ : Set (PN k d))
  rw [this]
  exact isIrreducible_singleton.closure

theorem PNIntegral_of : PNIntegral := fun k _ d => by
  haveI := pn_reduced k d
  haveI := pn_irred k d
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end LateralTheory.EtaleTrace.Cov
