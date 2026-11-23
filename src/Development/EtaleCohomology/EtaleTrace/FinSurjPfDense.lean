module

public import Development.EtaleCohomology.EtaleTrace.FinSurjPf
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LateralTheory.EtaleTrace.Cov

theorem loc_generic_top (X : Scheme.{0}) [IsIntegral X] (z : X.functionField) : z ∈ loc X (genericPoint X) := by
  refine ⟨z, ?_⟩
  simp [RingHom.algebraMap_toAlgebra, TopCat.Presheaf.stalkSpecializes_refl]

theorem FSDense_pf : FSDense := by
  intro k _ X _ p d π w cw hind

  have hz : ∀ (n : ℕ) (g : MvPolynomial (Fin (d + 1)) k), g.IsHomogeneous n →
      g ∈ (π (genericPoint X)).asHomogeneousIdeal → g = 0 := by
    intro n g hg hmem
    have hgX : (g * MvPolynomial.X 0).IsHomogeneous (n + 1) := hg.mul (isHomogeneous_X k (0 : Fin (d + 1)))
    have h1 := (cw.opens (n + 1) (Nat.succ_pos n) (g * MvPolynomial.X 0) hgX (genericPoint X))
    have hnot : genericPoint X ∉ π ⁻¹ᵁ Proj.basicOpen _ (g * MvPolynomial.X 0) := by
      intro h
      have h' : π (genericPoint X) ∈ Proj.basicOpen _ (g * MvPolynomial.X 0) := h
      rw [Proj.mem_basicOpen] at h'
      exact h' (Ideal.mul_mem_right _ _ hmem)
    have he : eval₂ (kHom p) w (g * MvPolynomial.X 0) = 0 := by
      by_contra hne
      exact hnot (h1.2 ⟨hne, fun _ _ => loc_generic_top X _⟩)
    have := hind (n + 1) _ hgX he
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd h (X_ne_zero 0)
  have hbot : ∀ a ∈ (π (genericPoint X)).asHomogeneousIdeal, a = 0 := by
    intro a ha
    classical
    rw [← DirectSum.sum_support_decompose (homogeneousSubmodule (Fin (d + 1)) k) a]
    refine Finset.sum_eq_zero fun i _ => ?_
    refine hz i _ ?_ ((π (genericPoint X)).asHomogeneousIdeal.isHomogeneous i ha)
    exact (mem_homogeneousSubmodule i _).mp (SetLike.coe_mem _)
  constructor
  intro y
  have hle : (show ProjectiveSpectrum (homogeneousSubmodule (Fin (d + 1)) k) from π (genericPoint X)) ≤
      (show ProjectiveSpectrum (homogeneousSubmodule (Fin (d + 1)) k) from y) := by
    rw [← ProjectiveSpectrum.as_ideal_le_as_ideal]
    intro a ha
    rw [hbot a ha]
    exact zero_mem _
  have hc := (ProjectiveSpectrum.le_iff_mem_closure _ _ _).mp hle
  exact closure_mono (Set.singleton_subset_iff.mpr (Set.mem_range_self _)) hc
