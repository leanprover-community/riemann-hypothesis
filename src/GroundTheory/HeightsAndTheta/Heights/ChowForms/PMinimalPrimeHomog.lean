module

public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Statements
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
public import Mathlib.RingTheory.GradedAlgebra.Radical
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

theorem isHomogIdeal_iff_isHomogeneous_degree {R : Type*} [CommRing R] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) R)) :
    IsHomogIdeal I ↔ I.IsHomogeneous (homogeneousSubmodule (Fin n) R) := by
  constructor
  · intro h i r hr
    convert h r hr i using 1
    exact decomposition.decompose'_apply r i
  · intro h f hf d
    exact homogeneousComponent_mem_of_mem h hf d

theorem MinimalPrimeHomog.proof : MinimalPrimeHomog.Statement := by
  intro F _ n J W hJ hW
  rw [isHomogIdeal_iff_isHomogeneous_degree] at hJ ⊢
  have hWp : W.IsPrime := hW.1.1
  have hcore : (W.homogeneousCore (homogeneousSubmodule (Fin n) F)).toIdeal = W := by
    apply le_antisymm (Ideal.toIdeal_homogeneousCore_le _ _)
    refine hW.2 ⟨hWp.homogeneousCore, ?_⟩ (Ideal.toIdeal_homogeneousCore_le _ _)
    exact hJ.toIdeal_homogeneousCore_eq_self.symm.trans_le (Ideal.homogeneousCore_mono _ hW.1.2)
  rw [← hcore]
  exact (W.homogeneousCore _).isHomogeneous

end GroundTheory.Heights₂.Heights
