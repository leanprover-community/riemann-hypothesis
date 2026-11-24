module

public import Formalism.LocalRingCardinality.DataCoeff
public import Formalism.BranchSandwichDivisors.BranchIsometryProofs.BranchScale
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.ClosedEqNabla
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.GlobalSchurBounds.FlipTwoThree
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility Formalism.MainNotions.flipTwoThree
open Formalism.REAL (fockF)

theorem natW_anti {N : ℕ} (lam : DomWeight N) : Antitone lam.natW := by
  intro i j h
  have := lam.anti h
  unfold DomWeight.natW
  omega

theorem weyl_eq_dual (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ) (hν : Antitone ν) :
    weyl ℂ r n hn ν = dualWeyl ℂ r n ν :=
  le_antisymm (Formalism.GradedWeylDivisibility.weylLeDual ℂ r n hn ν hν) (Formalism.BranchingDeterminantCap.bs_dual_le_weyl hn ν hν)

theorem dualWeyl_fd (r n : ℕ) (ν : Fin n → ℕ) : FiniteDimensional ℂ (dualWeyl ℂ r n ν) := by
  have hle : dualWeyl ℂ r n ν ≤ homogeneousSubmodule (Fin r × Fin n) ℂ (∑ s, ν s) := by
    intro f hf
    have h1 : f ∈ weightedHomogeneousSubmodule ℂ (colW r n) ν := (Submodule.mem_inf.mp hf).1
    rw [mem_weightedHomogeneousSubmodule] at h1
    rw [mem_homogeneousSubmodule]
    intro m hm
    rw [← Formalism.GradedWeylDivisibility.lclosedeq_weight_sum, h1 hm]
  have : FiniteDimensional ℂ (homogeneousSubmodule (Fin r × Fin n) ℂ (∑ s, ν s)) :=
    Module.Finite.iff_fg.mpr (homogeneousSubmodule_fg _ _ _)
  exact Submodule.finiteDimensional_of_le hle

theorem delSq_rowAct {n : ℕ} (sg : DomWeight n) (A : Matrix (Fin n) (Fin n) ℂ) (v : MvPolynomial (Fin n × Fin n) ℂ)
    (hv : v ∈ delSq ℂ n sg) : rowAct ℂ A v ∈ delSq ℂ n sg := by
  unfold delSq at hv ⊢
  rw [weyl_eq_dual n n le_rfl _ (natW_anti sg)] at hv ⊢
  exact Formalism.GradedWeylDivisibility.dualWeylRowStable ℂ n n _ A v hv

theorem delSq_fd {n : ℕ} (sg : DomWeight n) : FiniteDimensional ℂ (delSq ℂ n sg) := by
  unfold delSq
  rw [weyl_eq_dual n n le_rfl _ (natW_anti sg)]
  exact dualWeyl_fd n n _

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
