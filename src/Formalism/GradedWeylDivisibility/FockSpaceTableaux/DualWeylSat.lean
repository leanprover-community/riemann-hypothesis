module

public import Formalism.GradedWeylDivisibility.StatementA
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LSatLemmas
import Mathlib.Algebra.AffineMonoid.UniqueSums
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem dualWeylModuleSaturated : DualWeylSat := by
  intro R _ _ r n ν c f hc hcf
  rw [lsat_mem_dualWeyl] at hcf ⊢
  obtain ⟨hwh, hcol⟩ := hcf
  refine ⟨fun {d} hd => hwh ?_, fun l j hlj => ?_⟩
  · rw [AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul]
    exact mul_ne_zero hc hd
  · have h := hcol l j hlj
    rw [smul_eq_C_mul, map_mul, map_mul, algHom_C, algHom_C] at h
    exact mul_left_cancel₀ (by simpa using hc) h

end Formalism.GradedWeylDivisibility
