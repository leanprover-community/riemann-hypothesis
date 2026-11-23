module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.TaylorSpanGeneratorsAlt
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.HassePresH
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.HasseVan
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace PoleLengthBounds

theorem hasseSmul_holds : HasseSmul := by
  intro D B P j X ka wL wF G la k o x hx β hβ h h'
  classical
  have hmem : ∀ q : Idx D j G.N →₀ ℕ, hasse X la G.w q (x : Lw X la G.w) ∈ HK X la G.w wF := fun q =>
    (mem_HK X la G.w).2 (hasse_presentation X la G.w wF q _ ((mem_HK X la G.w).1 x.2))
  have key : (⟨_, h⟩ : ↥(HK X la G.w wF)) = ∑ q ∈ Finset.HasAntidiagonal.antidiagonal β,
      (@algebraMap (Op X la G.N) (Kp X la G.N) _ _ _ (hasseOp X la G.N q.1 o)) •
        (⟨_, hmem q.2⟩ : ↥(HK X la G.w wF)) := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    show hasse X la G.w β ((o • x : ↥(HK X la G.w wF)) : Lw X la G.w) = _
    rw [Submodule.coe_smul_of_tower, Algebra.smul_def,
      IsScalarTower.algebraMap_apply (Op X la G.N) (Rp X la G.N) (Lw X la G.w)]
    erw [hasse_mul]
    refine Finset.sum_congr rfl fun q _ => ?_
    erw [hasse_algebraMap_Op]
    rw [Submodule.coe_smul_of_tower, Algebra.smul_def]
    congr 1

  rw [key, map_sum, Finset.sum_eq_single (0, β)]
  · rw [LinearMap.map_smul_of_tower, hasseOp_zero, algebraMap_smul]
  · intro q hq hne
    rw [LinearMap.map_smul_of_tower]
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hq
    have h1 : q.1 ≠ 0 := fun h0 => hne (Prod.ext h0 (by rw [← hq, h0, zero_add]))
    have h2 : (q.2.sum fun _ n => n) < k := by
      rw [sumN_eq] at hβ ⊢
      rw [← hq, map_add (f := _)] at hβ
      have : Finsupp.degree q.1 ≠ 0 := fun h0 => h1 ((Finsupp.degree_eq_zero_iff _).1 h0)
      omega
    rw [hasseVan_holds G la k x hx q.2 h2 (hmem q.2), smul_zero]
  · intro h0
    exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.2 (zero_add β)) h0

end PoleLengthBounds
