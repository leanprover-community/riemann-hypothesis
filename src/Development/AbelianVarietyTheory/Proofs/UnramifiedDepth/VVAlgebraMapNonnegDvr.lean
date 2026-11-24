module

public import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
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
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

@[expose] public section

open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField

namespace GlobalTheory

theorem vV_algebraMap_nonneg_dvr (T : CDVR) (x : T.V) : 0 ≤ vV T.V (algebraMap T.V T.Fr x) := by
  unfold vV valV
  rw [neg_nonneg]
  have h1 := IsDedekindDomain.HeightOneSpectrum.valuation_le_one (K := T.Fr)
    (IsDiscreteValuationRing.maximalIdeal T.V) x
  by_cases h0 : (IsDedekindDomain.HeightOneSpectrum.valuation T.Fr
      (IsDiscreteValuationRing.maximalIdeal T.V)) (algebraMap T.V T.Fr x) = 0
  · rw [h0, WithZero.log_zero]
  · rw [WithZero.log_le_iff_le_exp h0]
    simpa using h1

theorem nval_eq_of_extension :
    ∀ (T : CDVR) (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (l : ℕ), l ≠ 0 → v (l : C) = 1 → ∀ (ι : T.Fr →+* C), (∀ x : T.Fr, x ≠ 0 → v (ι x) = (((vV T.V x : ℝ) / (vV T.V ((l : ℕ) : T.Fr) : ℝ) : ℝ) : WithTop ℝ)) → (∀ x : T.V, ((0 : ℝ) : WithTop ℝ) ≤ v (ι (algebraMap T.V T.Fr x))) ∧ ∀ x : T.Fr, nval T.V (vV T.V ((l : ℕ) : T.Fr)).toNat x = (WithBot.some (v (ι x)) : WithBot (WithTop ℝ)) := by
  intro T C _ v l hl hv ι hι
  have hvl : 0 ≤ vV T.V ((l : ℕ) : T.Fr) := by
    have h := vV_algebraMap_nonneg_dvr T (l : T.V)
    rwa [map_natCast] at h
  have hcast : (((vV T.V ((l : ℕ) : T.Fr)).toNat : ℕ) : ℝ) = ((vV T.V ((l : ℕ) : T.Fr) : ℤ) : ℝ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hvl]
  refine ⟨fun x => ?_, fun x => ?_⟩
  · by_cases hx : x = 0
    · subst hx
      simp
    · have hx' : algebraMap T.V T.Fr x ≠ 0 := fun h =>
        hx ((IsFractionRing.injective T.V T.Fr) (by rw [h, map_zero]))
      rw [hι _ hx']
      have h1 : (0 : ℝ) ≤ (vV T.V (algebraMap T.V T.Fr x) : ℝ) := by
        exact_mod_cast vV_algebraMap_nonneg_dvr T x
      have h2 : (0 : ℝ) ≤ (vV T.V ((l : ℕ) : T.Fr) : ℝ) := by exact_mod_cast hvl
      exact WithTop.coe_le_coe.mpr (div_nonneg h1 h2)
  · unfold nval
    split_ifs with hx
    · subst hx
      simp only [map_zero, AddValuation.map_zero]
      rfl
    · rw [hι x hx, hcast]
      rfl

end GlobalTheory
