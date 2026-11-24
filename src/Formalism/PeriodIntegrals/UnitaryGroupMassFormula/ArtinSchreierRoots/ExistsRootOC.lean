module

public import Formalism.PeriodIntegrals.ArtSch
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.Integral
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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

@[expose] public section

namespace PI.ArtSch.RootWork

open Polynomial

variable (l : ℕ) [Fact l.Prime]

theorem exists_root_OC (c b : OC l) : ∃ z : OC l, z ^ l - c * z - b = 0 := by
  classical
  have hl : 2 ≤ l := (Fact.out : l.Prime).two_le
  let p : (OC l)[X] := X ^ l - (C c * X + C b)
  have hdeg : (C c * X + C b).degree < (X ^ l : (OC l)[X]).degree := by
    rw [degree_X_pow]
    exact lt_of_le_of_lt degree_linear_le (by exact_mod_cast (show 1 < l by omega))
  have hmon : p.Monic := (monic_X_pow l).sub_of_left hdeg
  have hnat : p.natDegree = l := by
    apply natDegree_eq_of_degree_eq_some
    rw [degree_sub_eq_left_of_degree_lt hdeg, degree_X_pow]
  let q : ℂ_[l][X] := p.map (algebraMap (OC l) ℂ_[l])
  have hq : q.degree ≠ 0 := by
    rw [degree_eq_natDegree (hmon.map _).ne_zero, (hmon.natDegree_map _), hnat]
    exact_mod_cast (show l ≠ 0 by omega)
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root q hq
  have hx' : eval₂ (algebraMap (OC l) ℂ_[l]) x p = 0 := by
    rw [← eval_map]
    exact hx
  have hint : IsIntegral (OC l) x := ⟨p, hmon, hx'⟩
  have hmem : x ∈ PadicComplexInt l := (PadicComplexInt.integers l).mem_of_integral hint
  refine ⟨⟨x, hmem⟩, ?_⟩
  apply Subtype.ext
  have h2 : eval₂ (algebraMap (OC l) ℂ_[l]) x p = x ^ l - ((c : ℂ_[l]) * x + (b : ℂ_[l])) := by
    simp only [p, eval₂_sub, eval₂_add, eval₂_mul, eval₂_X_pow, eval₂_X, eval₂_C]
    rfl
  rw [h2] at hx'
  show x ^ l - (c : ℂ_[l]) * x - (b : ℂ_[l]) = 0
  rw [sub_sub]
  exact hx'

end PI.ArtSch.RootWork
