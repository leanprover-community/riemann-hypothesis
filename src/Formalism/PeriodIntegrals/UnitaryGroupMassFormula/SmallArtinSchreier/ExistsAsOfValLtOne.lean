module

public import Formalism.PeriodIntegrals.ArtSch
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SmallArtinSchreier.CoordPowEqZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace PI.UnitaryGroupMassFormula.ASSmall

open scoped NNReal

section Gen

variable {K : Type*} [Field K] {v : Valuation K ℝ≥0} {O : Type*} [CommRing O] [Algebra O K]
  (hv : v.Integers O) {p : ℕ} [Fact p.Prime] [Fact (¬ IsUnit (p : O))]

include hv in
theorem coeff_zero_nilpotent (hp : 0 < v (p : K)) (e : PreTilt O p)
    (he : PreTilt.val K v O hv p e < 1) : ∃ N : ℕ, PreTilt.coeff 0 e ^ N = 0 := by
  by_cases h0 : PreTilt.coeff 0 e = 0
  · exact ⟨1, by rw [pow_one, h0]⟩
  have hval : PreTilt.val K v O hv p e = ModP.preVal K v O p (PreTilt.coeff 0 e) := by
    change PreTilt.valAux K v O p e = _
    rw [PreTilt.valAux_eq hv h0, pow_zero, pow_one]
  obtain ⟨E, hE⟩ := Ideal.Quotient.mk_surjective (PreTilt.coeff 0 e)
  have hE0 : (Ideal.Quotient.mk (Ideal.span {(p : O)}) E : ModP O p) ≠ 0 := by
    rw [hE]; exact h0
  have hvE : v (algebraMap O K E) < 1 := by
    rw [← ModP.preVal_mk hv hE0, hE, ← hval]; exact he
  obtain ⟨N, hN⟩ := NNReal.exists_pow_lt_of_lt_one hp hvE
  refine ⟨N, ?_⟩
  have hEN : (Ideal.Quotient.mk (Ideal.span {(p : O)}) (E ^ N) : ModP O p) = 0 := by
    by_contra h
    have h1 := (ModP.v_p_lt_val hv).2 h
    rw [map_pow, v.map_pow] at h1
    exact lt_asymm h1 hN
  rw [← hE, ← map_pow]; exact hEN

include hv in
theorem exists_as_of_val_lt_one (hp : 0 < v (p : K)) (e : PreTilt O p)
    (he : PreTilt.val K v O hv p e < 1) : ∃ w : PreTilt O p, w ^ p - w = e := by
  obtain ⟨N, hN⟩ := coeff_zero_nilpotent hv hp e he
  exact ⟨solPerf (R := ModP O p) (p := p) e hN, solPerf_spec (R := ModP O p) (p := p) e hN⟩

end Gen

theorem tiltSmall : PI.ArtSch.TiltSmall := by
  intro l _ e he
  have hp : 0 < (PadicComplex.valued l).v ((l : ℕ) : PadicComplex l) := by
    rw [PadicComplex.valuation_p l]
    have : (0 : ℝ≥0) < (l : ℝ≥0) := by exact_mod_cast (Fact.out : l.Prime).pos
    positivity
  exact exists_as_of_val_lt_one (PadicComplexInt.integers l) hp e he

end PI.UnitaryGroupMassFormula.ASSmall
