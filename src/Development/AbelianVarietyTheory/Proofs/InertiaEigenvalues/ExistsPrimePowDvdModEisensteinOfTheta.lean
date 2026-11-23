module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimePowMulEqThetaWitt
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.LiftDiv

theorem dvd_mod_E : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (s : bk.S) (n : ℕ) (y : OC l), Per.θ l (bk.ev s) = (l : OC l) ^ n * y → ∃ s' t : bk.S, s = (l : bk.S) ^ n * s' + bk.E * t := by
  intro l _ K bk s n y h
  set r : ↥(OL K) := bk.str.symm (Ideal.Quotient.mk _ s) with hr
  have hθ : Per.θ l (bk.ev s) = intToOC K r := bk.θ_ev r s (by rw [hr, RingEquiv.apply_symm_apply])
  have hC : ((((r : ↥K.1) : Om l)) : ℂ_[l]) = (l : ℂ_[l]) ^ n * ((y : OC l) : ℂ_[l]) := by
    rw [← coe_intToOC, ← hθ, h]
    push_cast
    rfl
  have hl0 : (l : Om l) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hlpos : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have hnorm : ‖((r : ↥K.1) : Om l)‖ ≤ ((l : ℝ)⁻¹) ^ n := by
    rw [← PadicComplex.norm_extends, hC, norm_mul, norm_pow, GlobalTheory.UnrWitt.norm_l_C]
    exact mul_le_of_le_one_right (by positivity) (GlobalTheory.UnrWitt.norm_OC_le y)
  set q : ↥K.1 := (r : ↥K.1) / (l : ↥K.1) ^ n with hq
  have hqO : ((q : ↥K.1) : Om l) = ((r : ↥K.1) : Om l) / (l : Om l) ^ n := by
    rw [hq]; push_cast; rfl
  have hq1 : ‖((q : ↥K.1) : Om l)‖ ≤ 1 := by
    rw [hqO, norm_div, norm_pow, GlobalTheory.UnrWitt.norm_l_Om]
    rw [div_le_one (by positivity)]
    exact hnorm
  let r' : ↥(OL K) := ⟨q, GlobalTheory.UnrWitt.mem_OL_of_norm_le K q hq1⟩
  have hrr : r = (l : ↥(OL K)) ^ n * r' := by
    apply Subtype.ext
    apply Subtype.ext
    have : ((((l : ↥(OL K)) ^ n * r' : ↥(OL K)) : ↥K.1) : Om l) = (l : Om l) ^ n * ((q : ↥K.1) : Om l) := by
      push_cast; rfl
    rw [this, hqO, mul_div_cancel₀ _ (pow_ne_zero _ hl0)]
  obtain ⟨s', hs'⟩ := Ideal.Quotient.mk_surjective (bk.str r')
  have hmk : Ideal.Quotient.mk (Ideal.span {bk.E}) (s - (l : bk.S) ^ n * s') = 0 := by
    have e1 : Ideal.Quotient.mk (Ideal.span {bk.E}) s = bk.str r := by
      rw [hr, RingEquiv.apply_symm_apply]
    rw [map_sub, map_mul, map_pow, map_natCast, e1, hs', hrr, map_mul, map_pow, map_natCast, sub_self]
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 hmk)
  exact ⟨s', t, by rw [mul_comm bk.E t, ht]; ring⟩

end GlobalTheory.LiftDiv
