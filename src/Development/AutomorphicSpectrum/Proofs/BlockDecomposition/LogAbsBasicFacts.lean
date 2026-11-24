module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1 GlobalTheory.CuspRep

namespace GlobalTheory.CompanionTheory.LogAbs

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

theorem norm_cW_eq_one (u : Ad E) (hu : IsUnit u) : ∀ᶠ w in Filter.cofinite, ‖cW w u‖ = 1 := by
  have h := (FiniteAdeleRing.isUnit_iff.1 (hu.map (pFin E))).2
  filter_upwards [h] with w hw
  have e : cW w u = (pFin E u) w := rfl
  rw [e, FinitePlace.norm_def, hw]
  simp

theorem support_log_finite (u : Ad E) (hu : IsUnit u) :
    (Function.support fun w => Real.log ‖cW w u‖).Finite := by
  refine (Filter.eventually_cofinite.1 (norm_cW_eq_one u hu)).subset fun w hw h1 => hw ?_
  simp [h1]

theorem logAbs_mul (u u' : Ad E) (hu : IsUnit u) (hu' : IsUnit u') :
    logAbs (u * u') = logAbs u + logAbs u' := by
  have h1 : ∀ v, Real.log (‖cV v (u * u')‖ ^ 2) = Real.log (‖cV v u‖ ^ 2) + Real.log (‖cV v u'‖ ^ 2) := fun v => by
    rw [map_mul, norm_mul, mul_pow, Real.log_mul
      (pow_ne_zero 2 (norm_ne_zero_iff.2 (hu.map (cV v)).ne_zero))
      (pow_ne_zero 2 (norm_ne_zero_iff.2 (hu'.map (cV v)).ne_zero))]
  have h2 : ∀ w, Real.log ‖cW w (u * u')‖ = Real.log ‖cW w u‖ + Real.log ‖cW w u'‖ := fun w => by
    rw [map_mul, norm_mul, Real.log_mul (norm_ne_zero_iff.2 (hu.map (cW w)).ne_zero)
      (norm_ne_zero_iff.2 (hu'.map (cW w)).ne_zero)]
  unfold logAbs
  simp only [h1, h2]
  rw [Finset.sum_add_distrib, finsum_add_distrib (support_log_finite u hu) (support_log_finite u' hu')]
  ring

theorem norm_cV_algebraMap (v : InfinitePlace E) (c : E) : ‖cV v (algebraMap E (Ad E) c)‖ = v c := by
  rw [← InfinitePlace.norm_embedding_eq]
  exact congrArg norm (pInf_algebraMap c v)

theorem norm_cW_algebraMap (w : HeightOneSpectrum (𝓞 E)) (c : E) :
    ‖cW w (algebraMap E (Ad E) c)‖ = FinitePlace.mk w c := rfl

theorem logAbs_algebraMap (c : E) (hc : c ≠ 0) : logAbs (algebraMap E (Ad E) c) = 0 := by
  have hprod := prod_abs_eq_one hc
  have hA : (∏ w : InfinitePlace E, w c ^ w.mult) ≠ 0 := left_ne_zero_of_mul_eq_one hprod
  have hB : (∏ᶠ w : FinitePlace E, w c) ≠ 0 := right_ne_zero_of_mul_eq_one hprod
  have hlog := congrArg Real.log hprod
  rw [Real.log_mul hA hB, Real.log_one, Real.log_prod (fun w _ => pow_ne_zero _ ((InfinitePlace.pos_iff.2 hc).ne')),
    Real.log_finprod fun w : FinitePlace E => FinitePlace.pos_iff.2 hc] at hlog
  have hm : ∀ v : InfinitePlace E, v.mult = 2 := fun v =>
    InfinitePlace.mult_isComplex ⟨v, IsTotallyComplex.isComplex v⟩
  unfold logAbs
  simp only [norm_cV_algebraMap, norm_cW_algebraMap]
  simp only [hm] at hlog
  rw [← hlog, ← finsum_comp_equiv (FinitePlace.equivHeightOneSpectrum (K := E)).symm]
  rfl

theorem logAbsBasic : LogAbsBasic := fun _ _ _ _ =>
  ⟨support_log_finite, logAbs_mul, logAbs_algebraMap⟩

end GlobalTheory.CompanionTheory.LogAbs

end
