module

public import Formalism.LocalRingCardinality.AdicCompletionLocal.InstIsAdicCompleteOCSpanSingletonSetCast
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
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
import Mathlib.RingTheory.LocalProperties.Reduced
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemBallOfGaugeLt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.AinfSat

section Coeff

variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R] [CharP R p]

theorem coeff_pow_mul_add (r : ℕ) (w : WittVector p R) (i : ℕ) :
    (((p : WittVector p R) ^ r * w).coeff (i + r)) = (w.coeff i) ^ (p ^ r) := by
  induction r with
  | zero => simp
  | succ r ih =>
    have h : (p : WittVector p R) ^ (r + 1) * w
        = WittVector.verschiebung (WittVector.frobenius ((p : WittVector p R) ^ r * w)) := by
      rw [WittVector.verschiebung_frobenius]; ring
    rw [h, show i + (r + 1) = (i + r).succ by omega, WittVector.verschiebung_coeff_succ,
      WittVector.coeff_frobenius_charP, ih, ← pow_mul, pow_succ]

theorem coeff_pow_mul_lt (n : ℕ) (w : WittVector p R) :
    ∀ j, j < n → ((p : WittVector p R) ^ n * w).coeff j = 0 := by
  induction n with
  | zero => intro j hj; omega
  | succ n ih =>
    intro j hj
    have h : (p : WittVector p R) ^ (n + 1) * w
        = WittVector.verschiebung (WittVector.frobenius ((p : WittVector p R) ^ n * w)) := by
      rw [WittVector.verschiebung_frobenius]; ring
    rw [h]
    cases j with
    | zero => exact WittVector.verschiebung_coeff_zero _
    | succ j =>
      rw [WittVector.verschiebung_coeff_succ, WittVector.coeff_frobenius_charP, ih j (by omega),
        zero_pow hp.out.ne_zero]

theorem coeff_eq_of_dvd {n : ℕ} {u v : WittVector p R} (h : (p : WittVector p R) ^ n ∣ u - v)
    (j : ℕ) (hj : j < n) : u.coeff j = v.coeff j := by
  obtain ⟨w, hw⟩ := h
  have hz : WittVector.truncate n (u - v) = 0 := by
    ext k
    rw [WittVector.coeff_truncate, hw, coeff_pow_mul_lt n w k k.2]
    simp
  have ht : WittVector.truncate n u = WittVector.truncate n v := by
    rw [map_sub, sub_eq_zero] at hz; exact hz
  have := congrArg (TruncatedWittVector.coeff (⟨j, hj⟩ : Fin n)) ht
  simpa [WittVector.coeff_truncate] using this

end Coeff

variable (l : ℕ) [Fact l.Prime]

theorem exists_of_pow_eq (r : ℕ) (d : Cb l) (b : OCb l)
    (h : d ^ (l ^ r) = algebraMap (OCb l) (Cb l) b) : ∃ c : OCb l, algebraMap (OCb l) (Cb l) c = d := by
  refine ⟨(iterateFrobeniusEquiv (OCb l) l r).symm b, ?_⟩
  apply iterateFrobenius_inj (Cb l) l r
  rw [iterateFrobenius_def, iterateFrobenius_def, h, ← map_pow]
  congr 1
  have := (iterateFrobeniusEquiv (OCb l) l r).apply_symm_apply b
  rwa [iterateFrobeniusEquiv_apply, iterateFrobenius_def] at this

theorem mem_range_of_pow_mul (r : ℕ) (y : WCb l)
    (hy : ∀ n : ℕ, ∃ a : Ainf l, (l : WCb l) ^ n ∣ (l : WCb l) ^ r * y - inclW l a) :
    ∃ a : Ainf l, y = inclW l a := by
  have hc : ∀ i, ∃ c : OCb l, algebraMap (OCb l) (Cb l) c = y.coeff i := by
    intro i
    obtain ⟨a, ha⟩ := hy (i + r + 1)
    have he := coeff_eq_of_dvd ha (i + r) (by omega)
    rw [coeff_pow_mul_add] at he
    exact exists_of_pow_eq l r _ _ (by rw [he]; exact WittVector.map_coeff _ _ _)
  choose c hc using hc
  refine ⟨WittVector.mk l c, ?_⟩
  ext i
  rw [show inclW l (WittVector.mk l c) = WittVector.map (algebraMap (OCb l) (Cb l)) (WittVector.mk l c)
    from rfl, WittVector.map_coeff]
  exact (hc i).symm

theorem mem_ideal_of_saturated : ∀ (l : ℕ) [Fact l.Prime] (ι : Ainf l), IsUnit (inclW l ι) →
    ∀ (r : ℕ) (x : WCb l), (∀ n : ℕ, ∃ a : Ainf l,
      (l : WCb l) ^ n ∣ (l : WCb l) ^ r * x - inclW l (ι * a)) →
    ∃ a : Ainf l, x = inclW l (ι * a) := by
  intro l _ ι hu r x hx
  obtain ⟨u, hu⟩ := hu
  obtain ⟨a, ha⟩ := mem_range_of_pow_mul l r (↑u⁻¹ * x) (by
    intro n
    obtain ⟨a, w, hw⟩ := hx n
    refine ⟨a, ↑u⁻¹ * w, ?_⟩
    have : (l : WCb l) ^ r * (↑u⁻¹ * x) - inclW l a
        = ↑u⁻¹ * ((l : WCb l) ^ r * x - inclW l (ι * a)) := by
      rw [map_mul, ← hu, mul_sub]
      rw [← mul_assoc (↑u⁻¹ : WCb l) (↑u) _, Units.inv_mul, one_mul]
      ring
    rw [this, hw]; ring)
  refine ⟨a, ?_⟩
  rw [map_mul, ← ha, ← hu, ← mul_assoc, Units.mul_inv, one_mul]

end GlobalTheory.AinfSat
