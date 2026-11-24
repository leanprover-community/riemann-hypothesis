module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedK1BlockDecomposition
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

namespace GlobalTheory.CongOne

open GlobalTheory.TopStep GlobalTheory.BlockDecompositionK1

theorem mem_glint_prinCong_of_cols {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E))
    {n : ℕ} (D : ℕ) (k : Sp E n ≃ₗ[E] Sp E n) (hD : 1 ≤ D)
    (h : ∀ s l, IntAt P (((qOf P : E) ^ D)⁻¹ * (k (Pi.single s (1 : E)) l - (Pi.single s (1 : E) : Sp E n) l))) :
    ∃ hk : k ∈ GLint E n P, (⟨k, hk⟩ : GLint E n P) ∈ GlobalTheory.TopStep.prinCong n P D := by
  classical
  have hq : ((qOf P : ℕ) : E) ≠ 0 := qOf_ne_zero
  have hqD : ((qOf P : E) ^ D) ≠ 0 := pow_ne_zero _ hq
  have hsingle : ∀ s l, IntAt P ((Pi.single s (1 : E) : Sp E n) l) := fun s l =>
    mem_stdAt.1 (single_mem_stdAt (P := P) s) l
  have hent : ∀ l s, IntAt P (k (Pi.single s (1 : E)) l) := fun l s => by
    have e : k (Pi.single s (1 : E)) l = (qOf P : E) ^ D * (((qOf P : E) ^ D)⁻¹ *
        (k (Pi.single s (1 : E)) l - (Pi.single s (1 : E) : Sp E n) l)) + (Pi.single s (1 : E) : Sp E n) l := by
      field_simp
      ring
    rw [e]
    exact ((intAt_pow (intAt_nat (qOf P)) D).mul (h s l)).add (hsingle s l)
  let A : Matrix (Fin n) (Fin n) E := Matrix.of fun l s => k (Pi.single s (1 : E)) l
  have hA : ∀ l s, IntAt P (A l s) := hent
  have hAx : ∀ x, A.mulVec x = k x := fun x => by
    funext l
    refine Eq.trans ?_ (apply_eq_sum (k : Sp E n →ₗ[E] Sp E n) x l).symm
    show ∑ s, A l s * x s = _
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [mul_comm]
    rfl
  have hred : A.map (redP P) = 1 := by
    ext l s
    rw [Matrix.map_apply]
    have h0 : redP P (k (Pi.single s (1 : E)) l - (Pi.single s (1 : E) : Sp E n) l) = 0 := by
      obtain ⟨c, rfl⟩ : ∃ c, D = c + 1 := ⟨D - 1, by omega⟩
      exact reduction_eq_zero_of_integral_absNorm_pow_inv_mul (h s l)
    rw [reduction_sub (hent l s) (hsingle s l), sub_eq_zero] at h0
    show redP P (k (Pi.single s (1 : E)) l) = _
    rw [h0, Matrix.one_apply, Pi.single_apply]
    split_ifs
    · exact reduction_one₂
    · exact reduction_zero
  have hdet : IsUnit (redP P A.det) := by
    rw [(det_int hA).2, hred, Matrix.det_one]
    exact isUnit_one
  obtain ⟨j, hj⟩ := exists_glint_of_matrix A hA hdet
  have hjk : j.1 = k := LinearEquiv.ext fun x => (hj x).trans (hAx x)
  have hk : k ∈ GLint E n P := hjk ▸ j.2
  refine ⟨hk, fun x hx => ?_⟩
  refine mem_stdAt.2 fun l => ?_
  have e1 := apply_eq_sum (k : Sp E n →ₗ[E] Sp E n) x l
  have e2 := apply_eq_sum (LinearMap.id : Sp E n →ₗ[E] Sp E n) x l
  have e : (((qOf P : E) ^ D)⁻¹ • (k x - x)) l = ∑ s, x s * (((qOf P : E) ^ D)⁻¹ *
      (k (Pi.single s (1 : E)) l - (Pi.single s (1 : E) : Sp E n) l)) := by
    rw [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    change ((qOf P : E) ^ D)⁻¹ * ((k : Sp E n →ₗ[E] Sp E n) x l - (LinearMap.id : Sp E n →ₗ[E] Sp E n) x l) = _
    rw [e1, e2, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [LinearMap.id_apply, LinearEquiv.coe_coe]
    ring
  rw [e]
  exact intAt_sum _ fun s _ => (mem_stdAt.1 hx s).mul (h s l)

end GlobalTheory.CongOne
