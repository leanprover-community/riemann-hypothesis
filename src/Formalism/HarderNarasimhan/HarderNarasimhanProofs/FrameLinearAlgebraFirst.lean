module

public import Formalism.HarderNarasimhan.StatementFrameF
public import Formalism.CorankShare.CorankShareProofs.SumNormSqLeHilbertSchmidt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.Trace
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

/-!
# Linear-Algebraic Corank Bound (`FrameLA1`) via Centered Frame Variance

Proves `frame_linear_algebra_first : FrameLA1` by combining:
1. The near-isometry lower bound on `tr(frQ c B)` and upper bound on the restricted energy `tW`,
2. The coordinate-free centered variance identity `hs2_frQ_centered` (`hs2 (Q - s I) = tr(Q^2) - t^2 / D`),
3. The traceless subspace projection bound `subspace_projection_bound` (`|tW - s w| ≤ √(w (D - w) / D) · √(hs2 (Q - s I))`).
-/

noncomputable section

namespace Formalism.HN

namespace PframeLA1

open Finset Module LinearMap Formalism.CorankShareLayerCake.FR Formalism.CorankShareLayerCake.FR.Pgsn2pfrla
open scoped InnerProductSpace

lemma final_real1 (D R w e ε η t X tW : ℝ) (hD : 0 < D) (hR : 0 < R) (he0 : 0 ≤ e) (he : e ≤ 1 / 4)
    (hε : 0 ≤ ε) (hw0 : 0 ≤ w) (hwD : w ≤ D) (ht : R * (1 - √e) ≤ t) (hX0 : 0 ≤ X)
    (hX : X ≤ η * t ^ 2 / D) (hlow : t / D * w - √w * √X ≤ tW)
    (hup : tW ≤ ε * R + R * √(ε * e)) : w ≤ (η + 4 * ε + 4 * √e) * D := by
  have hse0 : 0 ≤ √e := Real.sqrt_nonneg e
  have hse : √e ≤ 1 / 2 :=
    (Real.sqrt_le_sqrt he).trans_eq (by rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)])
  have hRt : R ≤ 2 * t := by nlinarith
  have htpos : 0 < t := by linarith
  have hη : 0 ≤ η := by
    have h1 : 0 ≤ η * t ^ 2 := by
      have := mul_nonneg (hX0.trans hX) hD.le
      rwa [div_mul_cancel₀ _ hD.ne'] at this
    exact nonneg_of_mul_nonneg_left h1 (by positivity)
  by_cases hε4 : 1 / 4 ≤ ε
  · nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ η + 4 * ε + 4 * √e - 1) hD.le]
  push Not at hε4
  set q := √(ε * e)
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hqe : q ≤ √e := Real.sqrt_le_sqrt (by nlinarith)
  set y := D / t * √X
  have hy2 : y ^ 2 ≤ η * D := by
    have h1 : y ^ 2 = D ^ 2 * X / t ^ 2 := by rw [mul_pow, div_pow, Real.sq_sqrt hX0]; ring
    rw [h1, div_le_iff₀ (by positivity)]
    nlinarith [(le_div_iff₀ hD).mp hX]
  have hkey : t * (w - √w * y) ≤ t * (2 * D * (ε + q)) := by
    have h1 : t * w - D * (√w * √X) ≤ D * (R * (ε + q)) := by
      have hmul := mul_le_mul_of_nonneg_left (show t / D * w - √w * √X ≤ R * (ε + q) by linarith) hD.le
      have hDt : D * (t / D * w - √w * √X) = t * w - D * (√w * √X) := by field_simp [hD.ne']
      linarith
    have hyt : t * (√w * y) = D * (√w * √X) := by simp only [y]; field_simp [htpos.ne']
    nlinarith [mul_le_mul_of_nonneg_left (show R * (ε + q) ≤ 2 * t * (ε + q) by nlinarith) hD.le]
  have hmain : w - √w * y ≤ 2 * D * (ε + q) := le_of_mul_le_mul_left hkey htpos
  have hamgm : √w * y ≤ (w + y ^ 2) / 2 := by nlinarith [sq_nonneg (√w - y), Real.sq_sqrt hw0]
  nlinarith [mul_le_mul_of_nonneg_left hqe hD.le]

end PframeLA1

open Finset Module LinearMap Formalism.CorankShareLayerCake.FR Formalism.CorankShareLayerCake.FR.Pgsn2pfrla PframeLA1
open scoped InnerProductSpace

theorem frame_linear_algebra_first : FrameLA1 := by
  intro ι _ V _ _ _ H _ _ _ B c Nτ e η ε hc hd hK he0 he hη hQ hN
  set W : Submodule ℂ H := (⨆ i, (Nτ i).map (B i))ᗮ
  have hwD : (finrank ℂ W : ℝ) ≤ (finrank ℂ H : ℝ) := by exact_mod_cast Submodule.finrank_le W
  by_cases hD0 : finrank ℂ H = 0
  · have h0 : finrank ℂ W = 0 := by have := Submodule.finrank_le W; omega
    simp [h0, hD0]
  have hD : 0 < (finrank ℂ H : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hD0
  have hR : 0 < ∑ i, (finrank ℂ (V i) : ℝ) := by rw [← Nat.cast_sum]; exact_mod_cast hd
  have hnk : ∀ i, (finrank ℂ (Nτ i) : ℝ) ≤ finrank ℂ (V i) := fun i => by
    exact_mod_cast Submodule.finrank_le (Nτ i)
  have hε : 0 ≤ ε := by
    have hKnn : 0 ≤ ∑ i, ((finrank ℂ (V i) : ℝ) - finrank ℂ (Nτ i)) :=
      Finset.sum_nonneg fun i _ => sub_nonneg.mpr (hnk i)
    exact nonneg_of_mul_nonneg_left (hKnn.trans hN) hR
  -- Lower bound on total frame trace `Re tr(frQ c B)`
  have hfull : ∀ i, (finrank ℂ (V i) : ℝ) - √(finrank ℂ (V i) : ℝ) * √(hs2 (frK (c i) (B i) - LinearMap.id))
      ≤ c i * ∑ m, ‖B i (stdOrthonormalBasis ℂ (V i) m)‖ ^ 2 := fun i => by
    have h := fam_bound (c i) (B i) (stdOrthonormalBasis ℂ (V i)).orthonormal
    simp only [Fintype.card_fin] at h
    linarith [(abs_le.mp h).1]
  have hCS1 : ∑ i, √(finrank ℂ (V i) : ℝ) * √(hs2 (frK (c i) (B i) - LinearMap.id))
      ≤ (∑ i, (finrank ℂ (V i) : ℝ)) * √e := by
    calc _ ≤ √(∑ i, (finrank ℂ (V i) : ℝ)) * √(∑ i, hs2 (frK (c i) (B i) - LinearMap.id)) :=
          Real.sum_sqrt_mul_sqrt_le Finset.univ (fun _ => Nat.cast_nonneg _) (fun _ => hs2_nonneg _)
      _ ≤ √(∑ i, (finrank ℂ (V i) : ℝ)) * √(e * ∑ i, (finrank ℂ (V i) : ℝ)) :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hK) (Real.sqrt_nonneg _)
      _ = (∑ i, (finrank ℂ (V i) : ℝ)) * √e := by
          rw [Real.sqrt_mul he0]
          linear_combination √e * Real.mul_self_sqrt hR.le
  have ht : (∑ i, (finrank ℂ (V i) : ℝ)) * (1 - √e) ≤ (LinearMap.trace ℂ H (frQ c B)).re := by
    rw [tQ_eq c B]
    have h2 := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hfull i
    rw [Finset.sum_sub_distrib] at h2
    nlinarith [hCS1]
  -- Upper bound on restricted frame energy `tW = Re tr(P_W frQ c B)`
  set b := stdOrthonormalBasis ℂ W
  set g : Fin (finrank ℂ W) → H := fun l => (b l : H)
  have hg : Orthonormal ℂ g := b.orthonormal.comp_linearIsometry W.subtypeₗᵢ
  set tW : ℝ := ∑ l, (⟪g l, frQ c B (g l)⟫_ℂ).re
  have htW : tW = ∑ i, c i * ∑ l, ‖adjoint (B i) (g l)‖ ^ 2 := by
    simp only [tW, re_inner_Q, Finset.mul_sum]
    exact Finset.sum_comm
  have hWi : ∀ i, c i * ∑ l, ‖adjoint (B i) (g l)‖ ^ 2 ≤
      ((finrank ℂ (V i) : ℝ) - finrank ℂ (Nτ i)) +
        √((finrank ℂ (V i) : ℝ) - finrank ℂ (Nτ i)) * √(hs2 (frK (c i) (B i) - LinearMap.id)) := fun i => by
    have hperp : ∀ l, ∀ n ∈ Nτ i, ⟪B i n, g l⟫_ℂ = 0 := fun l n hn =>
      (Submodule.mem_orthogonal _ _).mp (b l).2 _
        (Submodule.mem_iSup_of_mem i (Submodule.mem_map_of_mem hn))
    have h1 := W_upper (B i) (Nτ i) hg hperp
    have hf : Orthonormal ℂ (fun m => ((stdOrthonormalBasis ℂ (Nτ i)ᗮ m : (Nτ i)ᗮ) : V i)) :=
      (stdOrthonormalBasis ℂ (Nτ i)ᗮ).orthonormal.comp_linearIsometry (Nτ i)ᗮ.subtypeₗᵢ
    have h2 := fam_bound (c i) (B i) hf
    simp only [Fintype.card_fin] at h2
    have hk : (finrank ℂ (Nτ i)ᗮ : ℝ) = finrank ℂ (V i) - finrank ℂ (Nτ i) := by
      have := Submodule.finrank_add_finrank_orthogonal (Nτ i)
      rw [eq_sub_iff_add_eq]
      exact_mod_cast (by omega : finrank ℂ (Nτ i)ᗮ + finrank ℂ (Nτ i) = finrank ℂ (V i))
    rw [hk] at h2
    linarith [(abs_le.mp h2).2, mul_le_mul_of_nonneg_left h1 (hc i).le]
  have hup : tW ≤ ε * (∑ i, (finrank ℂ (V i) : ℝ)) + (∑ i, (finrank ℂ (V i) : ℝ)) * √(ε * e) := by
    rw [htW]
    have h1 := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hWi i
    rw [Finset.sum_add_distrib] at h1
    have hCS : ∑ i, √((finrank ℂ (V i) : ℝ) - finrank ℂ (Nτ i)) * √(hs2 (frK (c i) (B i) - LinearMap.id))
        ≤ (∑ i, (finrank ℂ (V i) : ℝ)) * √(ε * e) := by
      calc _ ≤ √(∑ i, ((finrank ℂ (V i) : ℝ) - finrank ℂ (Nτ i))) *
              √(∑ i, hs2 (frK (c i) (B i) - LinearMap.id)) :=
            Real.sum_sqrt_mul_sqrt_le Finset.univ (fun i => sub_nonneg.mpr (hnk i)) (fun _ => hs2_nonneg _)
        _ ≤ √(ε * ∑ i, (finrank ℂ (V i) : ℝ)) * √(e * ∑ i, (finrank ℂ (V i) : ℝ)) :=
            mul_le_mul (Real.sqrt_le_sqrt hN) (Real.sqrt_le_sqrt hK) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
        _ = (∑ i, (finrank ℂ (V i) : ℝ)) * √(ε * e) := by
            rw [← Real.sqrt_mul (mul_nonneg hε hR.le),
              show ε * (∑ i, (finrank ℂ (V i) : ℝ)) * (e * ∑ i, (finrank ℂ (V i) : ℝ)) =
                ε * e * (∑ i, (finrank ℂ (V i) : ℝ)) ^ 2 by ring,
              Real.sqrt_mul (mul_nonneg hε he0), Real.sqrt_sq hR.le]
            ring
    linarith
  -- Centered frame variance and traceless subspace projection lower bound on `tW`
  set A : H →ₗ[ℂ] H :=
    frQ c B - (((LinearMap.trace ℂ H (frQ c B)).re / (finrank ℂ H : ℝ) : ℝ) : ℂ) • LinearMap.id
  have hlow : (LinearMap.trace ℂ H (frQ c B)).re / (finrank ℂ H : ℝ) * (finrank ℂ W : ℝ)
      - √(finrank ℂ W : ℝ) * √(hs2 A) ≤ tW := by
    have hproj := (abs_le.mp (subspace_projection_bound (adjoint_frQ c B) W hD0)).1
    have hfac : √((finrank ℂ W : ℝ) * ((finrank ℂ H : ℝ) - finrank ℂ W) / (finrank ℂ H : ℝ))
        ≤ √(finrank ℂ W : ℝ) := by
      refine Real.sqrt_le_sqrt ?_
      rw [div_le_iff₀ hD]
      nlinarith [Nat.cast_nonneg (α := ℝ) (finrank ℂ W)]
    linarith [mul_le_mul_of_nonneg_right hfac (Real.sqrt_nonneg (hs2 A))]
  have hX : hs2 A ≤ η * (LinearMap.trace ℂ H (frQ c B)).re ^ 2 / (finrank ℂ H : ℝ) := by
    rw [hs2_frQ_centered c B hD0]
    linarith [show (1 + η) * (LinearMap.trace ℂ H (frQ c B)).re ^ 2 / (finrank ℂ H : ℝ) =
      (LinearMap.trace ℂ H (frQ c B)).re ^ 2 / (finrank ℂ H : ℝ) +
        η * (LinearMap.trace ℂ H (frQ c B)).re ^ 2 / (finrank ℂ H : ℝ) by ring]
  exact final_real1 _ _ _ e ε η _ _ tW hD hR he0 he hε (Nat.cast_nonneg _) hwD ht
    (hs2_nonneg _) hX hlow hup

end Formalism.HN
