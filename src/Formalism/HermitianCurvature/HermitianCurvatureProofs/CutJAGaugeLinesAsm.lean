module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGaugeLinesCut
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreKLExistsOf
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreKLIsoAlg
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreKLLieGrp
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DiagonalTransferAction
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DifferentialOperatorBracket
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedA
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
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
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.PRho.GL

noncomputable section

namespace AsmPf

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

variable [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem hsVec_smul (c : ℂ) (A : Wq →L[ℂ] Wp) : B.hsVec (c • A) = c • B.hsVec A := by
  ext i
  simp [B.hsVec]

theorem base (hR : GLRight) (hLf : GLLeft) (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (hk : 2 ≤ P.k)
    (hF : Gauge.IsFrameB P Bs e)
    (hQQ : ∀ (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)), Gauge.FamR P Bs Dc Φ →
      ∀ (Y : ℝ) (a b : Fin 2) (ρ : M.Ty P),
        MA.toSm P (Gauge.rawR P Bs.μsec e (Q.QL P.k P.r Bs.z Bs.z' (Fin.last P.r) (Y : ℂ) a b Φ) ρ) =
          MA.actA P (MA.QQr P (MA.DQ P) (Y : ℂ) a b) (fun ρ' => MA.toSm P (Gauge.rawR P Bs.μsec e Φ ρ')) ρ)
    (ζ : ℂ) (hζ : P.TT < Complex.normSq ζ) (ρ : M.Ty P) (Fr : Fin (P.k - 1) → Fin (2 * P.r + P.k + 1) → ℂ)
    (hFr : Q.IsFrameOf P.k P.r [Bs.z, SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ] Fr) (w : ℂ) (x : Wq) :
    Q.capRep P.k P.r Bs.π Fr w (e ρ ζ x) = M.xC P ρ (w - ((P.k : ℂ) - 2) / 2) • e ρ ζ x := by
  obtain ⟨hOK, hz, hz', hTz, hTz', -, -⟩ := id hpl
  have hζ' : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq ζ := by
    rw [hTz, hTz']; exact hζ
  obtain ⟨hFr', hpass⟩ := hLf Wp Wq P Bs hpl hk ζ hζ Fr hFr
  have hq : ((fun _ => (1 : ℂ)), ζ) ∈ NF.QR P.k P.r Bs.z Bs.z' := ⟨fun _ => one_ne_zero, hζ'⟩
  obtain ⟨-, hg, hG⟩ := Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' Bs.sec hq
  have hEx := Gauge.GC.lie_existence_of_iso_group Gauge.GC.KLIso.lie_algebra_isomorphism_holds Gauge.GC.lie_group_realization
  obtain ⟨E, hEfib, hEeig, hE0⟩ := hEx Wp Wq P Bs.z Bs.z' Bs.π Bs.π' hpl hk _ hg hG.ne' _ hFr' ρ
  have hEF : E ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ :=
    fun p hp => hEfib p.1 hp.1 p.2 hp.2.1 hp.2.2
  have hgl' := (Formalism.FourierDecayAlt.P.frame_general_linear Wq P.k P.r (P.k - 1) Bs.z' Bs.π'
    (fun a => (NF.muZ P.k P.r Bs.μsec ζ)⁻¹ *ᵥ Fr a) ⟨Bs.π'_rep, Bs.π'_cont⟩
    (Formalism.FourierDecayAlt.P.Qx8.frame_sub hFr' (by simp))).2
  have hEc : ∀ (Y : ℂ) (v : Wq), E (Q.capRep P.k P.r Bs.π'
      (fun a => (NF.muZ P.k P.r Bs.μsec ζ)⁻¹ *ᵥ Fr a) (Y + ((P.k : ℂ) - 2) / 2) v) = M.xC P ρ Y • E v := by
    intro Y v
    rw [hgl']
    exact hEeig Y v
  obtain ⟨Y₀, hY₀⟩ := Formalism.FourierDecayAlt.P5.Kfp.sep_real hOK
  have horth : ∀ σ, σ ≠ ρ → inner ℂ (B.hsVec (e σ ζ)) (B.hsVec E) = 0 := by
    intro σ hσ
    have h := hR Wp Wq P Bs e hpl hk hF hQQ ζ hζ _ hFr' E hEF Y₀ (M.xC P ρ (Y₀ : ℂ) • E)
      (fun v => by rw [hEc, ContinuousLinearMap.smul_apply]) σ
    rw [hsVec_smul, inner_smul_right] at h
    have h2 : (M.xC P ρ (Y₀ : ℂ) - M.xC P σ (Y₀ : ℂ)) * inner ℂ (B.hsVec (e σ ζ)) (B.hsVec E) = 0 := by
      rw [sub_mul, h, sub_self]
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact absurd (hY₀ (sub_eq_zero.1 h3)).symm hσ
    · exact h3
  have hexp := (hF.2 ζ hζ).2.2 E hEF
  have hE1 : E = inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec E) • e ρ ζ := by
    conv_lhs => rw [hexp]
    rw [Finset.sum_eq_single ρ (fun σ _ hσ => by rw [horth σ hσ, zero_smul])
      (fun h => absurd (Finset.mem_univ ρ) h)]
  have hc0 : inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec E) ≠ 0 := by
    intro h0
    apply hE0
    rw [hE1, h0, zero_smul]
  have heig : ∀ (Y : ℂ) (v : Wq), e ρ ζ (Q.capRep P.k P.r Bs.π'
      (fun a => (NF.muZ P.k P.r Bs.μsec ζ)⁻¹ *ᵥ Fr a) (Y + ((P.k : ℂ) - 2) / 2) v) = M.xC P ρ Y • e ρ ζ v := by
    intro Y v
    have h := hEc Y v
    generalize hcdef : inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec E) = c at hE1 hc0
    rw [hE1] at h
    simp only [ContinuousLinearMap.smul_apply] at h
    rw [smul_comm (M.xC P ρ Y) c] at h
    exact smul_right_injective Wp hc0 h
  rw [hpass (e ρ ζ) ((hF.2 ζ hζ).1 ρ) w x]
  have hw : w = (w - ((P.k : ℂ) - 2) / 2) + ((P.k : ℂ) - 2) / 2 := by ring
  conv_lhs => rw [hw]
  exact heig _ x

end AsmPf

theorem gaugeLines_of_cut : GaugeLinesOfCut := by
  intro hR hL Cc E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ v e hH hk ζ hζ ρ Fr hFr w x
  obtain ⟨hB, hFrame, -, hQQ⟩ := hH
  have hpl := (hB.1.2.2.2.1.2 v).2.2.2.1
  exact AsmPf.base hR hL (D.parOf S v) (T v).base e hpl hk hFrame hQQ ζ hζ ρ Fr hFr w x

end

end Formalism.FourierDecayAlt.P.CutMP.JA.PRho.GL
