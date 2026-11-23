module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASASectionCut
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnTrSmooth
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTSSTr
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedF
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedLocSec
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Sqrt
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

@[expose] public section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

open Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.SSTr

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem radial_section_holds : SARadSec := by
  intro Wp Wq _ _ _ _ _ _ P Bs hpl e he U
  classical
  let g : (Fin P.r → ℂ) × ℂ → (Wq →L[ℂ] Wp) := fun x =>
    (((Real.sqrt (MA.wq P.k x P.TT))⁻¹ : ℝ) : ℂ) • ∑ ρ, MA.ext (U ρ : MA.Qp P.r P.TT → ℂ) x • e ρ x.2
  let φ := (NF.QR P.k P.r Bs.z Bs.z').indicator g
  have hQR : NF.QR P.k P.r Bs.z Bs.z' = MA.Qset P.r P.TT := Set.ext (qr_iff P Bs hpl)
  have hg : ContDiffOn ℝ ∞ g (MA.Qset P.r P.TT) := by
    have hw : ContDiffOn ℝ ∞ (fun x : MA.E P.r => (((Real.sqrt (MA.wq P.k x P.TT))⁻¹ : ℝ) : ℂ))
        (MA.Qset P.r P.TT) := by
      refine Formalism.FourierDecayAlt.P.NFRadRedLocSec.cd_ofReal ?_
      refine ContDiffOn.inv ?_ fun x hx => (Real.sqrt_pos.2 (Formalism.FourierDecayAlt.P.CutMP.En.wq_pos hx)).ne'
      exact (Formalism.FourierDecayAlt.P.CutMP.En.wq_contDiff P.k P.r P.TT).contDiffOn.sqrt fun x hx =>
        (Formalism.FourierDecayAlt.P.CutMP.En.wq_pos hx).ne'
    refine hw.smul (ContDiffOn.sum fun ρ _ => ?_)
    have hF : ContDiffOn ℝ ∞ (MA.ext (U ρ : MA.Qp P.r P.TT → ℂ)) (MA.Qset P.r P.TT) := (U ρ).2
    have he' : ContDiffOn ℝ ∞ (fun x : MA.E P.r => e ρ x.2) (MA.Qset P.r P.TT) :=
      (he.1 ρ).comp contDiff_snd.contDiffOn fun x hx => hx.2
    exact hF.smul he'
  have hφ : φ ∈ NF.RadSec P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' := by
    refine ⟨?_, fun x hx => ?_, fun x hx => ?_⟩
    · rw [hQR]
      exact hg.congr fun x hx => by simp only [φ, hQR, Set.indicator_of_mem hx]
    · simp only [φ, Set.indicator_of_mem hx, g]
      have hx' : P.TT < Complex.normSq x.2 := ((qr_iff P Bs hpl x).1 hx).2
      have h1 := fib_sum_smul P Bs x.2 (fun ρ => MA.ext (U ρ : MA.Qp P.r P.TT → ℂ) x) (fun ρ => e ρ x.2) fun ρ => (he.2 x.2 hx').1 ρ
      by_cases hne : Nonempty (M.Ty P)
      · obtain ⟨ρ0⟩ := hne
        intro p hp
        have h3 := fib_sum_smul P Bs x.2 (fun ρ => if ρ = ρ0 then (((Real.sqrt (MA.wq P.k x P.TT))⁻¹ : ℝ) : ℂ) else 0)
          (fun _ => ∑ ρ, MA.ext (U ρ : MA.Qp P.r P.TT → ℂ) x • e ρ x.2) (fun _ => h1) p hp
        simp only [ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h3
        exact h3
      · have : ∑ ρ, MA.ext (U ρ : MA.Qp P.r P.TT → ℂ) x • e ρ x.2 = 0 := by
          rw [Finset.univ_eq_empty_iff.2 (not_nonempty_iff.1 hne)]; simp
        rw [this, smul_zero]
        intro p hp
        ext v
        simp
    · simp [φ, Set.indicator_of_notMem hx]
  obtain ⟨Φ, hΦ, hrad⟩ := Formalism.FourierDecayAlt.P.radical_reduction_surjective Wp Wq P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π'
    (radBase P Bs hpl) φ hφ
  refine ⟨Φ, hΦ, fun q => ?_⟩
  have hq : q.1 ∈ NF.QR P.k P.r Bs.z Bs.z' := (qr_iff P Bs hpl q.1).2 q.2
  have h := congrFun hrad q.1
  simp only [NF.radR, Set.indicator_of_mem hq, φ] at h
  rw [h]
  simp only [g]
  congr 1
  refine Finset.sum_congr rfl fun ρ _ => ?_
  congr 1
  simp [MA.ext, q.2]

end Formalism.FourierDecayAlt.P.CutMP.JA.SA
