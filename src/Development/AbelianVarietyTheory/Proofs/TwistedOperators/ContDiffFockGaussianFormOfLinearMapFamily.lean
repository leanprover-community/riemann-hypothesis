module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockFormApply
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

open MeasureTheory

namespace GlobalTheory.FockFamily

theorem fockForm_family_contDiff {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (J : ℝ → (V × V) →ₗ[ℝ] (V × V)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => GlobalTheory.FockFamily.blockB (J t)) →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => GlobalTheory.FockFamily.blockD (J t)) →
    (∀ t, IsUnit (GlobalTheory.FockFamily.blockB (J t))) →
    (∀ x y, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => GlobalTheory.FockFamily.fockForm β (J t) x y) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × V => GlobalTheory.FockFamily.fockForm β (J p.1) p.2 p.2) := by
  intro hB hD hU

  let β₁ : V →ₗ[ℝ] (V →L[ℝ] ℝ) :=
    (LinearMap.toContinuousLinearMap : (V →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (V →L[ℝ] ℝ)).toLinearMap ∘ₗ β
  let βc : V →L[ℝ] V →L[ℝ] ℝ := LinearMap.toContinuousLinearMap β₁
  have hβc : ∀ x y, βc x y = β x y := fun x y => rfl

  have hC : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => Ring.inverse (blockB (J t))) := by
    rw [contDiff_iff_contDiffAt]
    intro t
    exact (contDiffAt_ringInverse ℝ (hU t).unit).comp t hB.contDiffAt
  have hDC : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun t => (blockD (J t)).comp (Ring.inverse (blockB (J t)))) := hD.clm_comp hC
  have hπ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun _ : ℝ × V => (Real.pi : ℂ) * Complex.I) := contDiff_const
  have hπ' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun _ : ℝ => (Real.pi : ℂ) * Complex.I) := contDiff_const
  have hR : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ},
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f →
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun e => ((f e : ℝ) : ℂ)) :=
    fun hf => Complex.ofRealCLM.contDiff.comp hf
  constructor
  · intro x y
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun t => Real.pi * βc x (Ring.inverse (blockB (J t)) y)) :=
      contDiff_const.mul (contDiff_const.clm_apply (hC.clm_apply contDiff_const))
    have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun t => βc x (((blockD (J t)).comp (Ring.inverse (blockB (J t)))) y)) :=
      contDiff_const.clm_apply (hDC.clm_apply contDiff_const)
    have := (hR h1).add (hπ'.mul (hR h2))
    simpa only [fockForm_apply, hβc, ContinuousLinearMap.comp_apply] using this
  · have hCp : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × V => Ring.inverse (blockB (J p.1)) p.2) :=
      (hC.comp contDiff_fst).clm_apply contDiff_snd
    have hDCp : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × V => ((blockD (J p.1)).comp (Ring.inverse (blockB (J p.1)))) p.2) :=
      (hDC.comp contDiff_fst).clm_apply contDiff_snd
    have hβp : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × V => βc p.2) :=
      βc.contDiff.comp contDiff_snd
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × V => Real.pi * βc p.2 (Ring.inverse (blockB (J p.1)) p.2)) :=
      contDiff_const.mul (hβp.clm_apply hCp)
    have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × V => βc p.2 (((blockD (J p.1)).comp (Ring.inverse (blockB (J p.1)))) p.2)) :=
      hβp.clm_apply hDCp
    have := (hR h1).add (hπ.mul (hR h2))
    simpa only [fockForm_apply, hβc, ContinuousLinearMap.comp_apply] using this

end GlobalTheory.FockFamily
