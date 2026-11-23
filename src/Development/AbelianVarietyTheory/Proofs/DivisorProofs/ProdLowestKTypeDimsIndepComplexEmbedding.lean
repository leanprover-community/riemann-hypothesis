module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OneMeasureSizes
public import Development.AbelianVarietyTheory.Counterexamples.TwistSurvey.ConjModelCast
public import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.ParabolicAtStandardWeylElement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.DimProdLab

theorem lab_spec {D : D7} (σ : D.what₂.LL →+* ℂ) (ρ : D.what₂.Tau) :
    labE σ (lab σ ρ) = tauE D ρ ∨ labE σ (lab σ ρ) = (starRingEnd ℂ).comp (tauE D ρ) := by
  unfold lab; rw [dite_eq_left (GlobalTheory.ConjReading.lab_exists σ ρ)]; exact (GlobalTheory.ConjReading.lab_exists σ ρ).choose_spec

theorem lab_injective {D : D7} (σ : D.what₂.LL →+* ℂ) : Function.Injective (lab σ : D.what₂.Tau → D.what₂.Tau) := by
  intro ρ ρ' h
  have cc : ∀ f : D.host.E →+* ℂ, (starRingEnd ℂ).comp ((starRingEnd ℂ).comp f) = f := GlobalTheory.ConjReading.conj_conj
  rcases lab_spec σ ρ with h1 | h1 <;> rcases lab_spec σ ρ' with h2 | h2 <;> rw [h] at h1
  · exact Formalism.IndefR.Fock.KV.tauE_injective (h1.symm.trans h2)
  · exact absurd (h1.symm.trans h2) (Formalism.IndefR.Fock.KV.tauE_ne_conj _ _)
  · exact absurd (h2.symm.trans h1) (Formalism.IndefR.Fock.KV.tauE_ne_conj _ _)
  · have e := congrArg (fun f => (starRingEnd ℂ).comp f) (h1.symm.trans h2)
    simp only [cc] at e
    exact Formalism.IndefR.Fock.KV.tauE_injective e

theorem dimK_congr {R : Ranks} (hc : HCParam R) {a b : ℕ × ℕ} (e : a = b) :
    dimK a.1 a.2 (Formalism.L2.NTheta.kapW hc a.1 a.2) = dimK b.1 b.2 (Formalism.L2.NTheta.kapW hc b.1 b.2) := by
  subst e; rfl

theorem prod_dims (D : D7) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) :
    (∏ ρ, ((dimK _ _ (kapAt (Wc D i) σ ρ) : ℚ) : ℂ)) = ((∏ τ, GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt D i τ : ℝ) : ℂ) := by
  set s := D.R.sigW ((i : ℕ) + 1)
  let hd : D.what₂.Tau → ℚ := fun τ => dimK s.1 s.2 (Formalism.L2.NTheta.kapW (D.hc τ) s.1 s.2)
  have h1 : ∀ ρ, dimK _ _ (kapAt (Wc D i) σ ρ) = hd (lab σ ρ) := fun ρ =>
    dimK_congr (D.hc (lab σ ρ)) (Formalism.IndefR.Fock.KV.sig_Wc i ρ)
  have h2 : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt D i τ = ((hd τ : ℚ) : ℝ) := fun τ =>
    congrArg (fun q : ℚ => (q : ℝ)) (dimK_congr (D.hc τ) (Formalism.IndefR.Fock.KV.sig_Wc i τ))
  have hb : Function.Bijective (lab σ : D.what₂.Tau → D.what₂.Tau) := (lab_injective σ).bijective_of_finite
  simp only [h1, h2]
  refine (Equiv.prod_comp (Equiv.ofBijective _ hb) (fun τ => ((hd τ : ℚ) : ℂ))).trans ?_
  push_cast
  rfl

end GlobalTheory.DimProdLab
