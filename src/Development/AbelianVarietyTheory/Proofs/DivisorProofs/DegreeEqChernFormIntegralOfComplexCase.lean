module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ArBirational
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCoordsBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConjFsBasisOfUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyHomologyEquiv
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AnalyticWeightLinearComb
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.CechPic GlobalTheory.QCoh

namespace GlobalTheory.ChernDegreeBaseChange

theorem exists_baseChange {F E : Type} [Field F] [Field E] (ρ : F →+* E) (Y : Var F) :
    ∃ (Y' : Var E) (r : Y'.X ⟶ Y.X), Y'.dim = Y.dim ∧ IsPullback r Y'.str Y.str (spMap ρ) := by
  have H := IsPullback.of_hasPullback Y.str (spMap ρ)
  generalize Limits.pullback.fst Y.str (spMap ρ) = r at H
  generalize Limits.pullback.snd Y.str (spMap ρ) = q at H
  have hs : SmoothOfRelativeDimension Y.dim q :=
    have := smoothOfRelativeDimension_isStableUnderBaseChange Y.dim
    MorphismProperty.of_isPullback H Y.smooth_str
  have hg : GeometricallyIntegral q :=
    MorphismProperty.of_isPullback (P := @GeometricallyIntegral) H Y.geometricallyIntegral_str
  have hc : GeometricallyConnected q :=
    ⟨fun _ _ y _ fst snd h =>
      have := GeometricallyIntegral.geometrically_isIntegral (f := q) y fst snd h
      inferInstance⟩
  obtain ⟨Y', e, hd, he⟩ := Var.exists_iso q Y.dim (ProjSpace.isProjOver_of_isPullback_spMap ρ H Y.isProjOver)
  refine ⟨Y', e.inv ≫ r, hd, ?_⟩
  refine H.of_iso e (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp
  · simpa using he.symm
  · simp
  · simp

theorem chernDegree_of_complex (h : GlobalTheory.Published.ChernDegreeComplex) : GlobalTheory.Published.ChernDegree := by
  intro F _ Y σ Δ L r hr φ hφ
  obtain ⟨Y', π, hd, H⟩ := exists_baseChange σ Y
  have := CxPts.compactSpace (RingHom.id ℂ) Y'.isProjOver
  have := CxPts.t2Space_cxPts_of_isProjOver σ Y.isProjOver
  have := CxPts.secondCountableTopology_of_isProjOver σ Y.isProjOver
  have := CxPts.secondCountableTopology_of_isProjOver (RingHom.id ℂ) Y'.isProjOver
  obtain ⟨m, hm, hb⟩ : ∃ m : CxPts Y'.str (RingHom.id ℂ) → CxPts Y.str σ, (∀ z, (m z).1 = z.1 ≫ π) ∧
      Function.Bijective m := ⟨bcMap H.w (RingHom.id ℂ), fun _ => rfl, bijective_bcMap H _⟩
  let Φ : CxPts Y'.str (RingHom.id ℂ) ≃ₜ CxPts Y.str σ :=
    Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective m hb) (continuous_of_comp hm)
  have hΦ : ∀ z, (Φ z).1 = z.1 ≫ π := hm
  have hL' := LB.isLB_pull hr.isLB π
  obtain ⟨s, hs⟩ := exists_isRatSec hL'
  have hp := presents_divOfRatSec hL' hs
  obtain ⟨h₁, h₂⟩ := h Y' _ _ s hp (ChernTransfer.pullW hΦ φ) (ChernTransfer.isCInf_pullW hΦ hφ)
  have hi : Y'.inter (fun _ => divOfRatSec hL' hs) = Y.inter fun _ => Δ := by
    letI := σ.toAlgebra
    rw [Var.inter_eq_of_toPic_eq (fun _ => hL') (fun _ => hp.toPic_eq),
      Var.inter_eq_of_toPic_eq (fun _ => hr.isLB) (fun _ => hr.toPic_eq), hd]
    exact FieldChangeInter.interNum_pull (f := Y.str) (f' := Y'.str) H (L := fun _ => L) fun _ => hr.isLB
  have hsm : SmoothOfRelativeDimension Y.dim Y'.str := hd ▸ Y'.smooth_str
  have e (ε) := ChernTransfer.chernPart_pullW hΦ (AnRead.all _ _ Y.dim) (AnRead.all _ _ Y.dim) hφ ε
  rw [hi] at h₂
  rw [hd] at h₁ h₂
  simp only [Weight.ChernIntegrableOn, Weight.chernInt, integrableOn_univ, Measure.restrict_univ, e,
    integral_map_equiv, integrable_map_equiv] at h₁ h₂ ⊢
  exact ⟨h₁, h₂⟩

end GlobalTheory.ChernDegreeBaseChange
