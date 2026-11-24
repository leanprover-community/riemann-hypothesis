module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalBoundaryMetricData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFrPtPtFOfEigFrame
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram

@[expose] public section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open GlobalTheory.ArcQ
open scoped ContDiff

namespace GlobalTheory.ShFam

theorem exists_frPt_cxPt_of_eigFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (y : CxPts (genStr Z) σ), ¬ LiesIn y (genBd Z) → ∀ f : EigFrame Z σ (y.1 ≫ genι Z), ∃ q : FrPt Xo c (CAt σ), cxPt Z q = y ∧ ∀ τ k, ∃ w : Sp (DualNumber ℂ) ⟶ Z.oF.t.G.left, w ≫ Z.m0.toSABMap.φ = q.u τ k ∧ w ≫ Z.m.φ = f.v τ k := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ y hy f
  have hr : Set.range y.1 ⊆ Set.range Z.jQ := by
    rintro _ ⟨p, rfl⟩
    obtain rfl : p = IsLocalRing.closedPoint ℂ := Subsingleton.elim _ _
    exact not_not.1 hy
  have := Z.jQ_open
  let zF := IsOpenImmersion.lift Z.jQ y.1 hr
  have hzF : zF ≫ Z.jQ = y.1 := IsOpenImmersion.lift_fac _ _ _
  have hs : zF ≫ pullback.snd _ _ = spMap σ := by
    have h2 := y.2
    rw [← hzF, Category.assoc, Z.jQ_over] at h2
    exact h2
  obtain ⟨q, hq, hv⟩ := exists_frPt_ptF_of_eigFrame E H Dw l Xo c O β Z ℂ σ zF (y.1 ≫ genι Z) f hs
    (by rw [← Category.assoc, hzF])
  refine ⟨q, Subtype.ext ?_, hv⟩
  exact (congrArg (· ≫ Z.jQ) hq).trans hzF

end GlobalTheory.ShFam
