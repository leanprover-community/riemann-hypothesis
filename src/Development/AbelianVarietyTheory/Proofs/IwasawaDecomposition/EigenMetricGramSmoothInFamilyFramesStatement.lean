module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LieGramEqGramOf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenMetricGramSmoothInFamilyFrames
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

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.LieBase GlobalTheory.CxPts GlobalTheory.Cartier


theorem _root_.GlobalTheory.T.eigenMetricGram_smooth_in_familyFrames : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) [SmoothOfRelativeDimension Dw.dim (genStr Z)] (σ : c.F →+* ℂ) (G : EigMet Z σ), G.SmoothOn (manifold Z σ) {y | ¬ LiesIn y (genBd Z)} → ∀ (F : Type) [Field F] (e : F ≃+* c.F) (X : Var F) (j : X.X ⟶ gen Z) (f₀ : EigFrame Z (constF e X) (genericPt X ≫ j ≫ genι Z)) (S : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr Z ≫ spMap e.toRingHom = X.str), IsOpenImmersion j → Tied e X j f₀ S A₀ → ∀ y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j), ∀ A ∈ S.S (under y), ∀ (τ : E →+* ℂ) (a b : Fin (Dw.mult τ)), CInfAt (fun z => (gramOf e G hj f₀ A₀ A z τ a b).re) y ∧ CInfAt (fun z => (gramOf e G hj f₀ A₀ A z τ a b).im) y := by
  first | exact @GlobalTheory.LieBase.cInfAt_gramOf | exact GlobalTheory.LieBase.cInfAt_gramOf | (intros; apply GlobalTheory.LieBase.cInfAt_gramOf <;> assumption)
