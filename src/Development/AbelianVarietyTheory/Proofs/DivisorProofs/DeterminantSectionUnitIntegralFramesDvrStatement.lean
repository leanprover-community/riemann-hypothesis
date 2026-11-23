module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSectionOfChg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantSectionUnitIntegralFramesDvr
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine

theorem _root_.GlobalTheory.T.determinantSection_unit_integral_frames_dvr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (O' : Type) [CommRing O'] (β' : O' →+* c.F) (Z : Model Xo c β') (U : Set (Xo.XF c)) (τ : E →+* ℂ) (σZ : RuleY Z) (σ : RuleU Xo c), SecY Z (compactOf Z U) τ σZ → NzY Z (compactOf Z U) τ σZ → Restricts Z U τ σZ σ → ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (j : c.F →+* R) (xR : Sp R ⟶ gen Y) (x : Sp K ⟶ Xo.XF c) (V : Set (gen Y)) vR wR v w vb wb, FrY Y V τ j xR vR wR → FrU Xo c U τ ((algebraMap R K).comp j) x v w → x ≫ Y.jQ = spMap (algebraMap R K) ≫ xR → SameVecs Y x v vb → SameVecs Y x w wb → (∀ i, (vb i).left = spMap (Chart.dualMapR (algebraMap R K)) ≫ (vR i).left) → (∀ i, (wb i).left = spMap (Chart.dualMapR (algebraMap R K)) ≫ (wR i).left) → ∃ u : Rˣ, σ K x v w = algebraMap R K u := by
  first | exact @GlobalTheory.DetLine.DvrUnit.unit_in_integral_frame | exact GlobalTheory.DetLine.DvrUnit.unit_in_integral_frame | (intros; apply GlobalTheory.DetLine.DvrUnit.unit_in_integral_frame <;> assumption)
