module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PushExLeft
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExpCoordinatesTangentFieldHolomorphicPeriodMap
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
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open GlobalTheory.ArcQ
open scoped ContDiff

theorem _root_.GlobalTheory.T.expCoordinates_tangentField_holomorphic_periodMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (i : Fin Fu.n) (n : ℕ) (B : Set (Fin n → ℂ)) (P : (Fin n → ℂ) → ((Fu.Di i).La →+ (Fin g → ℂ))) (p : (Fin n → ℂ) → (Sp ℂ ⟶ Xo.XF c)) (hu : ∀ b, Fu.u i (P b) = p b ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) (V : (gen Z).affineOpens) (v : Sp (DualNumber Γ(gen Z, V.1)) ⟶ Z.t.G.left), IsOpen B → (∀ b, IsPeriod (Fu.Di i) ty (P b)) → (∀ a, DifferentiableOn ℂ (fun b => P b a) B) → (∀ b, p b ≫ pullback.snd _ _ = spMap σ) → IsTanAtG Z.t (LogKS.chart V ≫ genι Z) v → ∃ W : (Fin n → ℂ) → (Fin g → ℂ), DifferentiableOn ℂ W {b ∈ B | ⊤ ≤ (p b ≫ Z.jQ) ⁻¹ᵁ V.1} ∧ ∀ b ∈ B, ∀ (y : CxPts (genStr Z) σ) (hy : y ∈ ptsIn (genStr Z) σ V.1), y.1 = p b ≫ Z.jQ → IsDerivAt0 (fun z => GlobalTheory.ShFam.Hor.LogCh.liftEx Z Fu (p b) i (P b) (hu b) z ≫ Z.m.φ) (W b) (spMap (Formalism.L2.Pj.dualMap (evHom hy)) ≫ v) := by
  first | exact @GlobalTheory.ModelExpCoord.coord_holomorphic | exact GlobalTheory.ModelExpCoord.coord_holomorphic | (intros; apply GlobalTheory.ModelExpCoord.coord_holomorphic <;> assumption)
