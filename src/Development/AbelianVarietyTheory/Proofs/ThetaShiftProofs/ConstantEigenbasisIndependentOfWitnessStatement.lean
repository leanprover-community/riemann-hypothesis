module

public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstantEigenbasisIndependentOfWitness
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcLineFunctions.ArcSPin

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

theorem _root_.GlobalTheory.T.constantEigenbasis_independent_of_witness : Out.GlobalFnsSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] (b : O →+* A) (a : ArcIn Dw l β A b) (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ) (ρ : (E →+* ℂ) → (𝓞 E →+* A)) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR A)), ArcBasis W ρ e → (∀ (O' : Type) [CommRing O'] (β' : O' →+* c.F) (Y' : Model Xo c β') (b' : O' →+* A) (a' : ArcIn Dw l β' A b') (χ' : Sp (PowerSeries A) ⟶ Y'.X) (W' : Wit Y' a' χ') (p : Out.IsPullDeg (RingHom.id A) a.D₀ a'.D₀) (e' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a'.D₀ (epsR A)), (∀ (x : 𝓞 E) y, p.xe (x • y) = x • p.xe y) → (letI := H.starRing; ∀ x : 𝓞 E, (a'.oa.onB.act x).left ≫ prj p = prj p ≫ (a.oa.onB.act x).left) → (∀ τ k, LetBC p (e τ k) (e' τ k)) → ArcBasis W' ρ e') ∧ (∀ (χ' : Sp (PowerSeries A) ⟶ Y.X) (W' : Wit Y a χ'), ArcBasis W' ρ e) ∧ ∀ τ ν (v : epsR (PowerSeries A) ⟶ W.t.G), GtTanR ν → LieImg W ν v → (∀ x : 𝓞 E, (v ≫ W.t.act.act x).left = spMap (epsScaleR (PowerSeries.C (R := A) (ρ τ x))) ≫ v.left) → ∃! cf : Fin (Dw.mult τ) → A, GtComb cf (e τ) ν := by
  exact GlobalTheory.ArcBasisIndep.arcBasis_indep
