module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsScalarFormTraceForm
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValEqOfAppInjective
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcDatumPullbackRescaledMatches
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
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsStrict

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.ModelData

theorem _root_.GlobalTheory.T.arcDatum_pullback_rescaled_matches : GlobalFnsSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (O' : Type) [CommRing O'] [IsDomain O'] (b : O →+* O') (a : ArcIn D l β O' b) (R : Type) [CommRing R] [IsDomain R] (f : O' →+* R) (D' : DegPre R) (hD : IsPullDeg f a.D₀ D') (u₀ : R) (uK : (FractionRing R)ˣ), (uK : FractionRing R) = algebraMap R _ u₀ → ∀ (q : D'.X → (FractionRing R)ˣ) (Φ : D'.P.A.left ⟶ a.D₀.P.A.left), Φ = PsiEvenPull.proj hD → (∀ y, q y = uK ^ (a.be (hD.xe y) (hD.xe y) / 2)) → ∃ (_ : Module (𝓞 E) (TauTwist.rescale D' q).X) (oW : letI := H.starRing; (TauTwist.rescale D' q).OAct (𝓞 E)) (he : _) (w : _) (e : _), GlobalTheory.LN.Match a f u₀ (TauTwist.rescale D' q) oW Φ he w e ∧ (∀ y, hD.xe (e y) = y) ∧ (TauTwist.rescale D' q).PsiEven ∧ (TauTwist.rescale D' q).TauBimult := by
  first | exact @GlobalTheory.RescaleMatch.exists_match_rescale | exact GlobalTheory.RescaleMatch.exists_match_rescale | (intros; apply GlobalTheory.RescaleMatch.exists_match_rescale <;> assumption)
