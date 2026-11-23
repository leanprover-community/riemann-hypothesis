module

public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcDataDescendsPrincipalIdealSubring
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

theorem _root_.GlobalTheory.T.arcData_descends_principalIdealSubring : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (R R' : Type) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [CharZero R] [Field R'] (f : R →+* R') (b : O →+* R) (b' : O →+* R') (a' : ArcIn Dw l β R' b') (D₀ : Out.DegPre R) (p : Out.IsPullDeg f D₀ a'.D₀) (n : ℕ), letI := H.starRing; ∀ oB : D₀.P.OAct (𝓞 E), Function.Injective f → b' = f.comp b → 0 < n → TauCan a'.D₀ n → (∀ x, (a'.oa.onB.act x).left ≫ prj p = prj p ≫ (oB.act x).left) → (∀ v, ∃ q, GlobalTheory.ArcPull.IsPullQk p q (a'.eta v)) → (∀ v, ∃ q, GlobalTheory.ArcPull.IsPullQk p q (a'.etaA v)) → ∃ (a : ArcIn Dw l β R b) (p' : Out.IsPullDeg f a.D₀ a'.D₀), a.D₀ = D₀ ∧ HEq p' p ∧ InBC f a a' p' ∧ TauCan a.D₀ n := by
  first | exact @GlobalTheory.ArcDescent.exists_arcIn_down | exact GlobalTheory.ArcDescent.exists_arcIn_down | (intros; apply GlobalTheory.ArcDescent.exists_arcIn_down <;> assumption)
