module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import Development.AbelianVarietyTheory.Definitions.Jets.ColValMonomial
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsCharactersBoundedMinorsOfHodgeTateChartBou
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
import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
import Formalism.LocalToGlobal.ProjectiveLattices.SubConstMemOrig
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.BidegreeTwoJet
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.BoxTuple
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpBijectiveUniformisation
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermCut
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.LemmaBStatement

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
open IsDedekindDomain

theorem _root_.GlobalTheory.T.exists_characters_boundedMinors_of_hodgeTateChartBound : (∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.HTFSt p) → ∀ (p : ℕ) [Fact p.Prime], ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra (FractionRing V) F] [Algebra V F] [IsScalarTower V (FractionRing V) F] (y : FamGerm.Pt1 E H V F), letI := H.starRing; IsAdicComplete (Ideal.span {(p : TWO.Ov y.v)}) (TWO.Ov y.v) → ¬ IsUnit (p : TWO.Ov y.v) → ∀ a : 𝓞 E, a * star a = (p : 𝓞 E) → (∃ u u' : 𝓞 E, u * a + u' * star a = 1) → ∀ (T : Type) [Fintype T] [DecidableEq T] (rk : T → ℕ) (τ : T → 𝓞 E →+* TWO.Ov y.v) (e : (Σ t, Fin (rk t)) → Fin y.d → TWO.Ov y.v), (∀ (c : 𝓞 E) l, (dAct F y.B c).mulVec (fun i => (e l i : F)) = (τ l.1 c : F) • fun i => (e l i : F)) → (∀ t, τ t a ∈ Ideal.span {(p : TWO.Ov y.v)}) → (∀ t, ∃ lam : Fin (rk t) → Fin y.d → TWO.Ov y.v, ∀ i i', ∑ s, lam i s * e ⟨t, i'⟩ s = if i = i' then 1 else 0) → (∃ ε : T → 𝓞 E, ∀ t t', τ t' (ε t) - (if t = t' then 1 else 0) ∈ Ideal.span {(p : TWO.Ov y.v)}) → ∀ c : TWO.Ov y.v, (p - 1) • y.v (c : F) = y.v (p : F) → ∀ (n : ℕ) (col : ∀ t, Fin (rk t) → Fin n), (∀ t, Function.Injective (col t)) → ∃ yy : (Σ t, Fin (rk t)) × Fin n → TWO.Ov y.v, (∀ b, y.CharAt a p e (fun l => yy (l, b))) ∧ ∀ t (s : Fin (rk t)), y.v (((Matrix.of fun a i : Fin (s.val + 1) => yy (⟨t, Fin.castLE s.isLt a⟩, col t (Fin.castLE s.isLt i))).det : TWO.Ov y.v) : F) ≤ (s.val + 1) • y.v (c : F) := by
  first | exact @GlobalTheory.ChartCharacter.characters_exist_of_chartBound | exact GlobalTheory.ChartCharacter.characters_exist_of_chartBound | (intros; apply GlobalTheory.ChartCharacter.characters_exist_of_chartBound <;> assumption)
