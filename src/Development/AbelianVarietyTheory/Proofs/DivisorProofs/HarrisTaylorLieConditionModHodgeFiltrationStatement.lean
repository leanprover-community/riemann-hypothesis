module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorModOfTmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieConditionModHodgeFiltration
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.InfUniv

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct

theorem _root_.GlobalTheory.T.harrisTaylor_lie_condition_mod_hodgeFiltration : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (C₀ : Type) [CommRing C₀] [IsLocalRing C₀] (β : R →+* C₀) (s : Sp C₀ ⟶ Sp R), s = spMap β → ∀ (o₀ : GlobalTheory.UPel.HT.Obj b N s) (y : HdR o₀.A), GlobalTheory.HTSummand.crysAct (dp0 C₀) (𝟙 _) o₀.act (algebraMap (𝓞 D.F) D.O D.ω) y - β b.ρ • y ∈ Fil o₀.A → ∃ w : Fin D.a → HdR o₀.A, (∀ i (c : 𝓞 D.F), GlobalTheory.HTSummand.crysAct (dp0 C₀) (𝟙 _) o₀.act (algebraMap (𝓞 D.F) D.O c) (w i) - β (b.t i c) • w i ∈ Fil o₀.A) ∧ y - ∑ i, w i ∈ Fil o₀.A := by
  first | (exact @GlobalTheory.HTSummand.lie_mod_fil) | (exact GlobalTheory.HTSummand.lie_mod_fil) | (intros; apply GlobalTheory.HTSummand.lie_mod_fil  <;> assumption)
