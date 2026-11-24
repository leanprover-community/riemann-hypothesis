module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.UnitarySelfGeneration

private theorem isLieEigen_twistAct_iff {O : Type} [CommRing O] {S : Scheme.{0}} {G : Over S} [GrpObj G] (act : OAct O G) (s : O ≃+* O) {k : Type} [Field k] (t : Sp k ⟶ S) (τ : O →+* k) (v : epsPt t ⟶ G) :
    IsLieEigen (twistAct act s) t (τ.comp s.toRingHom) v ↔ IsLieEigen act t τ v := by
  constructor
  · rintro ⟨h0, h1⟩
    refine ⟨h0, fun a => ?_⟩
    have := h1 (s.symm a)
    simpa [twistAct] using this
  · rintro ⟨h0, h1⟩
    refine ⟨h0, fun a => ?_⟩
    simpa [twistAct] using h1 (s a)

theorem tw_liemult : ∀ (O : Type) [CommRing O] (S : Scheme.{0}) (G : Over S) [GrpObj G] (act : OAct O G) (s : O ≃+* O) (k : Type) [Field k] (t : Sp k ⟶ S) (τ : O →+* k) (n : ℕ), LieMult (twistAct act s) t (τ.comp s.toRingHom) n ↔ LieMult act t τ n := by
  intro O _ S G _ act s k _ t τ n
  simp only [LieMult, isLieEigen_twistAct_iff]

end PositivityTheory.UnitarySelfGeneration
