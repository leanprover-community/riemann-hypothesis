module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KTrivOfKTrivNonemptyOpenNormalCharZero
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.SiegelFamilyZetaUnit
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerAlongIdIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSymplecticOfTranslFixed
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings
open GlobalTheory.PrincSubring

attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.KTrivFlatDescent

theorem trivAlong_of_flat_surjective : ∀ {S S' S'' : Scheme.{0}} (G : Over S) [GrpObj G] (L : LB G.left) (g : S' ⟶ S) (f : S'' ⟶ S') [Flat f] [Surjective f], L.IsLB → GlobalTheory.KTrivSpread.TrivAlong G L (f ≫ g) → GlobalTheory.KTrivSpread.TrivAlong G L g := by
  intro S S' S'' G _ L g f _ _ _ h T a ha x hx
  let u := pullback.fst a f
  have hu : Epi u := Flat.epi_of_flat_of_surjective _
  let T' : Over S := Over.mk (u ≫ T.hom)
  let U : T' ⟶ T := Over.homMk u rfl
  have hs : pullback.snd a f ≫ f ≫ g = T'.hom := by
    show pullback.snd a f ≫ f ≫ g = u ≫ T.hom
    rw [← Category.assoc, ← pullback.condition, Category.assoc, ha]
  have e₁ : U ≫ x = 1 := h T' (pullback.snd a f) hs (U ≫ x) (hx.comp U)
  have e₂ : U ≫ x = U ≫ (1 : T ⟶ G) := by rw [e₁, MonObj.comp_one]
  exact Over.OverMorphism.ext ((cancel_epi u).1 (congrArg (fun q => q.left) e₂))

end GlobalTheory.KTrivFlatDescent
