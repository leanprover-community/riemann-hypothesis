module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.MemEigSpOfMemHtDual
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.NotInFibreOfIsUnit
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

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem Lat.patch_values : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type)
    [AddCommGroup E] [Module Ω E] (S : Finset ℕ) (L₀ : Lat ξ E) (Lp : ℕ → Lat ξ E) (q : Cpt ξ), (∀ p ∈ S, p.Prime) →
    ((∀ p ∈ S, ¬ InFibre ξ p q) → Lat.patch S L₀ Lp q = L₀ q) ∧
      ∀ p ∈ S, InFibre ξ p q → Lat.patch S L₀ Lp q = Lp p q := by
  intro X Ω _ ξ E _ _ S L₀ Lp q hS
  exact ⟨fun h => Lat.patch_of_not S L₀ Lp h, fun p hp h => Lat.patch_of_unique S L₀ Lp hp h
    fun p' hp' h' => inFibre_unique (hS p hp) (hS p' hp') h h'⟩

end GlobalTheory.CompanionTheory.Ar
