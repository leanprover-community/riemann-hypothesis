module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LbIsoSpread
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.lbIso_spread_alt : ∀ (g n : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Type) [CommRing S] (R₀ : Subring S) (s₀ : Sp R₀ ⟶ Sp B) (d₀ : SiegPre g n ζ s₀) (Y : Scheme.{0}) (sY : Y ⟶ Sp B) (u : SiegPre g n ζ sY) (h₀ : Sp R₀ ⟶ Y) (ψ : d₀.A.left ⟶ u.A.left) (sE : Sp S ⟶ Sp B) (e : SiegPre g n ζ sE) (j : e.A.left ⟶ d₀.A.left), IsPullback ψ d₀.A.hom u.A.hom h₀ → ∀ (j₂ : (G2 e.A).left ⟶ (G2 d₀.A).left) (φ₂ : (G2 e.A).left ⟶ (G2 u.A).left), IsPullback j e.A.hom d₀.A.hom (spMap R₀.subtype) → IsSquare j j₂ → LBIso e.P (d₀.P.pull j₂) → IsSquare (j ≫ ψ) φ₂ → LBIso e.P (u.P.pull φ₂) → ∃ F : Finset S, ∀ (R₁ : Subring S) (hle : R₀ ≤ R₁), (F : Set S) ⊆ R₁ → ∀ (s₁ : Sp R₁ ⟶ Sp B) (d₁ : SiegPre g n ζ s₁) (φ₁ : d₁.A.left ⟶ d₀.A.left) (φ₁₂ : (G2 d₁.A).left ⟶ (G2 d₀.A).left) (χ₂ : (G2 d₁.A).left ⟶ (G2 u.A).left), IsPullback φ₁ d₁.A.hom d₀.A.hom (spMap (Subring.inclusion hle)) → IsSquare φ₁ φ₁₂ → LBIso d₁.P (d₀.P.pull φ₁₂) → IsSquare (φ₁ ≫ ψ) χ₂ → LBIso d₁.P (u.P.pull χ₂) := by
  first | exact @GlobalTheory.SiegBundleSpread.lbIso_spread | exact GlobalTheory.SiegBundleSpread.lbIso_spread | (intros; apply GlobalTheory.SiegBundleSpread.lbIso_spread <;> assumption)
