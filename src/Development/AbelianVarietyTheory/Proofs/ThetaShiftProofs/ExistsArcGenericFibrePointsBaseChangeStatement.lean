module

public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFShiftZeroIff
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsArcGenericFibrePointsBaseChange
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

theorem _root_.GlobalTheory.T.exists_arcGenericFibrePoints_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (S : Scheme.{0}) (A : AnArc (𝓞 E)) (t : SAB H S) (y : Sp ℂ⸨X⸩ ⟶ S) (Φ : GenPts A t y) (F : Type) [Field F] (f : ℂ⸨X⸩ →+* F) (φ : ∀ j, (Σ α : A.X, A.Theta j α) → A.V → F), AnFin A → (∀ (j : ℕ) [NeZero j] i v, φ j i v = f (A.FSum j i.1 i.2 v)) → ∃ Θ : FPts (I := fun j => Σ α : A.X, A.Theta j α) (fun e v => A.actV e v) t (spMap f ≫ y) φ, (∀ v, (Θ.x v).left = spMap f ≫ (Φ.x v).left ∧ ∀ j, ⊤ ≤ (Φ.x v).left ⁻¹ᵁ t.PP.L.U j → Θ.τ v j = f (Φ.τ v j)) ∧ ∀ (k : ℕ) [NeZero k] (ξ : 𝟙_ (Over S) ⟶ t.G) (la : A.La) (ψ : (Σ α : A.X, A.Theta k α) → A.V → ℂ⸨X⸩), Φ.LevelPt k (toUnit _ ≫ ξ) la → (∀ i z, IsFShift A k i.1 i.2 la z (ψ i z)) → Θ.Lev k (toUnit _ ≫ ξ) (fun i z => f (ψ i z)) := by
  first | exact @GlobalTheory.ArcBaseChange.exists_fpts_baseChange | exact GlobalTheory.ArcBaseChange.exists_fpts_baseChange | (intros; apply GlobalTheory.ArcBaseChange.exists_fpts_baseChange <;> assumption)
