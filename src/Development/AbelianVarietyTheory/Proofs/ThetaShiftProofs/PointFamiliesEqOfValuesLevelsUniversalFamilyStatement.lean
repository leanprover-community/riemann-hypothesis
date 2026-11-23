module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PointFamiliesEqOfValuesLevelsUniversalFamily
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

theorem _root_.GlobalTheory.T.pointFamilies_eq_of_values_levels_universalFamily : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (F : Type) [Field F] [IsAlgClosed F] [CharZero F] (V : Type) [AddCommGroup V] (act : 𝓞 E → V → V) (I : ℕ → Type) (φ : ∀ j, I j → V → F) (y₁ y₂ : Sp F ⟶ Xo.X) (Θ₁ : FPts act Xo.univ.t y₁ φ) (Θ₂ : FPts act Xo.univ.t y₂ φ), y₁ ≫ Xo.s = y₂ ≫ Xo.s → (∀ v, ∃ ψ, Θ₁.Lev l.A (toUnit _ ≫ Xo.univ.etaA v) ψ ∧ Θ₂.Lev l.A (toUnit _ ≫ Xo.univ.etaA v) ψ) → (∀ v ∈ idealPart D l, ∃ ψ, Θ₁.Lev l.M (toUnit _ ≫ Xo.univ.eta v) ψ ∧ Θ₂.Lev l.M (toUnit _ ≫ Xo.univ.eta v) ψ) → ∀ v, (Θ₁.x v).left = (Θ₂.x v).left ∧ ∀ j, ⊤ ≤ (Θ₁.x v).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → Θ₁.τ v j = Θ₂.τ v j := by
  first | exact @GlobalTheory.FamilyUnique.points_frames_eq | exact GlobalTheory.FamilyUnique.points_frames_eq | (intros; apply GlobalTheory.FamilyUnique.points_frames_eq <;> assumption)
