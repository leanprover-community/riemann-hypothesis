module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFShiftZeroIff
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TripleIsoRespectsLevelRatioPoints
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

theorem _root_.GlobalTheory.T.triple_iso_respects_level_ratio_points : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (B : Type) [CommRing B] (bb : Base l B) (F : Type) [Field F] [IsAlgClosed F] [CharZero F] (V : Type) [AddCommGroup V] (act : 𝓞 E → V → V) (I : ℕ → Type) (φ : ∀ j, I j → V → F) (s : Sp F ⟶ Sp B) (o₁ o₂ : Obj D l bb s) (Θ₁ : FPts act o₁.t (𝟙 _) φ) (Θ₂ : FPts act o₂.t (𝟙 _) φ) (m : SABMap o₁.t o₂.t (𝟙 _)) (w : LB.Iso o₁.t.PP.L (o₂.t.PP.L.pull m.φ)) (k : ℕ) (ψ : I k → V → F) (p₁ : Over.mk (𝟙 (Sp F)) ⟶ o₁.t.G) (p₂ : Over.mk (𝟙 (Sp F)) ⟶ o₂.t.G), 1 ≤ k → w.IsGen → (∀ v, (Θ₁.x v).left ≫ m.φ = (Θ₂.x v).left ∧ ∀ j j', ⊤ ≤ (Θ₁.x v).left ⁻¹ᵁ (LB.div (o₂.t.PP.L.pull m.φ) o₁.t.PP.L).U (fun _ => j, j') → Θ₂.τ v j = valR (Θ₁.x v).left _ (w.s (fun _ => j, j')).val * Θ₁.τ v j') → Θ₁.Lev k p₁ ψ → Θ₂.Lev k p₂ ψ → p₁.left ≫ m.φ = p₂.left := by
  first | exact @GlobalTheory.LevelRespect.level_pt_eq | exact GlobalTheory.LevelRespect.level_pt_eq | (intros; apply GlobalTheory.LevelRespect.level_pt_eq <;> assumption)
