module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFShiftZeroIff
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TwoRigidifiedThetaFramesOnFibre
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

theorem _root_.GlobalTheory.T.two_rigidified_theta_frames_on_fibre : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (A : AnArc (𝓞 E)) lin cst (w : ℂ) (y₀ : Sp ℂ ⟶ Xo.X) (π : A.V → (Over.mk y₀ ⟶ Xo.univ.t.G)) fr (g : ℕ) (h : A.V ≃L[ℂ] (Fin g → ℂ)) (e : (Fin g → ℂ) → (Sp ℂ ⟶ Xo.univ.t.G.left)) (ϑ : (Fin g → ℂ) → ℂ) fr', IsFibAt A Xo.univ.t lin cst w y₀ π fr → (∀ v, e (h v) = (π v).left) → IsThetaFrameAt Xo.univ.t.PP y₀ e ϑ fr' → (∃ z, ϑ z ≠ 0) → ∀ th ∈ A.Theta 1 0, (∃ v, A.Sum 1 0 th w v ≠ 0) → ∃ (lam : ℂ) (f : A.V → ℂ), lam ≠ 0 ∧ Differentiable ℂ f ∧ (∀ v, f v ≠ 0) ∧ f 0 = 1 ∧ (∀ v j, ⊤ ≤ (π v).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr' j (h v) = f v * fr j v) ∧ ∀ v, A.Sum 1 0 th w v = lam * ϑ (h v) * f v := by
  first | exact @GlobalTheory.TwoFrames.two_frames | exact GlobalTheory.TwoFrames.two_frames | (intros; apply GlobalTheory.TwoFrames.two_frames <;> assumption)
