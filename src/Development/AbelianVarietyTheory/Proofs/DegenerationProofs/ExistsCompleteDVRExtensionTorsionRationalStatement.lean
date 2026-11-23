module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RatTors
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompleteDVRExtensionTorsionRational
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

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait

theorem _root_.GlobalTheory.T.exists_completeDVR_extension_torsion_rational : Laws → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (C : Type) [NormedField C] [IsUltrametricDist C] [IsAlgClosed C] [Algebra (FractionRing W) C], CExt W (IsLocalRing.maximalIdeal W) C → ∀ n : ℕ, 1 ≤ n → ∀ (S₁ S₂ : Scheme.{0}) (s₁ : Sp W ⟶ S₁) (s₂ : Sp W ⟶ S₂) (B₁ : PolAV S₁) (B₂ : PolAV S₂), ∃ (W' : Type) (_ : CommRing W') (_ : IsDomain W') (_ : IsLocalRing W') (_ : Algebra (FractionRing W') C) (io : W →+* W'), GlobalTheory.LN.CDvr W' ∧ Function.Injective io ∧ io.Finite ∧ IsLocalHom io ∧ Along io C ∧ CExt W' (IsLocalRing.maximalIdeal W') C ∧ (∀ (B : PolAV (Sp W')) (ψ : B.A.left ⟶ B₁.A.left), IsGrpPullback B.A B₁.A (spMap io ≫ s₁) ψ → RatTors B C n) ∧ ∀ (B : PolAV (Sp W')) (ψ : B.A.left ⟶ B₂.A.left), IsGrpPullback B.A B₂.A (spMap io ≫ s₂) ψ → RatTors B C n := by
  first | exact @GlobalTheory.Ex.TorsionField.exists_cDvr_ratTors | exact GlobalTheory.Ex.TorsionField.exists_cDvr_ratTors | (intros; apply GlobalTheory.Ex.TorsionField.exists_cDvr_ratTors <;> assumption)
