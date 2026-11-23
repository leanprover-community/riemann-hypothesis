module

public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsScalarFormTraceForm
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValEqOfAppInjective
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDegenerationPreDataOverSubfield
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
open GlobalTheory

theorem _root_.GlobalTheory.T.exists_degenerationPreData_over_subfield : Laws → ∀ (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (D : DegPre K) (P₀ : PolAV (Sp K₀)) (Φ : D.P.A.left ⟶ P₀.A.left), IsGrpPullback D.P.A P₀.A (spMap i) Φ → LBIso D.P.L (P₀.L.pull Φ) → ∀ c₀ : D.X → (𝟙_ (Over (Sp K₀)) ⟶ P₀.A), (∀ y z, c₀ (y + z) = padd P₀.A (c₀ y) (c₀ z)) → (∀ y, (D.c y).left ≫ Φ = spMap i ≫ (c₀ y).left) → ∃ (D₀ : DegPre K₀) (ψ : TauTwist.PsiFam D) (hψ : ∀ χ, (ψ χ).IsGen) (hD : IsPullDeg i D₀ (TauTwist.withPsi D ψ hψ)), D₀.P = P₀ ∧ HEq (PsiEvenPull.proj hD) Φ := by
  first | exact @GlobalTheory.FieldPull.exists_pre_below | exact GlobalTheory.FieldPull.exists_pre_below | (intros; apply GlobalTheory.FieldPull.exists_pre_below <;> assumption)
