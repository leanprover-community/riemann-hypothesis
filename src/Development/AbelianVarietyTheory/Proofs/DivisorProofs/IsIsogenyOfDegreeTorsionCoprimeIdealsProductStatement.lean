module

public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique
public import Development.AbelianVarietyTheory.Definitions.Divisors.CompEqOneIffPush
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsogenyOfDegreeTorsionCoprimeIdealsProduct
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

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isIsogenyOfDegree_torsion_coprime_ideals_product : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (O : Type) [CommRing O] (ρ : ReciprocityTheory.ChartRestriction.G.Out.RingAct A O) (𝔞 𝔟 : Ideal O), 𝔞 ⊔ 𝔟 = ⊤ → ∀ (K₁ K₂ K₃ : Over S) (i₁ : K₁ ⟶ A) (i₂ : K₂ ⟶ A) (i₃ : K₃ ⟶ A), Mono i₁ → Mono i₂ → Mono i₃ → (∀ (T : Over S) (x : T ⟶ A), GlobalTheory.IwLevel.InSub i₁ x ↔ GlobalTheory.IwLevel.KilledBy ρ 𝔞 x) → (∀ (T : Over S) (x : T ⟶ A), GlobalTheory.IwLevel.InSub i₂ x ↔ GlobalTheory.IwLevel.KilledBy ρ 𝔟 x) → (∀ (T : Over S) (x : T ⟶ A), GlobalTheory.IwLevel.InSub i₃ x ↔ GlobalTheory.IwLevel.KilledBy ρ (𝔞 * 𝔟) x) → ∀ (d e : ℕ), 0 < e → GlobalTheory.IwLevel.IsIsogDeg (toUnit K₃) (d * e) → GlobalTheory.IwLevel.IsIsogDeg (toUnit K₂) e → GlobalTheory.IwLevel.IsIsogDeg (toUnit K₁) d := by
  first | (exact @GlobalTheory.IwLevel.CoprimeTors.isIsogDeg_of_coprime) | (exact GlobalTheory.IwLevel.CoprimeTors.isIsogDeg_of_coprime) | (intros; apply GlobalTheory.IwLevel.CoprimeTors.isIsogDeg_of_coprime  <;> assumption)
