module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.ArithBase
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorsionPointsOfSquareLevel
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnivBasis

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ThetaReal

theorem _root_.GlobalTheory.T.exists_torsionPoints_of_squareLevel_alt : Laws → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (M : ℕ) (ze : Γ(S, ⊤)ˣ), 1 ≤ M → IsUnit (M : Γ(S, ⊤)) → ∀ lev : Out.Level P (M ^ 2) ze, ∃ pt : (Fin P.g ⊕ Fin P.g → ZMod M) → (baseOver S ⟶ P.A), (∀ a b, pt (a + b) = pt a * pt b) ∧ (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (z : Over.mk x ⟶ P.A), z ^ M = 1 → ∃! a, (Over.homMk x (by simp) : Over.mk x ⟶ baseOver S) ≫ pt a = z) ∧ (∀ a b, WeilIs P.A P.L (M : ℕ) (pt a) (pt b) (ze ^ (M * (eStd P.g M a b).val))) ∧ (∀ a, ∃ y : baseOver S ⟶ P.A, y ^ (M ^ 2) = 1 ∧ y ^ M = pt a) ∧ ∀ (i : Fin P.g) (i₁ i₂ : Fin (2 * P.g)), (i₁ : ℕ) = i → (i₂ : ℕ) = i + P.g → pt (Pi.single (.inl i) 1) = lev.pt i₁ ^ M ∧ pt (Pi.single (.inr i) 1) = lev.pt i₂ ^ M := by
  first | exact @GlobalTheory.exists_torsionPoints_of_squareLevel | exact GlobalTheory.exists_torsionPoints_of_squareLevel | (intros; apply GlobalTheory.exists_torsionPoints_of_squareLevel <;> assumption)
