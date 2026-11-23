module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
public import Mathlib.Analysis.Complex.Norm
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FrobeniusOnTorsion
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

theorem _root_.GlobalTheory.T.frobenius_on_torsion_alt : ∀ (k : Type) [Field k] [IsAlgClosed k] (p l : ℕ) [Fact p.Prime] [CharP k p], l.Prime → l ≠ p → ∀ (G : Over (Sp k)) [GrpObj G], SmConn G → ∀ (g : ℕ), SmoothOfRelativeDimension g G.hom → ∀ (L : LB G.left), AmpleCub G L → ∀ (F : End G) (q : ℕ), 2 ≤ q → FrobG G F q → ∃ (t a m C : ℕ) (P : Polynomial ℤ) (W : Subgroup (𝟙_ (Over (Sp k)) ⟶ G)), 1 ≤ m ∧ (∀ β : ℂ, Polynomial.aeval β P = 0 → ‖β‖ < (q : ℝ) ^ m) ∧ (∀ x ∈ W, x ≫ ((F ^ m).asHom) = x ^ (q ^ m)) ∧ (∀ n, Finite {x : (𝟙_ (Over (Sp k)) ⟶ G) // x ^ l ^ n = 1} ∧ Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ G) // x ^ l ^ n = 1} ≤ C * l ^ (n * (t + 2 * a)) ∧ Nat.card {x : W // x ^ l ^ n = 1} ≤ C * l ^ (n * t)) ∧ (∀ (x : (𝟙_ (Over (Sp k)) ⟶ G)) n, x ^ l ^ n = 1 → polyPt (F ^ m) P x ∈ W) ∧ (g ≤ t + a → Nonempty (TorusExtension G)) := by
  first | exact @GlobalTheory.SS.frobenius_on_torsion | exact GlobalTheory.SS.frobenius_on_torsion | (intros; apply GlobalTheory.SS.frobenius_on_torsion <;> assumption)
