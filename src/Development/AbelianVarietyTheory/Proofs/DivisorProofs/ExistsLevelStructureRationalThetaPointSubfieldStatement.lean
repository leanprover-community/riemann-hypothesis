module

public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelStructureRationalThetaPointSubfield
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.exists_level_structure_rational_thetaPoint_subfield : ∀ (F Ω : Type) [Field F] [IsAlgClosed F] [CharZero F] [Field Ω] [IsAlgClosed Ω] (em : F →+* Ω) (A : PolAV (Sp Ω)) (n J : ℕ), n.Prime → 1 ≤ J → ∀ (Ix : Type) (x : Ix → (baseOver (Sp Ω) ⟶ A.A)) (v : Ix → F), (∀ z : baseOver (Sp Ω) ⟶ A.A, z ^ ((n ^ J) ^ 2) = 1 → ∃ i, x i = z) → IsThetaPt A (n ^ J) x (fun i => (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (em (v i))) → ∃ (ζ : Fˣ) (lev : Level A ((n ^ J) ^ 2) (unitOn (Units.map em.toMonoidHom ζ))) (v' : (Fin (2 * A.g) → ZMod ((n ^ J) ^ 2)) → F), IsPrimitiveRoot ζ ((n ^ J) ^ 2) ∧ IsThetaPt A (n ^ J) (GlobalTheory.levelPoint lev rfl) (fun a => (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (em (v' a))) := by
  first | exact @GlobalTheory.ThetaDescentLevel.exists_level | exact GlobalTheory.ThetaDescentLevel.exists_level | (intros; apply GlobalTheory.ThetaDescentLevel.exists_level <;> assumption)
