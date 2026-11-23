module

public import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GtPtAct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivalentIdempotentImageFixedTorsion
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_equivalent_idempotent_image_fixed_torsion : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (n : ℕ), 1 ≤ n → IsUnit (n : R) → ∀ (Q : Data R) (D' : DegData R (maximalIdeal R)) (F : PFactor Q D'.toPre) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'] (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), IsSemiAbelian G' → U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (a : TFK (R := R) (AlgebraicClosure (FractionRing R)) ⟶ A'.A), a ^ n = 1 → a ≫ oA.act F.e = a → ∀ p : QkPt D'.toPre (AlgebraicClosure (FractionRing R)) n, QkToAkU U'.toUnifPre (AlgebraicClosure (FractionRing R)) n p a → ∃ p₁ : QkPt D'.toPre (AlgebraicClosure (FractionRing R)) n, p₁.y = F.e • p.y ∧ GtPtAct F.o F.e p.g p₁.g ∧ QkPt.Equiv D'.toPre (AlgebraicClosure (FractionRing R)) p₁ p := by
  first | exact @GlobalTheory.Mum.EFix.exists_equiv_act_of_fixed | exact GlobalTheory.Mum.EFix.exists_equiv_act_of_fixed | (intros; apply GlobalTheory.Mum.EFix.exists_equiv_act_of_fixed <;> assumption)
