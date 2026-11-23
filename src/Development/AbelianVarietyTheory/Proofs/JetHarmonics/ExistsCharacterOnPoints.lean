module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.RosatiAdj
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
public import Development.AbelianVarietyTheory.Definitions.Jets.ColValMonomial
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.EqOneOfPowEqOneOfCompEqOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie

@[expose] public section

noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsionCharacter

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FamGerm GlobalTheory.KernelNoTorsion

theorem ringAct_natCast {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {Λ : Type} [Ring Λ]
    (ρ : RingAct A Λ) (n : ℕ) : ρ.act n = (𝟙 A) ^ n := by
  induction n with
  | zero =>
    have h : ρ.act 0 = ρ.act 0 * ρ.act 0 := by
      have := ρ.map_add 0 0
      rwa [add_zero] at this
    rw [Nat.cast_zero, pow_zero]
    exact left_eq_mul.mp h
  | succ n ih =>
    rw [Nat.cast_succ, ρ.map_add, ih, ρ.map_one, pow_succ]
    rfl

abbrev Admissible {V O : Type} [CommRing V] [IsLocalRing V] [CommRing O] (f : V →+* O) (A : Type) [CommRing A]
    [Algebra O A] : Prop :=
  (Module.Finite O A ∧ Module.Free O A) ∨ ∃ n : ℕ, ∀ a ∈ maximalIdeal V ^ n, algebraMap O A (f a) = 0

theorem dualBC_inr {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (s : O) :
    dualBC (Algebra.ofId O R) (TrivSqZeroExt.inr s) = TrivSqZeroExt.inr (algebraMap O R s) :=
  TrivSqZeroExt.lift_apply_inr _ _ _ _ _ s

theorem fst_comp_dualBC {O R : Type} [CommRing O] [CommRing R] [Algebra O R] :
    (TrivSqZeroExt.fstHom O R R).comp (dualBC (Algebra.ofId O R)) =
      (Algebra.ofId O R).comp (TrivSqZeroExt.fstHom O O O) := by
  apply DualNumber.algHom_ext
  show (dualBC (Algebra.ofId O R) (TrivSqZeroExt.inr 1)).fst =
    algebraMap O R (TrivSqZeroExt.inr 1 : DualNumber O).fst
  rw [dualBC_inr, TrivSqZeroExt.fst_inr, TrivSqZeroExt.fst_inr, map_zero]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {V : Type} [CommRing V] [IsDomain V]
  [IsDiscreteValuationRing V] {F : Type} [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (y : Pt1 E H V F)

theorem dAct_eq_map {R O F Λ : Type} [CommRing R] [CommRing O] [CommRing F] [CommRing Λ] [StarRing Λ] [Algebra R F]
    [Algebra O F] (f : R →+* O) (hf : ∀ r, algebraMap O F (f r) = algebraMap R F r) {d : ℕ}
    (B : Geo.Tor.Germ.FB R d Λ) (a : Λ) :
    TB.dAct F B a = ((TB.dLin (B.A.act a)).map f).map (algebraMap O F) := by
  ext i k
  simp [TB.dAct, TB.dLin, Geo.Tor.Germ.FB.actK, hf]

end GlobalTheory.TorsionCharacter
