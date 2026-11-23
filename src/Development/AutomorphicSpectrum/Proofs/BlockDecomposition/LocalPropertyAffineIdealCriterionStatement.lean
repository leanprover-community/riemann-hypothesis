module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalPropertyAffineIdealCriterion
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.LeftZeroDuality.H1StructureDimLe

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual PositivityTheory.ObstructionTrivialLocus GlobalTheory.CompanionTheory.TrivLoc
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.local_property_affine_ideal_criterion : ∀ (Y : Scheme.{0}) (P : ∀ T : Scheme.{0}, (T ⟶ Y) → Prop),
    (∀ (T T' : Scheme.{0}) (h : T' ⟶ T) (t : T ⟶ Y), P T t → P T' (h ≫ t)) →
    (∀ (T : Scheme.{0}) (t : T ⟶ Y), (∀ x : T, ∃ W : T.Opens, x ∈ W ∧ P W.toScheme (W.ι ≫ t)) → P T t) →
    (∀ y : Y, ∃ (U : Y.Opens) (hU : IsAffineOpen U) (r : Γ(Y, U)) (I : Ideal Γ(Y, U)), y ∈ Y.basicOpen r ∧
      ∀ (R' : Type) [CommRing R'] (g : Γ(Y, U) →+* R'), IsUnit (g r) →
        (P (Spec (CommRingCat.of R')) (Spec.map (CommRingCat.ofHom g) ≫ hU.fromSpec) ↔ I ≤ RingHom.ker g)) →
    ∀ (U : Y.Opens) (hU : IsAffineOpen U), ∃ J : Ideal Γ(Y, U), ∀ (R' : Type) [CommRing R'] (g : Γ(Y, U) →+* R'),
      (P (Spec (CommRingCat.of R')) (Spec.map (CommRingCat.ofHom g) ≫ hU.fromSpec) ↔ J ≤ RingHom.ker g) := by
  exact @GlobalTheory.CompanionTheory.TrivLoc.Rep.exists_ideal_on_affine
