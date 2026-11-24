module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilPairingFieldExtensionIff
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

theorem _root_.GlobalTheory.T.weilPairing_fieldExtension_iff : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (K Ω : Type) [Field K] [Field Ω] (i : K →+* Ω) (x : Sp K ⟶ S) (L : LB G.left) (k : ℤ) (y y' : Over.mk x ⟶ G) (c : Kˣ), IsAbelianScheme G → L.IsLB → (Out.WeilIs G L k ((Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ x) ⟶ Over.mk x) ≫ y) ((Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ x) ⟶ Over.mk x) ≫ y') (unitOn (Units.map i.toMonoidHom c)) ↔ Out.WeilIs G L k y y' (unitOn c)) := by
  first | exact @GlobalTheory.weilIs_fieldExt_iff | exact GlobalTheory.weilIs_fieldExt_iff | (intros; apply GlobalTheory.weilIs_fieldExt_iff <;> assumption)
