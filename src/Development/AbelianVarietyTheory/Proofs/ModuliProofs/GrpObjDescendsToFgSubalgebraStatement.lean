module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GrpObjDescendsToFgSubalgebra
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
theorem _root_.GlobalTheory.T.exists_fg_subalgebra_grpObj_model : ∀ (k V : Type) [CommRing k] [CommRing V] [Algebra k V] (A : Over (Sp V)) [GrpObj A] [IsCommMonObj A] (X : Scheme.{0}) (p : X ⟶ Sp k) (φ : A.left ⟶ X) (F : Finset V), Smooth p → IsSeparated p → QuasiCompact p → IsPullback φ A.hom p (spMap (algebraMap k V)) → ∃ (R : Subalgebra k V) (A₀ : Over (Sp R)) (_ : GrpObj A₀) (_ : IsCommMonObj A₀) (ψ : A.left ⟶ A₀.left), (F : Set V) ⊆ R ∧ R.FG ∧ Smooth A₀.hom ∧ IsSeparated A₀.hom ∧ QuasiCompact A₀.hom ∧ IsGrpPullback A A₀ (spMap R.val.toRingHom) ψ := by
  first | exact @GlobalTheory.grpObj_descends_to_fg_subalgebra | exact GlobalTheory.grpObj_descends_to_fg_subalgebra | (intros; apply GlobalTheory.grpObj_descends_to_fg_subalgebra <;> assumption)
