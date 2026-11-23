module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothModelsIsoOverFgSubalgebra
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
theorem _root_.GlobalTheory.T.exists_iso_pullback_over_fg_subalgebra : ∀ (k V : Type) [CommRing k] [CommRing V] [Algebra k V] (P Q T : Scheme.{0}) (p : P ⟶ Sp k) (q : Q ⟶ Sp k) (t : T ⟶ Sp V) (τ : T ⟶ P) (τ' : T ⟶ Q), Smooth p → IsSeparated p → QuasiCompact p → Smooth q → IsSeparated q → QuasiCompact q → IsPullback τ t p (spMap (algebraMap k V)) → IsPullback τ' t q (spMap (algebraMap k V)) → ∃ (R : Subalgebra k V) (e : pullback p (spMap (algebraMap k R)) ≅ pullback q (spMap (algebraMap k R))), R.FG ∧ e.hom ≫ pullback.snd _ _ = pullback.snd _ _ ∧ ∀ σ : T ⟶ pullback p (spMap (algebraMap k R)), σ ≫ pullback.fst _ _ = τ → σ ≫ pullback.snd _ _ = t ≫ spMap R.val.toRingHom → σ ≫ e.hom ≫ pullback.fst _ _ = τ' := by
  first | exact @GlobalTheory.smooth_models_iso_over_fg_subalgebra | exact GlobalTheory.smooth_models_iso_over_fg_subalgebra | (intros; apply GlobalTheory.smooth_models_iso_over_fg_subalgebra <;> assumption)
