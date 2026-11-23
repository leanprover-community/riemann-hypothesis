module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCoinductionAugmentationCompDEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSheafHomLinearMapsSheafCurryEquivStatement
public import Mathlib.Algebra.Category.ModuleCat.Projective
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem homSh_injective (R : Type) [CommRing R] (J : Shv R) [Injective J] (M : ModuleCat.{1} (ULift.{1} R)) [Projective M] :
    Injective ((homSh J).obj (op M)) := by
  obtain ⟨e, -, hX⟩ := GlobalTheory.T.exists_sheafHom_linearMapsSheaf_curry_equiv R J
  haveI : Module.Projective (ULift.{1} R) M := (IsProjective.iff_projective (P := M)).2 ‹_›
  constructor
  intro X Y g i _
  have surj : Function.Surjective (Linear.leftComp (ULift.{1} R) J i) :=
    fun k => ⟨Injective.factorThru k i, Injective.comp_factorThru k i⟩
  obtain ⟨h', hh'⟩ := Module.projective_lifting_property _ (e X M g) surj
  refine ⟨(e Y M).symm h', ?_⟩
  apply (e X M).injective
  rw [hX, Equiv.apply_symm_apply, hh']

end GlobalTheory.EtC
