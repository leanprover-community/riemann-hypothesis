module -- shake: keep-all
-- Its imports stay public: its settings apply to them, and the tactic extensions below are used
-- by nearly every file.

public import Mathlib.Algebra.DirectSum.Internal
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Ring.BooleanRing
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.Reproducing
public import Mathlib.Analysis.Normed.Unbundled.GelfandRadiusNorm
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.SpecificGroups.KleinFour
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Log
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Sqrt
public import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
public import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
public import Mathlib.Tactic.Lemma
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.TypeStar
public import Mathlib.Topology.Sheaves.Init
public import Aesop.Frontend.Tactic
public import Aesop.Main
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Std.Internal.Order.Automation
public import Std.Tactic.BVDecide.Normalize.Prop

/-!
# Speed settings

The three settings of this file make instance search and `simp` faster in all files of the
development. They add no axiom, and no proof relies on them: with this file emptied, the other files
still compile, more slowly.
-/

@[expose] public section

-- Instance search tries these instances late (the default priority is 1000). They give the
-- grade-zero part `A 0` of a graded ring its algebraic structure, and unifying `A 0` with an
-- arbitrary subtype is expensive. Without them `New.Derivatives.Divisibility.NormalForm` times out
-- and `Lib.GaloisRep.Hilbert90.UnitaryGroups` fails.
attribute [instance 20] SetLike.GradeZero.instMonoid SetLike.GradeZero.instCommMonoid
  SetLike.GradeZero.instSemiring SetLike.GradeZero.instCommSemiring SetLike.GradeZero.instRing
  SetLike.GradeZero.instCommRing

-- These lemmas leave the default `simp` set of every importing file. They match very many terms
-- and then fail on a side condition. Tagging a lemma in both directions erases both, and, unlike
-- `attribute [-simp]`, the effect passes to importers. The reversed tags last one command only,
-- so the warning about their head symbols does not apply.
set_option warning.simp.varHead false in
attribute [simp ←, simp] Matrix.conjTranspose_eq_transpose_of_trivial MonoidHom.CompTriple.comp_eq
  LinearMap.identityMapOfZeroModuleIsZero smul_left_cancel_iff mul_cancel_left_mem_nonZeroDivisors
  IsAddKleinFour.card_four' MeasureTheory.lintegral_of_isEmpty Nat.card_eq_zero_of_infinite
  IsRegular.smul_eq_zero_iff_right Unitary.star_mul_self_of_mem inv_mul_cancel_of_invertible
  bot_eq_one' EmbeddingLike.map_eq_one_iff Submodule.smul_coe_torsionBy Valuation.IsUniformizer.val
  star_trivial SetLike.GradeZero.coe_ofNat Associates.coe_unit_eq_one inv_mul_cancel_comm_assoc
  nsmul_eq_zero_iff SetLike.GradeZero.coe_mul RingHomCompTriple.comp_eq Finset.Ioc_eq_empty_of_le
  Finset.univ_eq_empty IsRegular.smul_right_inj IsAddKleinFour.card_four BooleanRing.mul_add_mul
  Submodule.smul_mem_iff' IsKleinFour.card_four' Nat.sub_eq_zero_of_le IsUnit.inv_mul_cancel
  IsUnit.mul_inv_cancel GroupWithZero.dvd_iff Ring.inverse_non_unit ciSup_of_not_bddAbove tsum_empty
  inv_mul_cancel_comm mul_inv_cancel_comm Set.iInter_of_empty CharP.cast_eq_zero IsEmpty.exists_iff
  IsMin.finsetIio_eq Set.Icc_eq_empty RCLike.star_def inf_of_le_right inf_of_le_left FunLike.coe_mul
  Nat.card_unique smul_left_inj norm_map RKHS.coe_smul tsum_comp_neg Nat.sub_self conj_trivial
  bot_eq_zero'

-- Not a `simp` lemma in Mathlib; the development uses it as one.
attribute [simp] Representation.isTrivial_def

/-- A synonym of `IsEmpty` about which `simp` knows nothing. -/
def New.IsVoid : Sort* → Prop := IsEmpty

/-- Many `simp` lemmas have a hypothesis `[IsEmpty α]`. When instance search does not find it,
`simp` tries to prove it. This lemma ends the attempt at once. -/
@[simp 1001]
lemma New.isEmpty_iff_isVoid (α : Sort*) : IsEmpty α ↔ IsVoid α := .rfl
