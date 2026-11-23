module

public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsKrullAkizuki
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.RingTheory.HopkinsLevitzki

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

theorem KrullAkizukiQuotientLength.proof (h : TorsionFreeQuotientLength.Statement) :
    KrullAkizukiQuotientLength.Statement := by
  intro R _ _ _ hdim K _ _ _ L _ _ _ _ _ S b hb

  have hinj : Function.Injective (algebraMap R S) := by
    intro x y hxy
    have h1 : algebraMap R L x = algebraMap R L y := by
      simpa using congrArg (fun s : S => (s : L)) hxy
    rw [IsScalarTower.algebraMap_apply R K L, IsScalarTower.algebraMap_apply R K L] at h1
    exact IsFractionRing.injective R K ((algebraMap K L).injective h1)
  have : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr hinj
  have : Module.IsTorsionFree R S := inferInstance

  have hrankL : Module.rank R L = Module.rank K L :=
    (IsLocalization.rank_eq K (nonZeroDivisors R) le_rfl).symm
  have hlt : Module.rank R S < Cardinal.aleph0 :=
    lt_of_le_of_lt (by rw [← hrankL]; exact Submodule.rank_le (Subalgebra.toSubmodule S))
      (Module.rank_lt_aleph0 K L)
  obtain ⟨r, hr⟩ := Cardinal.lt_aleph0.mp hlt

  have hdim0 : Ring.KrullDimLE 0 (R ⧸ Ideal.span {b}) := by
    rw [Ring.krullDimLE_iff]
    have h2 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hb)
    rw [hdim] at h2
    generalize ringKrullDim (R ⧸ Ideal.span {b}) = d at h2 ⊢
    cases d with
    | bot => exact bot_le
    | coe n =>
      have h3 : n + 1 ≤ 1 := by exact_mod_cast h2
      induction n using ENat.recTopCoe with
      | top => simp at h3
      | coe k =>
        have hk : k + 1 ≤ 1 := by exact_mod_cast h3
        obtain rfl : k = 0 := by omega
        simp
  have : IsArtinianRing (R ⧸ Ideal.span {b}) :=
    IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
  have hRlen : Module.length R (R ⧸ Ideal.span {b}) ≠ ⊤ := by
    rw [Module.length_ne_top_iff, isFiniteLength_iff_isNoetherian_isArtinian]
    exact ⟨inferInstance, isArtinian_of_surjective_algebraMap
      (Ideal.Quotient.mk_surjective (I := Ideal.span {b}))⟩

  have hle := h R hdim S r hr b hb
  have hfin : IsFiniteLength R (S ⧸ (Ideal.span {b} • ⊤ : Submodule R S)) :=
    Module.length_ne_top_iff.mp
      (ne_top_of_le_ne_top (WithTop.mul_ne_top (ENat.natCast_ne_top r) hRlen) hle)

  have heq : (Ideal.span {b} • ⊤ : Submodule R S) =
      (Ideal.span {algebraMap R S b}).restrictScalars R := by
    ext x
    simp only [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists,
      Submodule.mem_top, true_and, Submodule.restrictScalars_mem, Ideal.mem_span_singleton',
      Algebra.smul_def, mul_comm]
  rw [heq] at hfin
  exact hfin.of_surjective (f := (Submodule.Quotient.restrictScalarsEquiv R _).toLinearMap)
    (Submodule.Quotient.restrictScalarsEquiv R _).surjective

end GroundTheory.Heights₂.Heights.Model
