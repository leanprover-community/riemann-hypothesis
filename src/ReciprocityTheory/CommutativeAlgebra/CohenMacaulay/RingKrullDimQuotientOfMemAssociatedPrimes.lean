module

public import ReciprocityTheory.CommutativeAlgebra.ChainConnInDim
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.Bridge
public import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.Unmixed
public import Mathlib.RingTheory.KrullDimension.Module

@[expose] public section

namespace ReciprocityTheory.CA

open IsLocalRing RingTheory.Sequence Pointwise

variable {R : Type*} [CommRing R] [IsLocalRing R]

private theorem smul_top_eq_self' (I : Ideal R) : (I • (⊤ : Submodule R R)) = I := by
  exact Ideal.mul_top I

private theorem span_singleton_eq_smul_top' (x : R) :
    (x • (⊤ : Submodule R R)) = Ideal.span {x} := by
  rw [← Submodule.ideal_span_singleton_smul, smul_top_eq_self']

private theorem isSMulRegular_of_mem_nonZeroDivisors' {x : R} (reg : x ∈ nonZeroDivisors R) :
    IsSMulRegular R x := by
  intro a b hab
  have h0 : (a - b) * x = 0 := by
    simp only [smul_eq_mul] at hab
    rw [sub_mul, mul_comm a, mul_comm b, hab, sub_self]
  exact sub_eq_zero.mp ((mem_nonZeroDivisors_iff.mp reg).2 _ h0)

private noncomputable def quotSMulTopEquivQuot' (x : R) :
    QuotSMulTop x R ≃ₗ[R] R ⧸ Ideal.span {x} :=
  Submodule.quotEquivOfEq _ _ (span_singleton_eq_smul_top' x)

theorem isCM_of_quotient_span_singleton [IsNoetherianRing R] {x : R} (hx : x ∈ maximalIdeal R)
    (reg : x ∈ nonZeroDivisors R) [IsLocalRing (R ⧸ Ideal.span {x})]
    (h : IsCM (R ⧸ Ideal.span {x})) : IsCM R := by
  exact isCM_iff_isCMMod.mpr (IsCMMod.of_quotSMulTop hx (isSMulRegular_of_mem_nonZeroDivisors' reg)
    ((isCMMod_congr (quotSMulTopEquivQuot' x)).mpr ((isCM_quotient_iff _).mp h)))

theorem IsCM.quotient_ofList (h : IsCM R) {rs : List R} (hrs : ∀ r ∈ rs, r ∈ maximalIdeal R)
    (reg : IsRegular R rs) [IsLocalRing (R ⧸ Ideal.ofList rs)] :
    IsCM (R ⧸ Ideal.ofList rs) := by
  haveI : IsNoetherianRing R := h.1
  have h1 := (isCM_iff_isCMMod.mp h).quotient_ofList hrs reg
  exact (isCM_quotient_iff _).mpr
    ((isCMMod_congr (Submodule.quotEquivOfEq _ _ (smul_top_eq_self' _))).mp h1)

theorem IsCM.isRegular_of_isArtinianRing_quotient (h : IsCM R) (xs : List R)
    (hxs : ∀ r ∈ xs, r ∈ maximalIdeal R) (hlen : (xs.length : WithBot ℕ∞) = ringKrullDim R)
    (hart : IsArtinianRing (R ⧸ Ideal.ofList xs)) : IsRegular R xs := by
  apply (isCM_iff_isCMMod.mp h).isRegular_of_supportDim_quotient_le_zero xs hxs
  · rw [Module.supportDim_self_eq_ringKrullDim]; exact hlen
  · rw [Module.supportDim_eq_of_equiv (Submodule.quotEquivOfEq _ _ (smul_top_eq_self' _)),
      Module.supportDim_quotient_eq_ringKrullDim]
    exact Ring.krullDimLE_iff.mp inferInstance

end ReciprocityTheory.CA
