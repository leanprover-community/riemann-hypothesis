module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SelfDualLocalBasis.DualBasis
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SelfDualLocalBasis.HformSumRight
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix NumberField IsDedekindDomain

noncomputable section

namespace PI.SelfDualLoc.W

open PI.SelfDualLoc

def hvec {E : Type} [Field E] {n m : ℕ} (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E)
    (x : Fin m → Fin n → E) : (Fin n → E) →ₗ[E] (Fin m → E) where
  toFun y := fun i => hform σ J (x i) y
  map_add' y y' := by ext i; simp [hform_add_right]
  map_smul' c y := by ext i; simp [hform_smul_right]

theorem hvec_apply {E : Type} [Field E] {n m : ℕ} (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E)
    (x : Fin m → Fin n → E) (y : Fin n → E) (i : Fin m) :
    hvec σ J x y i = hform σ J (x i) y := rfl

theorem spanTop_of (hN : Nondeg) : SpanTop := by
  intro F E _ _ _ _ _ n σ J Lb T hfin hdual hT
  by_contra hne
  have hlt : Module.finrank E (Submodule.span E (Lb : Set (Fin n → E))) < n := by
    have h := Submodule.finrank_lt hne
    rwa [Module.finrank_fin_fun] at h
  let b := Module.finBasis E (Submodule.span E (Lb : Set (Fin n → E)))
  let x : Fin (Module.finrank E (Submodule.span E (Lb : Set (Fin n → E)))) → Fin n → E :=
    fun i => (b i : Fin n → E)
  have hker : LinearMap.ker (hvec (σ : E →+* E) J x) ≠ ⊥ := by
    intro hbot
    have h1 := LinearMap.finrank_range_add_finrank_ker (hvec (σ : E →+* E) J x)
    rw [hbot, finrank_bot, add_zero, Module.finrank_fin_fun] at h1
    have h2 := Submodule.finrank_le (LinearMap.range (hvec (σ : E →+* E) J x))
    rw [Module.finrank_fin_fun] at h2
    omega
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  apply hy0
  refine hN F E n σ J Lb T hfin hdual hT y fun z hz => ?_
  have hzV : z ∈ Submodule.span E (Lb : Set (Fin n → E)) := Submodule.subset_span hz
  have hz' : z = ∑ i, (b.repr ⟨z, hzV⟩ i) • x i := by
    have h := congrArg Subtype.val (b.sum_repr ⟨z, hzV⟩)
    rw [Submodule.coe_sum] at h
    exact h.symm
  rw [hz', hform_sum_left]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [hform_smul_left]
  have hi : hform (σ : E →+* E) J (x i) y = 0 := by
    rw [← hvec_apply]
    exact congrFun (LinearMap.mem_ker.mp hy) i
  rw [hi, mul_zero]

theorem dualBasis : DualBasis := by
  intro F E _ _ _ _ _ n σ J x _ hnd
  have hinj : Function.Injective (hvec (σ : E →+* E) J x) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    exact hnd y fun i => by rw [← hvec_apply, hy]; rfl
  let e := LinearEquiv.ofInjectiveEndo (hvec (σ : E →+* E) J x) hinj
  have he : ∀ v, e v = hvec (σ : E →+* E) J x v := fun v => rfl
  refine ⟨fun j => e.symm (Pi.single j 1), fun i j => ?_, fun w => ⟨fun j => e w j, ?_⟩⟩
  · rw [← hvec_apply, ← he, LinearEquiv.apply_symm_apply, Pi.single_apply]
  · apply e.injective

    rw [map_sum]
    simp only [map_smul, LinearEquiv.apply_symm_apply]
    ext i
    simp [Finset.sum_apply, Pi.single_apply]

end PI.SelfDualLoc.W
