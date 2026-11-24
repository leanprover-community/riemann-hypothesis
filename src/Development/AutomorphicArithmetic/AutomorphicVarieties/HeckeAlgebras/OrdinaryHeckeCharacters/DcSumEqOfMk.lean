module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.ContinuousTorusCharacter
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open IsLocalRing Matrix UpperTheory.V.Hi

private theorem dcSum_eq_of_mk {A H M : Type} [CommRing A] [Group H] [AddCommGroup M] [Module A M]
    (ρ : Representation A H M) (K' : Subgroup H) {v : M} (hv : v ∈ fixd ρ K') {y z : H}
    (h : (y : H ⧸ K') = (z : H ⧸ K')) : ρ y v = ρ z v := by
  have h1 : y⁻¹ * z ∈ K' := QuotientGroup.eq.mp h
  have h2 : ρ (y⁻¹ * z) v = v := hv _ h1
  calc ρ y v = ρ y (ρ (y⁻¹ * z) v) := by rw [h2]
    _ = ρ (y * (y⁻¹ * z)) v := by rw [map_mul ρ y]; rfl
    _ = ρ z v := by rw [mul_inv_cancel_left]

private theorem dcSum_apply {A H M : Type} [CommRing A] [Group H] [AddCommGroup M] [Module A M]
    (ρ : Representation A H M) (K K' : Subgroup H) (x : H)
    [Fintype (MulAction.orbit K (x : H ⧸ K'))] (v : M) :
    dc ρ K K' x v = ∑ q : MulAction.orbit K (x : H ⧸ K'), ρ (q : H ⧸ K').out v := by
  rw [dc, finsum_eq_sum_of_fintype, LinearMap.sum_apply]

theorem UpperTheory.V.Hi.dcSum :
    ∀ (A H M : Type) [CommRing A] [Group H] [AddCommGroup M] [Module A M] (ρ : Representation A H M) (K K' : Subgroup H) (x : H), (MulAction.orbit K (x : H ⧸ K')).Finite → (∀ s : Finset H, (∀ y ∈ s, (y : H ⧸ K') ∈ MulAction.orbit K (x : H ⧸ K')) → (∀ q ∈ MulAction.orbit K (x : H ⧸ K'), ∃! y, y ∈ s ∧ (y : H ⧸ K') = q) → ∀ v ∈ fixd ρ K', dc ρ K K' x v = ∑ y ∈ s, ρ y v) ∧ (∀ v ∈ fixd ρ K', dc ρ K K' x v ∈ fixd ρ K) ∧ (∀ V : Subgroup H, (∀ u ∈ V, u * x = x * u ∧ ∀ k ∈ K, u * k = k * u) → ∀ v ∈ fixd ρ K', v ∈ fixd ρ V → dc ρ K K' x v ∈ fixd ρ V) ∧ ∀ (A' M' : Type) [CommRing A'] [AddCommGroup M'] [Module A' M'] (ρ' : Representation A' H M') (f : M →+ M'), (∀ h v, f (ρ h v) = ρ' h (f v)) → ∀ v, f (dc ρ K K' x v) = dc ρ' K K' x (f v) := by
  intro A H M _ _ _ _ ρ K K' x hfin
  letI : Fintype (MulAction.orbit K (x : H ⧸ K')) := hfin.fintype
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s hs hu v hv
    rw [dcSum_apply]
    symm
    refine Finset.sum_bij (fun y hy => (⟨(y : H ⧸ K'), hs y hy⟩ : MulAction.orbit K (x : H ⧸ K')))
      (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
    · intro y hy z hz h
      have h' : (y : H ⧸ K') = (z : H ⧸ K') := congrArg Subtype.val h
      exact (hu _ (hs z hz)).unique ⟨hy, h'⟩ ⟨hz, rfl⟩
    · intro q _
      obtain ⟨y, ⟨hy, hq⟩, -⟩ := hu q.1 q.2
      exact ⟨y, hy, Subtype.ext hq⟩
    · intro y hy
      exact dcSum_eq_of_mk ρ K' hv (QuotientGroup.out_eq' _).symm
  · intro v hv u hu

    rw [dcSum_apply, map_sum]
    refine Fintype.sum_equiv (MulAction.toPerm (⟨u, hu⟩ : K)) _ _ ?_
    intro q
    have : ρ u (ρ (q : H ⧸ K').out v) = ρ (u * (q : H ⧸ K').out) v := by rw [map_mul]; rfl
    rw [this]
    apply dcSum_eq_of_mk ρ K' hv
    rw [QuotientGroup.out_eq']
    change _ = u • (q : H ⧸ K')
    conv_rhs => rw [← QuotientGroup.out_eq' (q : H ⧸ K')]
    rfl
  · intro V hV v hv hvV u hu

    rw [dcSum_apply, map_sum]
    refine Finset.sum_congr rfl ?_
    rintro ⟨q, k, hk⟩ _
    have h1 : ρ q.out v = ρ ((k : H) * x) v := by
      apply dcSum_eq_of_mk ρ K' hv
      rw [QuotientGroup.out_eq', ← hk]
      rfl
    have h2 : u * ((k : H) * x) = ((k : H) * x) * u := by
      rw [← mul_assoc, (hV u hu).2 k k.2, mul_assoc, (hV u hu).1, mul_assoc]
    change ρ u (ρ q.out v) = ρ q.out v
    rw [h1]
    calc ρ u (ρ ((k : H) * x) v) = ρ (u * ((k : H) * x)) v := by rw [map_mul ρ u]; rfl
      _ = ρ ((k : H) * x) (ρ u v) := by rw [h2, map_mul ρ _ u]; rfl
      _ = _ := by rw [hvV u hu]
  · intro A' M' _ _ _ ρ' f hf v

    rw [dcSum_apply, dcSum_apply, map_sum]
    exact Finset.sum_congr rfl fun q _ => hf _ _
