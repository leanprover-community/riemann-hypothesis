module

public import Mathlib.Topology.KrullDimension

@[expose] public section

open Set Topology TopologicalSpace

namespace LateralTheory.E.CurveKrullDim

variable {X : Type} [TopologicalSpace X]

theorem two_le_dim (A B : IrreducibleCloseds X) (hAB : (A : Set X) ⊂ B) (hB : (B : Set X) ≠ univ)
    [IrreducibleSpace X] : (2 : WithBot ℕ∞) ≤ topologicalKrullDim X := by
  let T : IrreducibleCloseds X := ⟨univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
  have h1 : A < B := by
    rw [← SetLike.coe_ssubset_coe]; exact hAB
  have h2 : B < T := by
    rw [← SetLike.coe_ssubset_coe]; exact ssubset_univ_iff.mpr hB
  let initial : LTSeries (IrreducibleCloseds X) := RelSeries.singleton _ A
  let pair := initial.snoc B h1
  let series := pair.snoc T (by
    change pair.last < T
    exact (RelSeries.last_snoc initial B h1).symm ▸ h2)
  unfold topologicalKrullDim
  exact Order.le_krullDim_iff.mpr ⟨series, rfl⟩

theorem closed_of_ne_univ [IrreducibleSpace X] [T0Space X] (hd : topologicalKrullDim X ≤ 1) (z : X)
    (hz : closure ({z} : Set X) ≠ univ) : IsClosed ({z} : Set X) := by
  rw [← closure_subset_iff_isClosed]
  intro y hy
  by_contra hne
  have hyz : closure ({y} : Set X) ⊂ closure {z} := by
    refine ⟨closure_minimal (singleton_subset_iff.mpr hy) isClosed_closure, fun h => hne ?_⟩
    have h1 : z ⤳ y := specializes_iff_mem_closure.mpr hy
    have h2 : y ⤳ z := specializes_iff_mem_closure.mpr (h (subset_closure rfl))
    exact (h1.antisymm h2).eq.symm
  have := two_le_dim ⟨closure {y}, isIrreducible_singleton.closure, isClosed_closure⟩
    ⟨closure {z}, isIrreducible_singleton.closure, isClosed_closure⟩ hyz hz
  exact (by decide : ¬ (2 : WithBot ℕ∞) ≤ 1) (this.trans hd)

theorem finite_of_closed [IrreducibleSpace X] [T0Space X] [QuasiSober X] [NoetherianSpace X]
    (hd : topologicalKrullDim X ≤ 1) (Z : Set X) (hZ : IsClosed Z) (hne : Z ≠ univ) : Z.Finite := by
  let : QuasiSober Z := hZ.isClosedEmbedding_subtypeVal.quasiSober
  have hpt (z : Z) : IsClosed ({z} : Set Z) := by
    have hz : closure ({z.val} : Set X) ≠ univ := fun h =>
      hne (eq_univ_of_univ_subset (h ▸ closure_minimal (singleton_subset_iff.mpr z.property) hZ))
    rw [← preimage_image_eq {z} Subtype.val_injective, image_singleton]
    exact (closed_of_ne_univ hd z.val hz).preimage continuous_subtypeVal
  have hfin : (univ : Set Z).Finite := by
    rw [← sUnion_irreducibleComponents]
    refine NoetherianSpace.finite_irreducibleComponents.sUnion fun S hS => ?_
    obtain ⟨z, hz⟩ := QuasiSober.sober hS.1 (isClosed_of_mem_irreducibleComponents S hS)
    rw [← hz.def, (hpt z).closure_eq]
    exact finite_singleton z
  exact finite_coe_iff.mp (finite_univ_iff.mp hfin)

end LateralTheory.E.CurveKrullDim
