import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.RestDirOf
import Mathlib

section
namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial

theorem li_map {k L : Type*} [Field k] [Field L] (ι : k →+* L) {σ κ : Type*} (f : κ → MvPolynomial σ k)
    (hf : LinearIndependent k f) : LinearIndependent L (fun i => MvPolynomial.map ι (f i)) := by
  classical
  letI := ι.toAlgebra
  have hs : LinearIndepOn k id (Set.range f) := (linearIndepOn_id_range_iff hf.injective).2 hf
  let b := Module.Basis.extend hs
  let B := (Algebra.TensorProduct.basis L b).map
    (MvPolynomial.algebraTensorAlgEquiv k L).toLinearEquiv
  have hB : ∀ x, B x = MvPolynomial.map ι (x : MvPolynomial σ k) := by
    intro x
    simp only [B, b, Module.Basis.map_apply, Algebra.TensorProduct.basis_apply,
      Module.Basis.coe_extend, AlgEquiv.toLinearEquiv_apply,
      MvPolynomial.algebraTensorAlgEquiv_tmul, one_smul]
    rfl
  have hsub : Set.range f ⊆ hs.extend (Set.subset_univ _) := hs.subset_extend _
  have hinj : Function.Injective
      (fun i => (⟨f i, hsub (Set.mem_range_self i)⟩ : hs.extend (Set.subset_univ _))) := by
    intro i j hij
    exact hf.injective (congrArg Subtype.val hij)
  have := B.linearIndependent.comp _ hinj
  convert this using 1
  all_goals first
    | rfl
    | (funext i; simp only [Function.comp_apply, hB])

end Formalism.MainNotions.G.SymmetricFormBlocks
end

section
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

variable (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst)

theorem restDimBC_proved : RestDimBC C0 CE1 CE2 X := by
  intro aTop _ aPlus _ b _
  set Dd := blockData X.p (X.S C0 CE1 CE2) aTop aPlus X.m b with hDd
  set V0 := Submodule.span ℚ_[X.p]
    (((gmB Dd).SSZ X.p (r := X.r) : Submodule ℤ_[X.p] (MvPolynomial (Formalism.GM.M.BVar (2 * X.s + 1) X.r (gmB Dd).T.t) ℚ_[X.p])) :
      Set (MvPolynomial (Formalism.GM.M.BVar (2 * X.s + 1) X.r (gmB Dd).T.t) ℚ_[X.p])) with hV0
  set W := Submodule.span (KK X.O) ((Dd.SSZ X.O (r := X.r) : Submodule X.O (MvPolynomial (BVar (2 * X.s + 1) X.r Dd.T.t) (KK X.O))) :
      Set (MvPolynomial (BVar (2 * X.s + 1) X.r Dd.T.t) (KK X.O))) with hW
  show Module.finrank ℚ_[X.p] V0 ≤ Module.finrank (KK X.O) W
  have : FiniteDimensional (KK X.O) W := span_SSZ_finite Dd
  by_cases hfin : FiniteDimensional ℚ_[X.p] V0
  swap
  · rw [Module.finrank_of_not_finite hfin]
    exact Nat.zero_le _

  have hmemW : ∀ x ∈ V0, MvPolynomial.map (iotaX X) x ∈ W := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact map_SSZ (ι := iotaX X) (iotaX_int X) Dd x hx
    | zero => rw [map_zero]; exact W.zero_mem
    | add x y _ _ hx hy => rw [map_add]; exact W.add_mem hx hy
    | smul a x _ hx => rw [map_smul_Q]; exact W.smul_mem _ hx
  set bs := Module.finBasis ℚ_[X.p] V0
  have hli : LinearIndependent ℚ_[X.p] (fun i => (bs i : MvPolynomial (Formalism.GM.M.BVar (2 * X.s + 1) X.r (gmB Dd).T.t) ℚ_[X.p])) :=
    bs.linearIndependent.map' V0.subtype (Submodule.ker_subtype V0)
  have hli2 := li_map (iotaX X) _ hli
  let w : Fin (Module.finrank ℚ_[X.p] V0) → W := fun i => ⟨MvPolynomial.map (iotaX X) (bs i).1, hmemW _ (bs i).2⟩
  have hli3 : LinearIndependent (KK X.O) w := LinearIndependent.of_comp W.subtype hli2
  have h := hli3.fintype_card_le_finrank
  rw [Fintype.card_fin] at h
  exact h

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end
