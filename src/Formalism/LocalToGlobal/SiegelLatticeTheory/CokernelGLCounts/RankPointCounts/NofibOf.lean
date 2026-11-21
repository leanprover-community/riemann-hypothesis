import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXCC
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.FullExists

section
namespace Formalism.L2.SG.Pf.NcReal.JX

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting

theorem nOinf_closed_under_mul_inv {D : D7} (X : HidaSetting D) (u : D.what₂.Word) :
    Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u ⊆ X.NinfU u ∧
    (∀ δ ∈ Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u, ∀ δ' ∈ Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u,
      δ * δ' ∈ Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u) ∧
    (∀ δ ∈ Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u, δ⁻¹ ∈ Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u) := by
  have hK := Formalism.L2.SG.Closed.level_subgroup_is_group X
  have hc := Formalism.L2.SG.Pf.NOsub_coe X u hK
  refine ⟨fun s hs => Formalism.L2.SG.Pf.no_sub_ninf X u hs, fun δ hδ δ' hδ' => ?_, fun δ hδ => ?_⟩
  · rw [← hc] at hδ hδ' ⊢
    exact (Formalism.L2.SG.Pf.NOsub X u hK).mul_mem hδ hδ'
  · rw [← hc] at hδ ⊢
    exact (Formalism.L2.SG.Pf.NOsub X u hK).inv_mem hδ

end Formalism.L2.SG.Pf.NcReal.JX
end

section
namespace Formalism.L2.SG.Pf.NcReal.JX

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting NumberField

def NOfibLat : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word),
    ∃ τ : ∀ p : CBlk D.R.rS, (∀ q, CSpc (InfinitePlace X.B.I.F) D.R.k q) → CSpc (InfinitePlace X.B.I.F) D.R.k p,
      (∀ p (x x' : ∀ q, CSpc (InfinitePlace X.B.I.F) D.R.k q), (∀ q, cHgt q < cHgt p → x q = x' q) → τ p x = τ p x') ∧
      ∀ x : ∀ q, CSpc (InfinitePlace X.B.I.F) D.R.k q,
        x ∈ blk X u '' Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u ↔ ∀ p, x p - τ p x ∈ cLat X u p

theorem nofib_of (hL : NOfibLat) : NOfib := by
  intro D X u
  obtain ⟨h1, h2, h3⟩ := nOinf_closed_under_mul_inv X u
  exact ⟨h1, h2, h3, hL X u⟩

end Formalism.L2.SG.Pf.NcReal.JX
end
