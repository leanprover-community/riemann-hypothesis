module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.StrongApproxN
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.BridgeFinK

@[expose] public section

noncomputable section

open Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.TypedSets
open Matrix

namespace MassDataMassesW.NBr

theorem bridgeK_holds : BridgeK := by
  intro D X hb x
  have hbr' : X.B.I.fmat x = _ := (hb.choose_spec (1, x)).2
  have hK : x ∈ X.B.I.Kset ↔
      Formalism.L2.SG.AdBridge.toHA X.B.I hb (1, x) ∈ Formalism.L2.SG.AdBridge.KfHA X.B.I := by
    refine Iff.trans ?_ (adelic_compact_finite_places X.B.I (Formalism.L2.SG.AdBridge.toHA X.B.I hb (1, x)))
    show (∀ y, y ∈ X.B.I.Lf ↔ X.B.I.fmat x *ᵥ y ∈ X.B.I.Lf) ↔ _
    rw [hbr']
    rfl
  refine hK.trans ?_
  simp only [KX, Formalism.L2.SG.Sub.Kf, Subgroup.mem_iInf, Subgroup.mem_comap, MonoidHom.comp_apply,
    incAf_finHA]
  rfl

end MassDataMassesW.NBr
