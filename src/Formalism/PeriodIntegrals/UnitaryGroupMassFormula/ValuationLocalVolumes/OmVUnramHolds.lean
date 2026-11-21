import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.LocalGramMatrixFrame

noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.OmVSt.OmW

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  NumberField IsDedekindDomain

variable {D : D7} (X : HidaSetting D)

theorem finrank_OE : Module.finrank (𝓞 X.B.I.F) (𝓞 X.B.I.E) = 2 := by
  rw [← IsFractionRing.finrank_eq (𝓞 X.B.I.F) X.B.I.F (𝓞 X.B.I.E) X.B.I.E]
  exact X.B.I.cm.deg2

def tau : 𝓞 X.B.I.E →+* 𝓞 X.B.I.E := RingOfIntegers.mapRingHom (starRingEnd X.B.I.E)

theorem tau_coe (x : 𝓞 X.B.I.E) :
    algebraMap (𝓞 X.B.I.E) X.B.I.E (tau X x) = star (algebraMap (𝓞 X.B.I.E) X.B.I.E x) := rfl

theorem tau_alg (a : 𝓞 X.B.I.F) :
    tau X (algebraMap (𝓞 X.B.I.F) (𝓞 X.B.I.E) a) = algebraMap (𝓞 X.B.I.F) (𝓞 X.B.I.E) a := by
  apply RingOfIntegers.coe_injective
  rw [tau_coe, ← IsScalarTower.algebraMap_apply (𝓞 X.B.I.F) (𝓞 X.B.I.E) X.B.I.E,
    IsScalarTower.algebraMap_apply (𝓞 X.B.I.F) X.B.I.F X.B.I.E]
  exact (X.B.I.cm.fixed _).2 ⟨_, rfl⟩

theorem approx (v : HeightOneSpectrum (𝓞 X.B.I.F)) (P : Ideal (𝓞 X.B.I.E)) [P.IsMaximal]
    [P.LiesOver v.asIdeal] (hf : P.inertiaDeg (𝓞 X.B.I.F) = 1)
    (x : 𝓞 X.B.I.E) : ∃ a : 𝓞 X.B.I.F, x - algebraMap (𝓞 X.B.I.F) (𝓞 X.B.I.E) a ∈ P := by
  have := v.isMaximal
  rw [Ideal.inertiaDeg_eq_of_isMaximal v.asIdeal P] at hf
  let : Field (𝓞 X.B.I.F ⧸ v.asIdeal) := Ideal.Quotient.field _
  let : Field (𝓞 X.B.I.E ⧸ P) := Ideal.Quotient.field _
  have htop : (⊥ : Subalgebra (𝓞 X.B.I.F ⧸ v.asIdeal) (𝓞 X.B.I.E ⧸ P)) = ⊤ :=
    Subalgebra.bot_eq_top_iff_finrank_eq_one.mpr hf
  have hx : Ideal.Quotient.mk P x ∈ (⊥ : Subalgebra (𝓞 X.B.I.F ⧸ v.asIdeal) (𝓞 X.B.I.E ⧸ P)) :=
    htop ▸ Algebra.mem_top
  obtain ⟨y, hy⟩ := Algebra.mem_bot.mp hx
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  refine ⟨a, ?_⟩
  rw [← Ideal.Quotient.eq, ← hy]
  rfl


end Formalism.L2.SG.Pf.NcVal.OmVSt.OmW
