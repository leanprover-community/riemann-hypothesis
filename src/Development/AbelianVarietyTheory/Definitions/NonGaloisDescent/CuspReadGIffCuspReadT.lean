import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
import CompanionTheory.EightfoldTheory.ZeroLevelTheory.LocalLanglands.Imports
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CGTrueT
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspReadTOfCuspRead
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClsLocEqOfIsLocComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormsFiniteGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.NotIsComplementaryProductAbsPow

section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.BasicNotions Formalism.MainNotions.N

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.DefiniteBC

attribute [local instance] host_isCMField

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂}
variable {A : NAut N}

def CuspReadG (rc : RecMap A) : Prop :=
  ∀ (a : ℕ) (P : CuspSub H.E a), 1 ≤ a → P.IsCsd →
    (∀ w (σ : LocIrr w a), P.IsLocComp w σ → UpperTheory.Zero.LLC.Good (GlobalTheory.LocGL.IrrGL.of σ.ρ σ.smooth σ.irred)) →
    ∃ π : A.CG a, A.csd π ∧ (∀ w σ, P.IsLocComp w σ → A.locG π w = rc w a σ) ∧ ∀ τ m, P.HasInfChar τ m → A.infG π τ = m

end GlobalTheory.DefiniteBC

end
end

section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.DefiniteBC GlobalTheory.RowTie

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.DefiniteBC.GoodModel

attribute [local instance] host_isCMField

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}




theorem good_rank_one {w : PlE H} (σ : LocIrr w 1) : UpperTheory.Zero.LLC.Good (IrrGL.of σ.ρ σ.smooth σ.irred) := by
  have hc : (IrrGL.of σ.ρ σ.smooth σ.irred).IsCusp :=
    IrrGL.isCusp_of.2 ⟨one_pos, GlobalTheory.GenericUnitary.isCuspidal_of_isSmooth_one σ.smooth⟩
  refine ⟨_, hasSupport_self hc, fun y hy => ?_⟩
  left; rw [Multiset.mem_singleton.1 hy]; rfl

theorem rank_one {rc : RecMap A} (h : CuspReadG rc) (P : CuspSub H.E 1) (hc : P.IsCsd) :
    ∃ π : A.CG 1, A.csd π ∧ (∀ w σ, P.IsLocComp w σ → A.locG π w = rc w 1 σ) ∧
      ∀ τ m, P.HasInfChar τ m → A.infG π τ = m :=
  h 1 P le_rfl hc fun _ σ _ => good_rank_one σ

theorem isCsd_triv : (CuspSub.triv H.E (le_refl 1)).IsCsd := by
  refine ⟨LinearEquiv.refl ℂ _, fun o φ => Subtype.ext ?_⟩
  obtain ⟨φ, hφ⟩ := φ
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hφ
  change act (thetaOp o) (c • oneFn H.E 1) = act o (c • oneFn H.E 1)
  rw [map_smul, map_smul, act_oneFn, act_oneFn]
  cases o <;> rfl

theorem exists_member {rc : RecMap A} (h : CuspReadG rc) :
    ∃ π : A.CG 1, A.csd π ∧ ∀ w, ∃ σ, (CuspSub.triv H.E (le_refl 1)).IsLocComp w σ ∧ A.locG π w = rc w 1 σ := by
  obtain ⟨π, h1, h2, -⟩ := rank_one h _ isCsd_triv
  refine ⟨π, h1, fun w => ?_⟩
  obtain ⟨σ, hσ, -⟩ := LocEx.exists_isLocComp GlobalTheory.automorphicFormsFiniteGL H.E 1 (CuspSub.triv H.E (le_refl 1)) w
  exact ⟨σ, hσ, h2 w σ hσ⟩


end GlobalTheory.DefiniteBC.GoodModel

end
end
