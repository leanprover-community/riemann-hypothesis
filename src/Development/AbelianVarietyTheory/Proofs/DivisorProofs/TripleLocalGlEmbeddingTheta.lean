import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnitaryElementActsLocalOperatorAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroComplementaryAdelicSchwartzFunction
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinPartIdemMulMemIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SwapNegApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocIsoRefl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodSplitPlaceTranslationActsThroughWeil
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearFormEqZeroOfKillsProductSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerPreservesAdelicSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SliceTransformSchwartzBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalIdempotentCharacterValue
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSmulOfCommuteHeisenbergLinearModelSchwartzBruh
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergOperatorIsotropicTranslationCharSplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledVacuumTwistedVacuumConditionDoubledLattic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlaceAdelicMatrixGivenComponents

section
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.SwapAtSplit

open scoped TensorProduct
open GlobalTheory.EmbChart (atPlace tensAt compFin_tensAt tensAt_mul_right sigR_tensAt)

theorem exists_swap_elt : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (v : Pl F) (t : E →ₐ[F] Fv F v), ∃ f : AE F E,
      GlobalTheory.LatVac.liftV v (1 : Fv F v) • f = f ∧ f * f = algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) ∧
      f * cA σ f = -algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) ∧ piW t f = 1 ∧ piW (t.comp σ) f = -1 := by
  intro F E _ _ _ _ _ σ h v t
  set y : Fv F v ⊗[F] E := (splitAlgEquiv h t).symm (1, -1) with hy
  have hQ : algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) = tensAt E v 1 := rfl
  have hpi : ∀ τ : E →ₐ[F] Fv F v, piW τ (tensAt E v y) = splitProj τ y := fun τ => by
    change splitProj τ (compFin F E v (tensAt E v y)) = _
    rw [compFin_tensAt]
  refine ⟨tensAt E v y, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Algebra.smul_def, mul_comm, tensAt_mul_right]
    have e : compFin F E v (algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1)) = 1 := by
      change GlobalTheory.AdelicU.evFin F v (GlobalTheory.LatVac.liftV v 1) ⊗ₜ[F] (1 : E) = 1
      rw [GlobalTheory.LatVac.evFin_liftV]; rfl
    rw [e, mul_one]
  · rw [hQ, tensAt_mul_right, compFin_tensAt]
    congr 1
    exact split_ext h t (by simp [hy]) (by simp [hy])
  · have hc : cA σ (tensAt E v y) = tensAt E v (sigR (Fv F v) σ y) := sigR_tensAt v σ y
    rw [hc, hQ, tensAt_mul_right, compFin_tensAt, ← map_neg]
    congr 1
    refine split_ext h t ?_ ?_
    · rw [map_mul, ← splitProj_comp, map_neg, map_one]; simp [hy]
    · rw [map_mul, splitProj_comp_sigR h, map_neg, map_one]; simp [hy]
  · rw [hpi]; simp [hy]
  · rw [hpi]; simp [hy]

end GlobalTheory.SwapAtSplit
end
end

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_idempotent_conjugation_sign : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (v : Pl F) (t : E →ₐ[F] Fv F v), ∃ f : AE F E,
      GlobalTheory.LatVac.liftV v (1 : Fv F v) • f = f ∧ f * f = algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) ∧
      f * cA σ f = -algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) ∧ piW t f = 1 ∧ piW (t.comp σ) f = -1 := by
  atlas_forward_decl GlobalTheory.SwapAtSplit.exists_swap_elt
end

section
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.DblDiag

open Matrix

theorem swap_at_place : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : Pl F) (f : AE F E),
    GlobalTheory.LatVac.liftV v (1 : Fv F v) • f = f → f * f = algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) →
    f * cA σ f = -algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) →
    ∃ w : UG (cA σ) (dbl (incM F J)),
      ((w : GL (Fin n ⊕ Fin n) (AE F E)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) =
        Matrix.fromBlocks ((1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • (1 : Matrix (Fin n) (Fin n) (AE F E))) (f • 1) (f • 1)
          ((1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • 1) ∧
      At (evFin F v) (((w : GL (Fin n ⊕ Fin n) (AE F E)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) - 1) ∧
      w * w = 1 ∧
      ∀ k : UA σ J, At (evFin F v) (mat k - 1) → ∀ gd gd' : UG (cA σ) (dbl (incM F J)),
        ((gd : GL (Fin n ⊕ Fin n) (AE F E)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) = Matrix.fromBlocks (mat k) 0 0 1 →
        ((gd' : GL (Fin n ⊕ Fin n) (AE F E)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) = Matrix.fromBlocks 1 0 0 (mat k) →
        w * gd * w = gd' := by
  intro F E _ _ _ _ _ σ n J v f hQf hff hfc
  set Q : AF F := GlobalTheory.LatVac.liftV v (1 : Fv F v) with hQdef
  have hQQ : Q * Q = Q := by
    have h := GlobalTheory.LatVac.at_liftV v (1 : Fv F v) (1 - Q)
      (by rw [map_sub, map_one, hQdef, GlobalTheory.LatVac.evFin_liftV, sub_self])
    rw [← hQdef, smul_eq_mul, sub_mul, one_mul, sub_eq_zero] at h
    exact h.symm
  set q : AE F E := algebraMap (AF F) (AE F E) Q with hqdef
  set p : AE F E := algebraMap (AF F) (AE F E) (1 - Q) with hpdef
  have hp : p = 1 - q := by rw [hpdef, map_sub, map_one]
  have hqq : q * q = q := by rw [hqdef, ← map_mul, hQQ]
  have hqf : q * f = f := by rw [hqdef, ← Algebra.smul_def]; exact hQf
  have hcp : cA σ p = p := AlgHom.commutes _ _
  have hpp : p * p = p := by rw [hp]; linear_combination hqq
  have hpf : p * f = 0 := by rw [hp]; linear_combination -hqf
  have hpcf : p * cA σ f = 0 := by rw [← hcp, ← map_mul, hpf, map_zero]
  have hsm : ∀ (m : Type) [Fintype m] [DecidableEq m] (N : Matrix m m (AE F E)), (1 - Q) • N = p • N :=
    fun m _ _ N => (algebraMap_smul (AE F E) (1 - Q) N).symm
  have hmap : ∀ a : AE F E, (a • (1 : Matrix (Fin n) (Fin n) (AE F E))).map (cA σ) = cA σ a • 1 := by
    intro a; ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, Matrix.one_apply]
    split_ifs <;> simp
  set M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E) :=
    Matrix.fromBlocks ((1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • (1 : Matrix (Fin n) (Fin n) (AE F E))) (f • 1) (f • 1)
      ((1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • 1) with hMdef
  have hM : M = Matrix.fromBlocks (p • 1) (f • 1) (f • 1) (p • 1) := by
    rw [hMdef, ← hQdef, hsm]

  have hMM : M * M = 1 := by
    rw [hM, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul]
    congr 1 <;> ext i j <;> simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]
    · linear_combination (1 : Matrix (Fin n) (Fin n) (AE F E)) i j * (hpp + hff + hp)
    · linear_combination (1 : Matrix (Fin n) (Fin n) (AE F E)) i j * (2 * hpf)
    · linear_combination (1 : Matrix (Fin n) (Fin n) (AE F E)) i j * (2 * hpf)
    · linear_combination (1 : Matrix (Fin n) (Fin n) (AE F E)) i j * (hpp + hff + hp)
  have hU : Mᵀ * dbl (incM F J) * M.map (cA σ) = dbl (incM F J) := by
    rw [hM, dbl, Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_multiply]
    simp only [Matrix.transpose_smul, Matrix.transpose_one, hmap, hcp, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_neg,
      Matrix.neg_mul, smul_smul, smul_neg]
    congr 1 <;> ext i j <;>
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply, Matrix.neg_apply]
    all_goals
      first
        | linear_combination incM F J i j * (hpp - hfc + hp)
        | linear_combination incM F J i j * (hfc - hpp - hp)
        | linear_combination incM F J i j * (hpcf - hpf)
        | linear_combination incM F J i j * (hpf - hpcf)
        | linear_combination incM F J i j * (hpcf + hpf)
        | linear_combination incM F J i j * (-hpcf - hpf)

  refine ⟨⟨⟨M, M, hMM, hMM⟩, hU⟩, rfl, ?_, Subtype.ext (Units.ext hMM), ?_⟩
  · intro u hu
    show u • (M - 1) = 0
    have hQu : u * Q = 0 := by
      have h := GlobalTheory.LatVac.at_liftV v (1 : Fv F v) u hu
      rwa [← hQdef, smul_eq_mul] at h
    set ua : AE F E := algebraMap (AF F) (AE F E) u with huadef
    have huq : ua * q = 0 := by rw [huadef, hqdef, ← map_mul, hQu, map_zero]
    have huf : ua * f = 0 := by rw [← hqf]; linear_combination f * huq
    rw [← algebraMap_smul (AE F E) u, ← huadef, hM, ← Matrix.fromBlocks_one]
    ext (i | i) (j | j) <;>
      simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, smul_eq_mul] <;>
      first
          | linear_combination 1 * ((ua * (1 : Matrix (Fin n) (Fin n) (AE F E)) i j) * hp - (1 : Matrix (Fin n) (Fin n) (AE F E)) i j * huq)
          | linear_combination 1 * ((1 : Matrix (Fin n) (Fin n) (AE F E)) i j * huf)
          | linear_combination 1 * (-((1 : Matrix (Fin n) (Fin n) (AE F E)) i j * huf))
          | linear_combination 1 * (- (ua * (1 : Matrix (Fin n) (Fin n) (AE F E)) i j) * hp + (1 : Matrix (Fin n) (Fin n) (AE F E)) i j * huq)
          | linear_combination 1 * ((ua * (1 : Matrix (Fin n) (Fin n) (AE F E)) i j) * hp + (1 : Matrix (Fin n) (Fin n) (AE F E)) i j * huq)
          | linear_combination 1 * (-(ua * (1 : Matrix (Fin n) (Fin n) (AE F E)) i j) * hp - (1 : Matrix (Fin n) (Fin n) (AE F E)) i j * huq)
  · intro k hk gd gd' hgd hgd'
    apply Subtype.ext
    apply Units.ext
    show M * ((gd : GL (Fin n ⊕ Fin n) (AE F E)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) * M =
      ((gd' : GL (Fin n ⊕ Fin n) (AE F E)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E))
    have hK : p • (mat k - 1) = 0 := by
      rw [← hsm]
      exact hk (1 - Q) (by rw [map_sub, map_one, hQdef, GlobalTheory.LatVac.evFin_liftV, sub_self])
    have hKe : ∀ i j, p * mat k i j = p * (1 : Matrix (Fin n) (Fin n) (AE F E)) i j := by
      intro i j
      have h := congrFun (congrFun hK i) j
      simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.zero_apply, smul_eq_mul] at h
      linear_combination h
    rw [hgd, hgd', hM, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero,
      add_zero, zero_add, smul_smul, smul_zero]
    congr 1 <;> ext i j <;>
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]
    all_goals
      first
        | linear_combination 1 * (mat k i j * hpp + hKe i j + (1 : Matrix (Fin n) (Fin n) (AE F E)) i j * hff + (1 : Matrix (Fin n) (Fin n) (AE F E)) i j * hp)
        | linear_combination 1 * (mat k i j * hpf + (1 : Matrix (Fin n) (Fin n) (AE F E)) i j * hpf)
        | linear_combination 1 * (mat k i j * hff + (1 : Matrix (Fin n) (Fin n) (AE F E)) i j * hpp + mat k i j * hp - hKe i j)

end GlobalTheory.DblDiag
end
end

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_weyl_element_doubled : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : Pl F) (f : AE F E),
    GlobalTheory.LatVac.liftV v (1 : Fv F v) • f = f → f * f = algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) →
    f * cA σ f = -algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) →
    ∃ w : UG (cA σ) (dbl (incM F J)),
      ((w : GL (Fin n ⊕ Fin n) (AE F E)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) =
        Matrix.fromBlocks ((1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • (1 : Matrix (Fin n) (Fin n) (AE F E))) (f • 1) (f • 1)
          ((1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • 1) ∧
      At (evFin F v) (((w : GL (Fin n ⊕ Fin n) (AE F E)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) - 1) ∧
      w * w = 1 ∧
      ∀ k : UA σ J, At (evFin F v) (mat k - 1) → ∀ gd gd' : UG (cA σ) (dbl (incM F J)),
        ((gd : GL (Fin n ⊕ Fin n) (AE F E)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) = Matrix.fromBlocks (mat k) 0 0 1 →
        ((gd' : GL (Fin n ⊕ Fin n) (AE F E)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) = Matrix.fromBlocks 1 0 0 (mat k) →
        w * gd * w = gd' := by
  atlas_forward_decl GlobalTheory.DblDiag.swap_at_place
end

section
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny

namespace GlobalTheory.LocSplitOp

theorem exists_locOp : ∀ {F : Type} [Field F] [NumberField F] {W : Type} [AddCommGroup W] [Module (AF F) W] {Bf : W → W → AF F} {κ : Type} [Fintype κ]
    (dd : Darboux Bf κ) (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ {G : Type} [Group G] (act : G → W → W) (om : G →* Module.End ℂ ((κ → AF F) → ℂ)),
    IsSplitting (adeleClass F) ψ dd act om →
    ∀ (v : Pl F) (p : G), (∀ u, At (evFin F v) u → At (evFin F v) (act p u)) →
    (∀ Φ ∈ SB (κ → Fv F v), ∃ Φ₁ ∈ SB (κ → Fv F v), Acts (evFin F v) (om p) Φ Φ₁) →
    ∃ S : ((κ → Fv F v) → ℂ) → (κ → Fv F v) → ℂ,
      (∀ Φ ∈ SB (κ → Fv F v), S Φ ∈ SB (κ → Fv F v) ∧ Acts (evFin F v) (om p) Φ (S Φ)) ∧
      ∀ u, At (evFin F v) u → ∀ Φ ∈ SB (κ → Fv F v),
        S (schr (GlobalTheory.LatVac.psiAt ψ v) (GlobalTheory.LatVac.locCo dd v u) Φ) =
          schr (GlobalTheory.LatVac.psiAt ψ v) (GlobalTheory.LatVac.locCo dd v (act p u)) (S Φ) := by
  intro F _ _ W _ _ Bf κ _ dd ψ hψ G _ act om hsp v p hat hex
  choose! S hS using hex
  refine ⟨S, hS, ?_⟩
  intro u hu Φ hΦ
  have hc : Continuous ψ := hψ.1
  have hw := GlobalTheory.SchrSB.schr_mem_SB ψ hc v (GlobalTheory.LatVac.locCo dd v u) Φ hΦ
  have restS : ∀ r, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (evFin F v) Φ r → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (evFin F v) (S Φ) r :=
    fun r hr => ⟨hr.1, by rw [← (hS Φ hΦ).2 r hr]; exact hsp.pres p _ hr.2⟩
  refine GlobalTheory.TensUniq.eq_of_tens_eq v Φ _ _ hΦ fun r hr => ?_
  have hb1 := GlobalTheory.VacBridge.rho_acts_locCo dd ψ v u hu Φ r hr
  have hRw : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (evFin F v)
      (schr (GlobalTheory.LatVac.psiAt ψ v) (GlobalTheory.LatVac.locCo dd v u) Φ) r :=
    ⟨hr.1, by rw [← hb1]; exact GlobalTheory.SchrKeepsSchA.schr_mem_schA F ψ hψ κ _ _ hr.2⟩
  rw [← (hS _ hw).2 r hRw, ← hb1, hsp.impl _ _ _ hr.2, (hS Φ hΦ).2 r hr,
    GlobalTheory.VacBridge.rho_acts_locCo dd ψ v _ (hat u hu) (S Φ) r (restS r hr)]

end GlobalTheory.LocSplitOp
end

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitting_preserves_local_schwartz : ∀ {F : Type} [Field F] [NumberField F] {W : Type} [AddCommGroup W] [Module (AF F) W] {Bf : W → W → AF F} {κ : Type} [Fintype κ]
    (dd : Darboux Bf κ) (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ {G : Type} [Group G] (act : G → W → W) (om : G →* Module.End ℂ ((κ → AF F) → ℂ)),
    IsSplitting (adeleClass F) ψ dd act om →
    ∀ (v : Pl F) (p : G), (∀ u, At (evFin F v) u → At (evFin F v) (act p u)) →
    (∀ Φ ∈ SB (κ → Fv F v), ∃ Φ₁ ∈ SB (κ → Fv F v), Acts (evFin F v) (om p) Φ Φ₁) →
    ∃ S : ((κ → Fv F v) → ℂ) → (κ → Fv F v) → ℂ,
      (∀ Φ ∈ SB (κ → Fv F v), S Φ ∈ SB (κ → Fv F v) ∧ Acts (evFin F v) (om p) Φ (S Φ)) ∧
      ∀ u, At (evFin F v) u → ∀ Φ ∈ SB (κ → Fv F v),
        S (schr (GlobalTheory.LatVac.psiAt ψ v) (GlobalTheory.LatVac.locCo dd v u) Φ) =
          schr (GlobalTheory.LatVac.psiAt ψ v) (GlobalTheory.LatVac.locCo dd v (act p u)) (S Φ) := by
  atlas_forward_decl GlobalTheory.LocSplitOp.exists_locOp
end

section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.slice_transform_schwartz_bijective : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {κ : Type} [Fintype κ] {n d : ℕ}
    (ι : ((κ → k) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ)),
    Set.BijOn ι (SB (κ → k) : Set ((κ → k) → ℂ)) (SB (Matrix (Fin n) (Fin d) k) : Set _) →
    Set.BijOn (GlobalTheory.SwapSlice.sliceT ι) (SB (κ ⊕ κ → k) : Set ((κ ⊕ κ → k) → ℂ))
      (SB (Matrix (Fin n) (Fin d) k × Matrix (Fin n) (Fin d) k) : Set _) := by
  first | exact @GlobalTheory.SwapSliceBij.sliceT_bijOn | exact GlobalTheory.SwapSliceBij.sliceT_bijOn | (intros; apply GlobalTheory.SwapSliceBij.sliceT_bijOn <;> assumption)
end

section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_idempotent_character_value : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ {a' d : ℕ} (J : Matrix (Fin a') (Fin a') (AE F E)) (v : Pl F) (t : E →ₐ[F] Fv F v) (f : AE F E),
    GlobalTheory.LatVac.liftV v (1 : Fv F v) • f = f → f * f = algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) →
    f * cA σ f = -algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) → piW t f = 1 → piW (t.comp σ) f = -1 →
    ∀ w : UG (cA σ) (dbl J),
      ((w : GL (Fin a' ⊕ Fin a') (AE F E)) : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (AE F E)) =
        Matrix.fromBlocks ((1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • (1 : Matrix (Fin a') (Fin a') (AE F E))) (f • 1) (f • 1)
          ((1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • 1) →
    At (evFin F v) (((w : GL (Fin a' ⊕ Fin a') (AE F E)) : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (AE F E)) - 1) ∧
    ∀ (u₁ u₂ : Matrix (Fin d) (Fin a') (AE F E)), At (evFin F v) u₁ → At (evFin F v) u₂ →
      (u₁.map (piW t) = 0 → u₂.map (piW t) = 0 →
        actB (cA σ) w (Matrix.fromCols u₁ u₂) = Matrix.fromCols (-u₂) (-u₁)) ∧
      (u₁.map (piW (t.comp σ)) = 0 → u₂.map (piW (t.comp σ)) = 0 →
        actB (cA σ) w (Matrix.fromCols u₁ u₂) = Matrix.fromCols u₂ u₁) := by
  first | exact @GlobalTheory.SwapAtPlace.swap_at_acts | exact GlobalTheory.SwapAtPlace.swap_at_acts | (intros; apply GlobalTheory.SwapAtPlace.swap_at_acts <;> assumption)
end

section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny

open GlobalTheory.FlipMatch

namespace GlobalTheory.SwapHeis

theorem heis_sliceT : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    G.V'.J.det ≠ 0 → G.W.J.det ≠ 0 →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v)
    (ι : (((Fin a' × Fin (a + a')) → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv F v) → ℂ)),
    G.M'.IsLinBar B.ψ t 1 1 ι →
    ∀ (d' : Darboux (symp (cA σ) (-1) (incM F G.W.J) (incM F G.V'.J)) (Fin a' × Fin (a + a'))),
    (∀ x : Matrix (Fin a') (Fin (a + a')) (AE F E), d'.e xᵀ = G.M'.co.e x) →
    ∀ (dd : Darboux (symp (cA σ) (-1) (incM F G.W.J) (dbl (incM F G.V'.J))) ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')))),
    IsDblCoord (cA σ) (-1) (incM F G.W.J) (incM F G.V'.J) d' dd →
    ∀ (u₁ u₂ : Matrix (Fin (a + a')) (Fin a') (AE F E)), At (evFin F v) u₁ → At (evFin F v) u₂ →
    GlobalTheory.FlipMatch.pairM (GlobalTheory.FlipMatch.coX t 1 1 u₁ᵀ) (GlobalTheory.FlipMatch.coY σ G.V' G.W t 1 1 u₁ᵀ) = 0 →
    GlobalTheory.FlipMatch.pairM (GlobalTheory.FlipMatch.coX t 1 1 u₂ᵀ) (GlobalTheory.FlipMatch.coY σ G.V' G.W t 1 1 u₂ᵀ) = 0 →
    ∀ Φ ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v),
    ∀ Z : Matrix (Fin a') (Fin (a + a')) (Fv F v) × Matrix (Fin a') (Fin (a + a')) (Fv F v),
      GlobalTheory.SwapSlice.sliceT ι (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v (Matrix.fromCols u₁ u₂)) Φ) Z =
        GlobalTheory.LatVac.psiAt B.ψ v (-GlobalTheory.FlipMatch.pairM Z.1 (GlobalTheory.FlipMatch.coX t 1 1 u₁ᵀ) +
                     GlobalTheory.FlipMatch.pairM Z.2 (GlobalTheory.FlipMatch.coX t 1 1 u₂ᵀ)) *
          GlobalTheory.SwapSlice.sliceT ι Φ (Z.1 + GlobalTheory.FlipMatch.coY σ G.V' G.W t 1 1 u₁ᵀ,
            Z.2 + GlobalTheory.FlipMatch.coY σ G.V' G.W t 1 1 u₂ᵀ) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT hdV hdW v t ι hι d' hd' dd hdd u₁ u₂ hu₁ hu₂ hp₁ hp₂ Φ hΦ Z
  set ψv := GlobalTheory.LatVac.psiAt B.ψ v with hψv
  have hc : Continuous ψv := GlobalTheory.SchrSB.continuous_psiAt B.ψ hT.base.std.1 v
  have hstar : ∀ y, starRingEnd ℂ (ψv y) = ψv (-y) := fun y => GlobalTheory.DblVacLine.star_psiAt B.ψ hT.base.std.1 v y
  have hatT : ∀ u : Matrix (Fin (a + a')) (Fin a') (AE F E), At (evFin F v) u → At (evFin F v) uᵀ :=
    fun u hu r hr => by rw [← Matrix.transpose_smul, hu r hr, Matrix.transpose_zero]
  have Heisenberg₂ : ∀ u : Matrix (Fin (a + a')) (Fin a') (AE F E), At (evFin F v) u →
      pairM (coX t 1 1 uᵀ) (coY σ G.V' G.W t 1 1 uᵀ) = 0 →
      ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ Y,
        ι (schr ψv (GlobalTheory.LatVac.locCo G.M'.co v uᵀ) φ) Y =
          ψv (-pairM Y (coX t 1 1 uᵀ)) * ι φ (Y + coY σ G.V' G.W t 1 1 uᵀ) := by
    intro u hu hp φ hφ Y
    exact (GlobalTheory.HeisFlip.heis_trans_char hT.base.cm G.V' G.W hT.geo.hV'.herm hT.geo.hW.skew hdV hdW G.M' B.ψ
      hT.base.std t 1 1 uᵀ (hatT u hu) hp φ hφ _ (GlobalTheory.SchrSB.schr_mem_SB B.ψ hT.base.std.1 v _ φ hφ)
      (GlobalTheory.VacBridge.rho_acts_locCo G.M'.co B.ψ v uᵀ (hatT u hu) φ)).2 ι hι Y
  have hloc : GlobalTheory.LatVac.locCo dd v (Matrix.fromCols u₁ u₂) =
      (Sum.elim (GlobalTheory.LatVac.locCo G.M'.co v u₁ᵀ).1 (GlobalTheory.LatVac.locCo G.M'.co v u₂ᵀ).1,
        Sum.elim (GlobalTheory.LatVac.locCo G.M'.co v u₁ᵀ).2 (-(GlobalTheory.LatVac.locCo G.M'.co v u₂ᵀ).2)) := by
    have e1 := hd' u₁ᵀ
    have e2 := hd' u₂ᵀ
    rw [Matrix.transpose_transpose] at e1 e2
    have h := hdd u₁ u₂
    ext k <;> cases k <;> simp [GlobalTheory.LatVac.locCo, h, e1, e2]
  have hconjSB : ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), (fun x => starRingEnd ℂ (φ x)) ∈ SB _ :=
    fun φ hφ => ⟨hφ.1.comp _, hφ.2.comp_left (map_zero _)⟩
  have hconj : ∀ (w : (Fin a' × Fin (a + a') → Fv F v) × (Fin a' × Fin (a + a') → Fv F v))
      (φ : (Fin a' × Fin (a + a') → Fv F v) → ℂ),
      (fun x => starRingEnd ℂ (schr ψv (w.1, -w.2) φ x)) = schr ψv w (fun x => starRingEnd ℂ (φ x)) := by
    intro w φ
    funext x
    simp only [GlobalTheory.WeilM.schr, map_mul, hstar]
    congr 2
    rw [dotProduct_neg, dotProduct_neg]
    ring
  have hbox : ∀ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ φ₂ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
      GlobalTheory.SwapSlice.sliceT ι (schr ψv (GlobalTheory.LatVac.locCo dd v (Matrix.fromCols u₁ u₂)) (boxFun φ₁ φ₂)) Z =
        ψv (-pairM Z.1 (coX t 1 1 u₁ᵀ) + pairM Z.2 (coX t 1 1 u₂ᵀ)) *
          GlobalTheory.SwapSlice.sliceT ι (boxFun φ₁ φ₂) (Z.1 + coY σ G.V' G.W t 1 1 u₁ᵀ, Z.2 + coY σ G.V' G.W t 1 1 u₂ᵀ) := by
    intro φ₁ h₁ φ₂ h₂
    rw [hloc, GlobalTheory.BoxSpan.schr_boxFun, GlobalTheory.SwapSlice.sliceT_boxFun, GlobalTheory.SwapSlice.sliceT_boxFun]
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, Prod.mk.eta]
    rw [GlobalTheory.SwapSlice.barL_apply, GlobalTheory.SwapSlice.barL_apply, hconj (GlobalTheory.LatVac.locCo G.M'.co v u₂ᵀ),
      Heisenberg₂ u₁ hu₁ hp₁ φ₁ h₁, Heisenberg₂ u₂ hu₂ hp₂ _ (hconjSB φ₂ h₂), map_mul, hstar, neg_neg, AddChar.map_add_eq_mul]
    ring
  let Lw : ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ]
      ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → Fv F v) → ℂ) :=
    { toFun := schr ψv (GlobalTheory.LatVac.locCo dd v (Matrix.fromCols u₁ u₂))
      map_add' := fun f g => by funext x; simp [schr, mul_add]
      map_smul' := fun c f => by funext x; simp [schr]; ring }
  let Z' : Matrix (Fin a') (Fin (a + a')) (Fv F v) × Matrix (Fin a') (Fin (a + a')) (Fv F v) :=
    (Z.1 + coY σ G.V' G.W t 1 1 u₁ᵀ, Z.2 + coY σ G.V' G.W t 1 1 u₂ᵀ)
  let c : ℂ := ψv (-pairM Z.1 (coX t 1 1 u₁ᵀ) + pairM Z.2 (coX t 1 1 u₂ᵀ))
  let Λ : ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] ℂ :=
    (LinearMap.proj Z).comp ((GlobalTheory.SwapSlice.sliceT ι).comp Lw) - c • (LinearMap.proj Z').comp (GlobalTheory.SwapSlice.sliceT ι)
  have hΛ : ∀ Ψ, Λ Ψ = GlobalTheory.SwapSlice.sliceT ι (schr ψv (GlobalTheory.LatVac.locCo dd v (Matrix.fromCols u₁ u₂)) Ψ) Z -
      c * GlobalTheory.SwapSlice.sliceT ι Ψ Z' := fun Ψ => rfl
  have h0 := GlobalTheory.BoxSpan.boxSpan_ker F v (Fin a' × Fin (a + a')) (Fin a' × Fin (a + a')) ψv hc
    (GlobalTheory.PsiNontriv.psiAt_ne_one B.ψ hT.base.std v) Λ
    (fun φ₁ h₁ φ₂ h₂ => by rw [hΛ, hbox φ₁ h₁ φ₂ h₂, sub_self]) Φ hΦ
  rw [hΛ, sub_eq_zero] at h0
  exact h0

end GlobalTheory.SwapHeis
end

section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny

namespace GlobalTheory.SplitCoord

theorem exists_at_coord : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ {n d : ℕ} (X : Spc F E n) (Y : Spc F E d), X.J.det ≠ 0 → Y.J.det ≠ 0 → ∀ (v : Pl F) (t : E →ₐ[F] Fv F v)
    (Z : Matrix (Fin n) (Fin d) (Fv F v)),
    (∃ x : Matrix (Fin n) (Fin d) (AE F E), At (evFin F v) x ∧ x.map (piW t) = 0 ∧
      GlobalTheory.FlipMatch.coY σ X Y t 1 1 x = Z) ∧
    (∃ x : Matrix (Fin n) (Fin d) (AE F E), At (evFin F v) x ∧ x.map (piW (t.comp σ)) = 0 ∧
      GlobalTheory.FlipMatch.coX t 1 1 x = Z) := by
  intro F E _ _ _ _ _ σ hcm n d X Y hdX hdY v t Z
  have hA : IsUnit (X.J.map t).det := by
    rw [show (X.J.map t).det = (t : E →+* Fv F v) X.J.det from (RingHom.map_det _ _).symm]
    exact isUnit_iff_ne_zero.2 fun h => hdX ((t : E →+* Fv F v).injective (by rw [map_zero]; exact h))
  have hB : IsUnit (Y.J.map t)ᵀ.det := by
    rw [Matrix.det_transpose, show (Y.J.map t).det = (t : E →+* Fv F v) Y.J.det from (RingHom.map_det _ _).symm]
    exact isUnit_iff_ne_zero.2 fun h => hdY ((t : E →+* Fv F v).injective (by rw [map_zero]; exact h))
  constructor
  · obtain ⟨x, hat, h0, h1⟩ := GlobalTheory.SplitComps.exists_mat_comps hcm v t (0 : Matrix (Fin n) (Fin d) (Fv F v))
      (-((X.J.map t)⁻¹ * Z * ((Y.J.map t)ᵀ)⁻¹))
    refine ⟨x, hat, h0, ?_⟩
    simp only [GlobalTheory.FlipMatch.coY, h1, Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc, Units.val_one,
      Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ hA, Matrix.nonsing_inv_mul _ hB, Matrix.mul_one]
  · obtain ⟨x, hat, h0, h1⟩ := GlobalTheory.SplitComps.exists_mat_comps hcm v t Z (0 : Matrix (Fin n) (Fin d) (Fv F v))
    refine ⟨x, hat, h1, ?_⟩
    simp only [GlobalTheory.FlipMatch.coX, h0, inv_one, Units.val_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]

end GlobalTheory.SplitCoord
end

section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny

namespace GlobalTheory.GramDet

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem det_ne_zero_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hn, A, hA⟩ := h
  subst hn
  set A' : Matrix (Fin (r + s)) (Fin (r + s)) ℂ := A.submatrix id finSumFinEquiv.symm with hA'
  have key : A'ᵀ * M * A'.map star =
      (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
    rw [← hA]
    ext i j
    simp [hA', Matrix.mul_apply, Matrix.submatrix_apply, Matrix.transpose_apply]
  intro h0
  have hd := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_mul, h0, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁] at hd
  simp [Matrix.det_neg] at hd
  exact pow_ne_zero s (neg_ne_zero.mpr one_ne_zero) hd.symm

theorem det_ne_zero_of_map {n : ℕ} {K : Type} [Field K] (φ : K →+* ℂ) {J : Matrix (Fin n) (Fin n) K}
    (h : (J.map φ).det ≠ 0) : J.det ≠ 0 := by
  intro h0
  apply h
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]

theorem gram_det_ne_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    G.V'.J.det ≠ 0 ∧ G.W.J.det ≠ 0 := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  refine ⟨det_ne_zero_of_map (B.emb w).1 (det_ne_zero_of_hasSig (hT.geo.hV'.sig w)), ?_⟩
  refine det_ne_zero_of_map (B.emb w).1 ?_
  have h := det_ne_zero_of_hasSig (hT.geo.hW.sig w)
  rw [Matrix.det_smul] at h
  intro h0
  exact h (by rw [h0, mul_zero])

end GlobalTheory.GramDet
end

section
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny
noncomputable section

namespace GlobalTheory.SwapSchur

open GlobalTheory.SwapSlice

def splitC {R : Type} {m n : ℕ} (Y : Matrix (Fin m) (Fin (n + n)) R) :
    Matrix (Fin m) (Fin n) R × Matrix (Fin m) (Fin n) R :=
  (fun i j => Y i (Fin.castAdd n j), fun i j => Y i (Fin.natAdd n j))

def joinC {R : Type} {m n : ℕ} (Z : Matrix (Fin m) (Fin n) R × Matrix (Fin m) (Fin n) R) :
    Matrix (Fin m) (Fin (n + n)) R :=
  fun i => Fin.append (Z.1 i) (Z.2 i)

theorem splitC_joinC {R : Type} {m n : ℕ} (Z : Matrix (Fin m) (Fin n) R × Matrix (Fin m) (Fin n) R) :
    splitC (joinC Z) = Z := by
  rcases Z with ⟨Z₁, Z₂⟩
  simp only [splitC, joinC, Fin.append_left, Fin.append_right]

theorem joinC_splitC {R : Type} {m n : ℕ} (Y : Matrix (Fin m) (Fin (n + n)) R) : joinC (splitC Y) = Y := by
  funext i
  exact Fin.append_castAdd_natAdd

theorem splitC_add {R : Type} [Add R] {m n : ℕ} (Y C : Matrix (Fin m) (Fin (n + n)) R) :
    splitC (Y + C) = splitC Y + splitC C := rfl

theorem swapNeg_swapNeg {Y : Type} [InvolutiveNeg Y] (Z : Y × Y) : swapNeg (swapNeg Z) = Z := by
  simp [swapNeg]

def swapH {k : Type} [TopologicalSpace k] [AddGroup k] [IsTopologicalAddGroup k] {m n : ℕ} :
    Matrix (Fin m) (Fin (n + n)) k ≃ₜ (Matrix (Fin m) (Fin n) k × Matrix (Fin m) (Fin n) k) where
  toFun Y := swapNeg (splitC Y)
  invFun Z := joinC (swapNeg Z)
  left_inv Y := by
    show joinC (swapNeg (swapNeg (splitC Y))) = Y
    rw [swapNeg_swapNeg, joinC_splitC]
  right_inv Z := by
    show swapNeg (splitC (joinC (swapNeg Z))) = Z
    rw [splitC_joinC, swapNeg_swapNeg]
  continuous_toFun := by
    have h1 : Continuous fun Y : Matrix (Fin m) (Fin (n + n)) k => (splitC Y).1 :=
      continuous_matrix fun i j => continuous_id.matrix_elem i (Fin.castAdd n j)
    have h2 : Continuous fun Y : Matrix (Fin m) (Fin (n + n)) k => (splitC Y).2 :=
      continuous_matrix fun i j => continuous_id.matrix_elem i (Fin.natAdd n j)
    exact h2.neg.prodMk h1.neg
  continuous_invFun := by
    refine continuous_matrix fun i j => ?_
    cases j using Fin.addCases with
    | left j =>
      simp only [joinC, swapNeg, Fin.append_left, Matrix.neg_apply]
      exact (continuous_snd.matrix_elem i j).neg
    | right j =>
      simp only [joinC, swapNeg, Fin.append_right, Matrix.neg_apply]
      exact (continuous_fst.matrix_elem i j).neg

theorem comp_mem_SB {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {g : Y → ℂ}
    (hg : g ∈ SB Y) : g ∘ e ∈ SB X :=
  ⟨hg.1.comp_continuous e.continuous, hg.2.comp_homeomorph e⟩

theorem bijOn_comp {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) :
    Set.BijOn (fun g : Y → ℂ => g ∘ e) (SB Y : Set (Y → ℂ)) (SB X : Set (X → ℂ)) := by
  refine ⟨fun g hg => comp_mem_SB e hg, fun g _ g' _ h => funext fun y => ?_, fun f hf => ?_⟩
  · have := congrFun h (e.symm y)
    simpa using this
  · refine ⟨f ∘ e.symm, comp_mem_SB e.symm hf, ?_⟩
    funext x
    simp

theorem pairM_neg_left {k A C : Type} [CommRing k] [Fintype A] [Fintype C] (X Y : Matrix A C k) :
    GlobalTheory.FlipMatch.pairM (-X) Y = -GlobalTheory.FlipMatch.pairM X Y := by
  simp [GlobalTheory.FlipMatch.pairM, Finset.sum_neg_distrib]

theorem pairM_zero_right {k A C : Type} [CommRing k] [Fintype A] [Fintype C] (X : Matrix A C k) :
    GlobalTheory.FlipMatch.pairM X 0 = 0 := by
  simp [GlobalTheory.FlipMatch.pairM]

theorem pairM_zero_left {k A C : Type} [CommRing k] [Fintype A] [Fintype C] (Y : Matrix A C k) :
    GlobalTheory.FlipMatch.pairM 0 Y = 0 := by
  simp [GlobalTheory.FlipMatch.pairM]

def formR {k : Type} [CommRing k] {m n : ℕ} (l : Matrix (Fin m) (Fin (n + n)) k →ₗ[k] k) : Matrix (Fin m) (Fin n) k :=
  fun i j => l (Matrix.single i (Fin.natAdd n j) 1)

def formL {k : Type} [CommRing k] {m n : ℕ} (l : Matrix (Fin m) (Fin (n + n)) k →ₗ[k] k) : Matrix (Fin m) (Fin n) k :=
  fun i j => -l (Matrix.single i (Fin.castAdd n j) 1)

theorem linForm_eq {k : Type} [CommRing k] {m n : ℕ} (l : Matrix (Fin m) (Fin (n + n)) k →ₗ[k] k)
    (Y : Matrix (Fin m) (Fin (n + n)) k) :
    l Y = GlobalTheory.FlipMatch.pairM (splitC Y).2 (formR l) -
      GlobalTheory.FlipMatch.pairM (splitC Y).1 (formL l) := by
  have e : ∀ i j, l (Matrix.single i j (Y i j)) = Y i j * l (Matrix.single i j 1) := fun i j => by
    rw [← smul_eq_mul, ← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]
  conv_lhs => rw [Matrix.matrix_eq_sum_single Y, map_sum]
  simp only [map_sum, e]
  simp only [GlobalTheory.FlipMatch.pairM, splitC, formR, formL, Fin.sum_univ_add, mul_neg, Finset.sum_neg_distrib,
    sub_neg_eq_add, Finset.sum_add_distrib]
  ring

end GlobalTheory.SwapSchur

open GlobalTheory.SwapSchur in

theorem GlobalTheory.SwapSchur.sliceT_swap_eq_smul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v)
    (ι : (((Fin a' × Fin (a + a')) → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv F v) → ℂ)),
    G.M'.IsLinBar B.ψ t 1 1 ι →
    ∀ (d' : Darboux (symp (cA σ) (-1) (incM F G.W.J) (incM F G.V'.J)) (Fin a' × Fin (a + a'))),
    (∀ x : Matrix (Fin a') (Fin (a + a')) (AE F E), d'.e xᵀ = G.M'.co.e x) →
    ∀ (dd : Darboux (symp (cA σ) (-1) (incM F G.W.J) (dbl (incM F G.V'.J))) ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')))),
    IsDblCoord (cA σ) (-1) (incM F G.W.J) (incM F G.V'.J) d' dd →
    ∀ (f : AE F E), GlobalTheory.LatVac.liftV v (1 : Fv F v) • f = f → f * f = algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) →
    f * cA σ f = -algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) → piW t f = 1 → piW (t.comp σ) f = -1 →
    ∀ w : UG (cA σ) (dbl (incM F G.V'.J)),
      ((w : GL (Fin a' ⊕ Fin a') (AE F E)) : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (AE F E)) =
        Matrix.fromBlocks ((1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • (1 : Matrix (Fin a') (Fin a') (AE F E))) (f • 1) (f • 1)
          ((1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • 1) →
    ∀ S : (((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v) → ℂ) →
        ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v) → ℂ,
    (∀ Φ ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v),
      S Φ ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v)) →
    (∀ Φ ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v),
      ∀ Φ' ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v), ∀ c : ℂ, S (c • Φ + Φ') = c • S Φ + S Φ') →
    (∀ u, At (evFin F v) u → ∀ Φ ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v),
      S (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v u) Φ) =
        schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v (actB (cA σ) w u)) (S Φ)) →
    ∃ c : ℂ, ∀ Φ ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v),
      GlobalTheory.SwapSlice.sliceT ι (S Φ) = c • (GlobalTheory.SwapSlice.sliceT ι Φ ∘ GlobalTheory.SwapSlice.swapNeg) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v t ι hι d' hd' dd hdd f hf1 hf2 hf3 hf4 hf5 w hw S hSB hSlin hS
  classical
  obtain ⟨hdV', hdW⟩ := GlobalTheory.GramDet.gram_det_ne_zero F E σ B a a' G X om om' hT
  have hcm : IsCMExt F E σ := hT.base.cm
  have hstd : IsStd B.ψ := hT.base.std
  have hψc : Continuous B.ψ := hstd.1
  have hcont : Continuous (GlobalTheory.LatVac.psiAt B.ψ v) := GlobalTheory.SchrSB.continuous_psiAt B.ψ hψc v
  have hne : GlobalTheory.LatVac.psiAt B.ψ v ≠ 1 := GlobalTheory.PsiNontriv.psiAt_ne_one B.ψ hstd v
  have hι' : G.M'.IsLin B.ψ (piW (t.comp σ)) (piW t)
      (fun u => -((1 : GL (Fin a') (Fv F v)).1ᵀ * G.V'.J.map t * u.map (piW (t.comp σ)) * (G.W.J.map t)ᵀ *
        (1 : GL (Fin (a + a')) (Fv F v)).1)) ι := hι
  have hbij := GlobalTheory.SwapSliceBij.sliceT_bijOn ι hι'.bij
  obtain ⟨-, hw2⟩ := GlobalTheory.SwapAtPlace.swap_at_acts σ hcm (d := a + a') (incM F G.V'.J) v t f hf1 hf2 hf3 hf4 hf5 w hw
  have hheis := GlobalTheory.SwapHeis.heis_sliceT F E σ B a a' G X om om' hT hdV' hdW v t ι hι d' hd' dd hdd
  choose xY hxYat hxY0 hxY using fun Z => (GlobalTheory.SplitCoord.exists_at_coord σ hcm G.V' G.W hdV' hdW v t Z).1
  choose xX hxXat hxX0 hxX using fun Z => (GlobalTheory.SplitCoord.exists_at_coord σ hcm G.V' G.W hdV' hdW v t Z).2

  have atT : ∀ x : Matrix (Fin a') (Fin (a + a')) (AE F E), At (evFin F v) x → At (evFin F v) xᵀ :=
    fun x hx r hr => by rw [← Matrix.transpose_smul, hx r hr, Matrix.transpose_zero]
  have atNeg : ∀ x : Matrix (Fin (a + a')) (Fin a') (AE F E), At (evFin F v) x → At (evFin F v) (-x) :=
    fun x hx r hr => by rw [smul_neg, hx r hr, neg_zero]
  have atCols : ∀ u₁ u₂ : Matrix (Fin (a + a')) (Fin a') (AE F E), At (evFin F v) u₁ → At (evFin F v) u₂ →
      At (evFin F v) (Matrix.fromCols u₁ u₂) := by
    intro u₁ u₂ h1 h2 r hr
    ext i j
    cases j with
    | inl j => simpa using congrFun (congrFun (h1 r hr) i) j
    | inr j => simpa using congrFun (congrFun (h2 r hr) i) j

  have coX0 : ∀ x : Matrix (Fin a') (Fin (a + a')) (AE F E), x.map (piW t) = 0 → GlobalTheory.FlipMatch.coX t 1 1 x = 0 := by
    intro x hx; simp [GlobalTheory.FlipMatch.coX, hx]
  have coY0 : ∀ x : Matrix (Fin a') (Fin (a + a')) (AE F E), x.map (piW (t.comp σ)) = 0 →
      GlobalTheory.FlipMatch.coY σ G.V' G.W t 1 1 x = 0 := by
    intro x hx; simp [GlobalTheory.FlipMatch.coY, hx]
  have mapNeg : ∀ (π : AE F E →+* Fv F v) (x : Matrix (Fin a') (Fin (a + a')) (AE F E)), (-x).map π = -x.map π := by
    intro π x; ext i j; simp
  have coXneg : ∀ x : Matrix (Fin a') (Fin (a + a')) (AE F E),
      GlobalTheory.FlipMatch.coX t 1 1 (-x) = -GlobalTheory.FlipMatch.coX t 1 1 x := by
    intro x; simp only [GlobalTheory.FlipMatch.coX, mapNeg]; simp [Matrix.mul_neg, Matrix.neg_mul]
  have coYneg : ∀ x : Matrix (Fin a') (Fin (a + a')) (AE F E),
      GlobalTheory.FlipMatch.coY σ G.V' G.W t 1 1 (-x) = -GlobalTheory.FlipMatch.coY σ G.V' G.W t 1 1 x := by
    intro x; simp only [GlobalTheory.FlipMatch.coY, mapNeg]; simp [Matrix.mul_neg, Matrix.neg_mul]

  let hH : Matrix (Fin a') (Fin ((a + a') + (a + a'))) (Fv F v) ≃ₜ
      (Matrix (Fin a') (Fin (a + a')) (Fv F v) × Matrix (Fin a') (Fin (a + a')) (Fv F v)) := swapH
  let ι₁ := (LinearMap.funLeft ℂ ℂ hH) ∘ₗ GlobalTheory.SwapSlice.sliceT ι
  have hι₁ : ∀ Φ Y, ι₁ Φ Y = GlobalTheory.SwapSlice.sliceT ι Φ (GlobalTheory.SwapSlice.swapNeg (splitC Y)) := fun _ _ => rfl
  let ι₂ : ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → Fv F v) → ℂ) →
      Matrix (Fin a') (Fin ((a + a') + (a + a'))) (Fv F v) → ℂ :=
    fun Φ Y => GlobalTheory.SwapSlice.sliceT ι (S Φ) (splitC Y)
  have hbij₁ : Set.BijOn ι₁ (SB (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → Fv F v) : Set _)
      (SB (Matrix (Fin a') (Fin ((a + a') + (a + a'))) (Fv F v)) : Set _) :=
    (bijOn_comp hH).comp hbij
  have hlin₂ : ∀ x ∈ SB (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → Fv F v),
      ∀ y ∈ SB (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → Fv F v), ∀ c : ℂ, ι₂ (c • x + y) = c • ι₂ x + ι₂ y := by
    intro x hx y hy c
    funext Y
    simp only [ι₂, hSlin x hx y hy c, map_add, map_smul, Pi.add_apply, Pi.smul_apply]

  have tMap : ∀ (π : AE F E →+* Fv F v) (x : Matrix (Fin a') (Fin (a + a')) (AE F E)), x.map π = 0 → xᵀ.map π = 0 := by
    intro π x hx; rw [Matrix.transpose_map, hx, Matrix.transpose_zero]
  have tNeg : ∀ x : Matrix (Fin a') (Fin (a + a')) (AE F E), (-xᵀ)ᵀ = -x := by
    intro x; rw [Matrix.transpose_neg, Matrix.transpose_transpose]
  have tr1 : ∀ x₁ x₂ : Matrix (Fin a') (Fin (a + a')) (AE F E), At (evFin F v) x₁ → At (evFin F v) x₂ →
      x₁.map (piW t) = 0 → x₂.map (piW t) = 0 →
      ∀ x ∈ SB (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → Fv F v), ∀ Z,
      GlobalTheory.SwapSlice.sliceT ι (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v (Matrix.fromCols x₁ᵀ x₂ᵀ)) x) Z =
        GlobalTheory.SwapSlice.sliceT ι x (Z.1 + GlobalTheory.FlipMatch.coY σ G.V' G.W t 1 1 x₁, Z.2 + GlobalTheory.FlipMatch.coY σ G.V' G.W t 1 1 x₂) := by
    intro x₁ x₂ a1 a2 m1 m2 x hx Z
    have c1 : GlobalTheory.FlipMatch.coX t 1 1 x₁ᵀᵀ = 0 := by rw [Matrix.transpose_transpose]; exact coX0 _ m1
    have c2 : GlobalTheory.FlipMatch.coX t 1 1 x₂ᵀᵀ = 0 := by rw [Matrix.transpose_transpose]; exact coX0 _ m2
    rw [hheis x₁ᵀ x₂ᵀ (atT _ a1) (atT _ a2) (by rw [c1, pairM_zero_left]) (by rw [c2, pairM_zero_left]) x hx, c1, c2,
      Matrix.transpose_transpose, Matrix.transpose_transpose]
    simp only [pairM_zero_right, neg_zero, add_zero, AddChar.map_zero_eq_one, one_mul]
  have tr2 : ∀ x₁ x₂ : Matrix (Fin a') (Fin (a + a')) (AE F E), At (evFin F v) x₁ → At (evFin F v) x₂ →
      x₁.map (piW t) = 0 → x₂.map (piW t) = 0 →
      ∀ x ∈ SB (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → Fv F v), ∀ Z,
      GlobalTheory.SwapSlice.sliceT ι (S (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v (Matrix.fromCols x₁ᵀ x₂ᵀ)) x)) Z =
        GlobalTheory.SwapSlice.sliceT ι (S x) (Z.1 - GlobalTheory.FlipMatch.coY σ G.V' G.W t 1 1 x₂, Z.2 - GlobalTheory.FlipMatch.coY σ G.V' G.W t 1 1 x₁) := by
    intro x₁ x₂ a1 a2 m1 m2 x hx Z
    have c1 : GlobalTheory.FlipMatch.coX t 1 1 (-x₁ᵀ)ᵀ = 0 := by rw [tNeg, coXneg, coX0 _ m1, neg_zero]
    have c2 : GlobalTheory.FlipMatch.coX t 1 1 (-x₂ᵀ)ᵀ = 0 := by rw [tNeg, coXneg, coX0 _ m2, neg_zero]
    rw [hS _ (atCols _ _ (atT _ a1) (atT _ a2)) x hx, (hw2 _ _ (atT _ a1) (atT _ a2)).1 (tMap _ _ m1) (tMap _ _ m2),
      hheis (-x₂ᵀ) (-x₁ᵀ) (atNeg _ (atT _ a2)) (atNeg _ (atT _ a1)) (by rw [c2, pairM_zero_left])
        (by rw [c1, pairM_zero_left]) (S x) (hSB x hx), c1, c2, tNeg, tNeg, coYneg, coYneg]
    simp only [pairM_zero_right, neg_zero, add_zero, AddChar.map_zero_eq_one, one_mul, sub_eq_add_neg]
  have mu1 : ∀ x₁ x₂ : Matrix (Fin a') (Fin (a + a')) (AE F E), At (evFin F v) x₁ → At (evFin F v) x₂ →
      x₁.map (piW (t.comp σ)) = 0 → x₂.map (piW (t.comp σ)) = 0 →
      ∀ x ∈ SB (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → Fv F v), ∀ Z,
      GlobalTheory.SwapSlice.sliceT ι (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v (Matrix.fromCols x₁ᵀ x₂ᵀ)) x) Z =
        GlobalTheory.LatVac.psiAt B.ψ v (-GlobalTheory.FlipMatch.pairM Z.1 (GlobalTheory.FlipMatch.coX t 1 1 x₁) +
          GlobalTheory.FlipMatch.pairM Z.2 (GlobalTheory.FlipMatch.coX t 1 1 x₂)) * GlobalTheory.SwapSlice.sliceT ι x Z := by
    intro x₁ x₂ a1 a2 m1 m2 x hx Z
    have c1 : GlobalTheory.FlipMatch.coY σ G.V' G.W t 1 1 x₁ᵀᵀ = 0 := by rw [Matrix.transpose_transpose]; exact coY0 _ m1
    have c2 : GlobalTheory.FlipMatch.coY σ G.V' G.W t 1 1 x₂ᵀᵀ = 0 := by rw [Matrix.transpose_transpose]; exact coY0 _ m2
    rw [hheis x₁ᵀ x₂ᵀ (atT _ a1) (atT _ a2) (by rw [c1, pairM_zero_right]) (by rw [c2, pairM_zero_right]) x hx, c1, c2,
      Matrix.transpose_transpose, Matrix.transpose_transpose, add_zero, add_zero]
  have mu2 : ∀ x₁ x₂ : Matrix (Fin a') (Fin (a + a')) (AE F E), At (evFin F v) x₁ → At (evFin F v) x₂ →
      x₁.map (piW (t.comp σ)) = 0 → x₂.map (piW (t.comp σ)) = 0 →
      ∀ x ∈ SB (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → Fv F v), ∀ Z,
      GlobalTheory.SwapSlice.sliceT ι (S (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v (Matrix.fromCols x₁ᵀ x₂ᵀ)) x)) Z =
        GlobalTheory.LatVac.psiAt B.ψ v (-GlobalTheory.FlipMatch.pairM Z.1 (GlobalTheory.FlipMatch.coX t 1 1 x₂) +
          GlobalTheory.FlipMatch.pairM Z.2 (GlobalTheory.FlipMatch.coX t 1 1 x₁)) * GlobalTheory.SwapSlice.sliceT ι (S x) Z := by
    intro x₁ x₂ a1 a2 m1 m2 x hx Z
    rw [hS _ (atCols _ _ (atT _ a1) (atT _ a2)) x hx, (hw2 _ _ (atT _ a1) (atT _ a2)).2 (tMap _ _ m1) (tMap _ _ m2)]
    exact mu1 x₂ x₁ a2 a1 m2 m1 (S x) (hSB x hx) Z
  obtain ⟨c, hc⟩ := GlobalTheory.LinSchur.eq_smul_of_commute (SB _) (GlobalTheory.LatVac.psiAt B.ψ v) hcont hne ι₁ ι₂ hbij₁ hlin₂
    (fun C x => schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v
      (Matrix.fromCols (xY (-(splitC C).2))ᵀ (xY (-(splitC C).1))ᵀ)) x)
    (fun l x => schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v
      (Matrix.fromCols (xX (formR l))ᵀ (xX (formL l))ᵀ)) x)
    (fun C x hx => ⟨GlobalTheory.SchrSB.schr_mem_SB B.ψ hψc v _ x hx, funext fun Y => by
        beta_reduce
        rw [hι₁, tr1 _ _ (hxYat _) (hxYat _) (hxY0 _) (hxY0 _) x hx, hxY, hxY, hι₁]
        simp only [GlobalTheory.SwapSlice.swapNeg, splitC_add, Prod.fst_add, Prod.snd_add, neg_add],
      funext fun Y => by
        beta_reduce
        show GlobalTheory.SwapSlice.sliceT ι (S _) (splitC Y) = GlobalTheory.SwapSlice.sliceT ι (S x) (splitC (Y + C))
        rw [tr2 _ _ (hxYat _) (hxYat _) (hxY0 _) (hxY0 _) x hx, hxY, hxY]
        simp only [splitC_add, sub_neg_eq_add]
        rfl⟩)
    (fun l x hx => ⟨GlobalTheory.SchrSB.schr_mem_SB B.ψ hψc v _ x hx, funext fun Y => by
        beta_reduce
        rw [hι₁, mu1 _ _ (hxXat _) (hxXat _) (hxX0 _) (hxX0 _) x hx, hxX, hxX, hι₁, linForm_eq l Y]
        congr 2
        simp only [GlobalTheory.SwapSlice.swapNeg, pairM_neg_left]
        ring,
      funext fun Y => by
        beta_reduce
        show GlobalTheory.SwapSlice.sliceT ι (S _) (splitC Y) = _ * GlobalTheory.SwapSlice.sliceT ι (S x) (splitC Y)
        rw [mu2 _ _ (hxXat _) (hxXat _) (hxX0 _) (hxX0 _) x hx, hxX, hxX, linForm_eq l Y]
        congr 2
        ring⟩)
  refine ⟨c, fun Φ hΦ => funext fun Z => ?_⟩
  have e : GlobalTheory.SwapSlice.sliceT ι (S Φ) (splitC (joinC Z)) =
      c * GlobalTheory.SwapSlice.sliceT ι Φ (GlobalTheory.SwapSlice.swapNeg (splitC (joinC Z))) := congrFun (hc Φ hΦ) (joinC Z)
  rw [splitC_joinC] at e
  exact e
end
end

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linear_bar_model_local_triple : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v)
    (ι : (((Fin a' × Fin (a + a')) → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv F v) → ℂ)),
    G.M'.IsLinBar B.ψ t 1 1 ι →
    ∀ (d' : Darboux (symp (cA σ) (-1) (incM F G.W.J) (incM F G.V'.J)) (Fin a' × Fin (a + a'))),
    (∀ x : Matrix (Fin a') (Fin (a + a')) (AE F E), d'.e xᵀ = G.M'.co.e x) →
    ∀ (dd : Darboux (symp (cA σ) (-1) (incM F G.W.J) (dbl (incM F G.V'.J))) ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')))),
    IsDblCoord (cA σ) (-1) (incM F G.W.J) (incM F G.V'.J) d' dd →
    ∀ (f : AE F E), GlobalTheory.LatVac.liftV v (1 : Fv F v) • f = f → f * f = algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) →
    f * cA σ f = -algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) → piW t f = 1 → piW (t.comp σ) f = -1 →
    ∀ w : UG (cA σ) (dbl (incM F G.V'.J)),
      ((w : GL (Fin a' ⊕ Fin a') (AE F E)) : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (AE F E)) =
        Matrix.fromBlocks ((1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • (1 : Matrix (Fin a') (Fin a') (AE F E))) (f • 1) (f • 1)
          ((1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • 1) →
    ∀ S : (((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v) → ℂ) →
        ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v) → ℂ,
    (∀ Φ ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v),
      S Φ ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v)) →
    (∀ Φ ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v),
      ∀ Φ' ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v), ∀ c : ℂ, S (c • Φ + Φ') = c • S Φ + S Φ') →
    (∀ u, At (evFin F v) u → ∀ Φ ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v),
      S (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v u) Φ) =
        schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v (actB (cA σ) w u)) (S Φ)) →
    ∃ c : ℂ, ∀ Φ ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v),
      GlobalTheory.SwapSlice.sliceT ι (S Φ) = c • (GlobalTheory.SwapSlice.sliceT ι Φ ∘ GlobalTheory.SwapSlice.swapNeg) := by
  atlas_forward_decl GlobalTheory.SwapSchur.sliceT_swap_eq_smul
end

section
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.SwapActs

theorem swap_acts_box : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v → ∀ (t : E →ₐ[F] Fv F v)
    (ι : (((Fin a' × Fin (a + a')) → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv F v) → ℂ)),
    G.M'.IsLinBar B.ψ t 1 1 ι →
    ∀ (d' : Darboux (symp (cA σ) (-1) (incM F G.W.J) (incM F G.V'.J)) (Fin a' × Fin (a + a'))),
    (∀ x : Matrix (Fin a') (Fin (a + a')) (AE F E), d'.e xᵀ = G.M'.co.e x) →
    ∀ (dd : Darboux (symp (cA σ) (-1) (incM F G.W.J) (dbl (incM F G.V'.J))) ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')))),
    IsDblCoord (cA σ) (-1) (incM F G.W.J) (incM F G.V'.J) d' dd →
    ∀ (omd : UG (cA σ) (dbl (incM F G.V'.J)) →* Module.End ℂ (((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → AF F) → ℂ)),
    IsUSplitting (adeleClass F) B.ψ dd (actB (cA σ)) omd →
    ∀ (f : AE F E), GlobalTheory.LatVac.liftV v (1 : Fv F v) • f = f → f * f = algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) →
    f * cA σ f = -algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) → piW t f = 1 → piW (t.comp σ) f = -1 →
    ∀ w : UG (cA σ) (dbl (incM F G.V'.J)),
      ((w : GL (Fin a' ⊕ Fin a') (AE F E)) : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (AE F E)) =
        Matrix.fromBlocks ((1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • (1 : Matrix (Fin a') (Fin a') (AE F E))) (f • 1) (f • 1)
          ((1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • 1) →
    ∃ c : ℂ, ∀ φ₁ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v), ∀ φ₂ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v),
      ∀ ψ₁ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v), ∀ ψ₂ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v),
      ι ψ₁ = (fun Y => starRingEnd ℂ (ι (fun y => starRingEnd ℂ (φ₂ y)) (-Y))) →
      ι (fun y => starRingEnd ℂ (ψ₂ y)) = (fun Y => starRingEnd ℂ (ι φ₁ (-Y))) →
      Acts (evFin F v) (omd w) (boxFun φ₁ φ₂) (c • boxFun ψ₁ ψ₂) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v hv t ι hι d' hd' dd hdd omd hspl f hf1 hf2 hf3 hf4 hf5 w hw
  have hcm : IsCMExt F E σ := hT.base.cm
  obtain ⟨hAt, -⟩ := GlobalTheory.T.local_idempotent_character_value σ hcm (incM F G.V'.J) (d := a + a') v t f hf1 hf2 hf3 hf4 hf5 w hw
  have atAct : ∀ u : Matrix (Fin (a + a')) (Fin a' ⊕ Fin a') (AE F E), At (evFin F v) u →
      At (evFin F v) (actB (cA σ) w u) := by
    intro u hu r hr
    simp only [actB]
    rw [← Matrix.smul_mul, hu r hr, Matrix.zero_mul]
  have hex := GlobalTheory.T.doubledUnitaryElement_acts_localOperatorAtPlace F E σ B a a' G hT.base dd omd hspl v w hAt
  obtain ⟨S, hS, hSh⟩ := GlobalTheory.T.splitting_preserves_local_schwartz dd B.ψ hT.base.std (actB (cA σ)) omd hspl.toIsSplitting v w atAct hex
  have hSlin := GlobalTheory.LocWeilAct.linear_of_acts v (omd w) S hS
  obtain ⟨c, hc⟩ := GlobalTheory.T.linear_bar_model_local_triple F E σ B a a' G X om om' hT v t ι hι d' hd' dd hdd f hf1 hf2 hf3 hf4 hf5 w hw S
    (fun Φ hΦ => (hS Φ hΦ).1) hSlin hSh
  refine ⟨c, fun φ₁ h₁ φ₂ h₂ ψ₁ k₁ ψ₂ k₂ e₁ e₂ => ?_⟩
  have hbij := GlobalTheory.T.slice_transform_schwartz_bijective ι hι.bij
  have hΦ := GlobalTheory.BoxSpan.boxFun_mem_SB' h₁ h₂
  have hΨ : c • boxFun ψ₁ ψ₂ ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v) :=
    (SB _).smul_mem c (GlobalTheory.BoxSpan.boxFun_mem_SB' k₁ k₂)
  have key : S (boxFun φ₁ φ₂) = c • boxFun ψ₁ ψ₂ := by
    refine hbij.injOn (hS _ hΦ).1 hΨ ?_
    rw [hc _ hΦ, map_smul]
    congr 1
    funext Z
    rw [Function.comp_apply, GlobalTheory.SwapSlice.sliceT_boxFun, GlobalTheory.SwapSlice.sliceT_boxFun, GlobalTheory.SwapSlice.swapNeg_apply,
      GlobalTheory.SwapSlice.barL_apply, GlobalTheory.SwapSlice.barL_apply, e₁, e₂]
    simp only [Complex.conj_conj]
    ring
  have h := (hS _ hΦ).2
  rwa [key] at h

end GlobalTheory.SwapActs
end
end

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linear_model_local_good_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v → ∀ (t : E →ₐ[F] Fv F v)
    (ι : (((Fin a' × Fin (a + a')) → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv F v) → ℂ)),
    G.M'.IsLinBar B.ψ t 1 1 ι →
    ∀ (d' : Darboux (symp (cA σ) (-1) (incM F G.W.J) (incM F G.V'.J)) (Fin a' × Fin (a + a'))),
    (∀ x : Matrix (Fin a') (Fin (a + a')) (AE F E), d'.e xᵀ = G.M'.co.e x) →
    ∀ (dd : Darboux (symp (cA σ) (-1) (incM F G.W.J) (dbl (incM F G.V'.J))) ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')))),
    IsDblCoord (cA σ) (-1) (incM F G.W.J) (incM F G.V'.J) d' dd →
    ∀ (omd : UG (cA σ) (dbl (incM F G.V'.J)) →* Module.End ℂ (((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → AF F) → ℂ)),
    IsUSplitting (adeleClass F) B.ψ dd (actB (cA σ)) omd →
    ∀ (f : AE F E), GlobalTheory.LatVac.liftV v (1 : Fv F v) • f = f → f * f = algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) →
    f * cA σ f = -algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) → piW t f = 1 → piW (t.comp σ) f = -1 →
    ∀ w : UG (cA σ) (dbl (incM F G.V'.J)),
      ((w : GL (Fin a' ⊕ Fin a') (AE F E)) : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (AE F E)) =
        Matrix.fromBlocks ((1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • (1 : Matrix (Fin a') (Fin a') (AE F E))) (f • 1) (f • 1)
          ((1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • 1) →
    ∃ c : ℂ, ∀ φ₁ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v), ∀ φ₂ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v),
      ∀ ψ₁ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v), ∀ ψ₂ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v),
      ι ψ₁ = (fun Y => starRingEnd ℂ (ι (fun y => starRingEnd ℂ (φ₂ y)) (-Y))) →
      ι (fun y => starRingEnd ℂ (ψ₂ y)) = (fun Y => starRingEnd ℂ (ι φ₁ (-Y))) →
      Acts (evFin F v) (omd w) (boxFun φ₁ φ₂) (c • boxFun ψ₁ ψ₂) := by
  atlas_forward_decl GlobalTheory.SwapActs.swap_acts_box
end

section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.DblSwap

section Groups

variable {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) {β : Type} [Fintype β] [DecidableEq β]
  {J : Matrix β β E}

theorem unit_left (k : UG c J) : (Matrix.fromBlocks ((k : GL β E) : Matrix β β E) 0 0 1)ᵀ * dbl J *
    (Matrix.fromBlocks ((k : GL β E) : Matrix β β E) 0 0 1).map c = dbl J := by
  have hk : ((k : GL β E) : Matrix β β E)ᵀ * J * ((k : GL β E) : Matrix β β E).map c = J := k.2
  have h1 : (1 : Matrix β β E).map c = 1 := Matrix.map_one _ (map_zero c) (map_one c)
  rw [dbl, Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Matrix.transpose_zero, Matrix.transpose_one, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add,
    Matrix.map_zero _ (map_zero c), h1, Matrix.one_mul, Matrix.mul_one, hk]

def leftDiag (k : UG c J) : UG c (dbl J) :=
  ⟨⟨Matrix.fromBlocks ((k : GL β E) : Matrix β β E) 0 0 1, Matrix.fromBlocks (((k : GL β E)⁻¹ : GL β E) : Matrix β β E) 0 0 1,
    by rw [Matrix.fromBlocks_multiply]; simp [Matrix.fromBlocks_one],
    by rw [Matrix.fromBlocks_multiply]; simp [Matrix.fromBlocks_one]⟩, unit_left c k⟩

end Groups

section Local

variable {F : Type} [Field F] [NumberField F]

theorem box_mem_SB {k : Type} [CommRing k] [TopologicalSpace k] [T2Space k] {κ κ' : Type}
    {φ₁ : (κ → k) → ℂ} {φ₂ : (κ' → k) → ℂ} (h₁ : φ₁ ∈ SB (κ → k)) (h₂ : φ₂ ∈ SB (κ' → k)) :
    boxFun φ₁ φ₂ ∈ SB (κ ⊕ κ' → k) := by
  have cl : Continuous fun x : κ ⊕ κ' → k => x ∘ Sum.inl := continuous_pi fun i => continuous_apply _
  have cr : Continuous fun x : κ ⊕ κ' → k => x ∘ Sum.inr := continuous_pi fun i => continuous_apply _
  refine ⟨(h₁.1.comp_continuous cl).mul (h₂.1.comp_continuous cr), ?_⟩
  let e := (Homeomorph.sumArrowHomeomorphProdArrow (X := k) (ι := κ) (ι' := κ'))
  refine HasCompactSupport.intro ((h₁.2.prod h₂.2).image e.symm.continuous) fun x hx => ?_
  have hx' : e x ∉ tsupport φ₁ ×ˢ tsupport φ₂ := fun h => hx ⟨e x, h, e.symm_apply_apply x⟩
  rw [Homeomorph.sumArrowHomeomorphProdArrow_apply, Set.mem_prod, not_and_or] at hx'
  simp only [boxFun]
  rcases hx' with h | h
  · rw [image_eq_zero_of_notMem_tsupport h, zero_mul]
  · rw [image_eq_zero_of_notMem_tsupport h, mul_zero]

theorem conjSB {Y : Type} [TopologicalSpace Y] {φ : Y → ℂ} (h : φ ∈ SB Y) :
    (fun y => starRingEnd ℂ (φ y)) ∈ SB Y :=
  ⟨h.1.comp _, h.2.comp_left (map_zero _)⟩

theorem negSB {Y : Type} [TopologicalSpace Y] [AddGroup Y] [IsTopologicalAddGroup Y] {φ : Y → ℂ} (h : φ ∈ SB Y) :
    (fun y => φ (-y)) ∈ SB Y :=
  ⟨h.1.comp_continuous continuous_neg, h.2.comp_homeomorph (Homeomorph.neg Y)⟩

theorem tens_box (v : Pl F) {κ κ' : Type} (φ₁ : (κ → Fv F v) → ℂ) (φ₂ : (κ' → Fv F v) → ℂ)
    (r₁ : (κ → AF F) → ℂ) (r₂ : (κ' → AF F) → ℂ) :
    tens (evFin F v) (boxFun φ₁ φ₂) (boxFun r₁ r₂) = boxFun (tens (evFin F v) φ₁ r₁) (tens (evFin F v) φ₂ r₂) := by
  funext x
  simp only [tens, boxFun, Function.comp_def]
  ring

theorem rest_box (v : Pl F) {κ κ' : Type} [Fintype κ] [Fintype κ'] {φ₁ : (κ → Fv F v) → ℂ} {φ₂ : (κ' → Fv F v) → ℂ}
    {r₁ : (κ → AF F) → ℂ} {r₂ : (κ' → AF F) → ℂ} (h₁ : Rest (evFin F v) φ₁ r₁) (h₂ : Rest (evFin F v) φ₂ r₂) :
    Rest (evFin F v) (boxFun φ₁ φ₂) (boxFun r₁ r₂) := by
  refine ⟨fun x z hz => ?_, ?_⟩
  · have hz1 : At (evFin F v) (z ∘ Sum.inl) := fun u hu => by
      funext i; exact congrFun (hz u hu) (Sum.inl i)
    have hz2 : At (evFin F v) (z ∘ Sum.inr) := fun u hu => by
      funext i; exact congrFun (hz u hu) (Sum.inr i)
    show r₁ ((x + z) ∘ Sum.inl) * r₂ ((x + z) ∘ Sum.inr) = r₁ (x ∘ Sum.inl) * r₂ (x ∘ Sum.inr)
    rw [show (x + z) ∘ Sum.inl = x ∘ Sum.inl + z ∘ Sum.inl from rfl,
      show (x + z) ∘ Sum.inr = x ∘ Sum.inr + z ∘ Sum.inr from rfl, h₁.1 _ _ hz1, h₂.1 _ _ hz2]
  · rw [tens_box]
    exact GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ _ h₁.2 _ h₂.2

theorem eq_of_tens_ne (v : Pl F) {κ : Type} {ψ₁ ψ₂ : (κ → Fv F v) → ℂ} {r : (κ → AF F) → ℂ}
    (hr : ∀ x z, At (evFin F v) z → r (x + z) = r x) {x₀ : κ → AF F} (h0 : r x₀ ≠ 0)
    (h : tens (evFin F v) ψ₁ r = tens (evFin F v) ψ₂ r) : ψ₁ = ψ₂ := by
  funext y
  let z : κ → AF F := fun i => GlobalTheory.LatVac.liftV v (y i - evFin F v (x₀ i))
  have hz : At (evFin F v) z := by
    intro u hu; funext i; exact GlobalTheory.LatVac.at_liftV v _ u hu
  have hev : (fun i => evFin F v ((x₀ + z) i)) = y := by
    funext i
    simp only [Pi.add_apply, z, map_add, GlobalTheory.LatVac.evFin_liftV]
    abel
  have e := congrFun h (x₀ + z)
  simp only [tens, hev, hr x₀ z hz] at e
  exact mul_right_cancel₀ h0 e

theorem actsComp (v : Pl F) {κ : Type} [Fintype κ] {T₁ T₂ : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ}
    (hT₂ : ∀ f ∈ schA F κ, T₂ f ∈ schA F κ) {φ φ₁ φ₂ : (κ → Fv F v) → ℂ}
    (h₂ : Acts (evFin F v) T₂ φ φ₁) (h₁ : Acts (evFin F v) T₁ φ₁ φ₂) :
    Acts (evFin F v) (fun f => T₁ (T₂ f)) φ φ₂ := by
  intro r hr
  have e := h₂ r hr
  have hr₁ : Rest (evFin F v) φ₁ r := ⟨hr.1, e ▸ hT₂ _ hr.2⟩
  show T₁ (T₂ _) = _
  rw [e, h₁ r hr₁]

theorem tens_smul (v : Pl F) {κ : Type} (c : ℂ) (φ : (κ → Fv F v) → ℂ) (r : (κ → AF F) → ℂ) :
    tens (evFin F v) (c • φ) r = c • tens (evFin F v) φ r := by
  funext x; simp only [tens, Pi.smul_apply, smul_eq_mul]; ring

theorem actsSmul (v : Pl F) {κ : Type} [Fintype κ] (T : Module.End ℂ ((κ → AF F) → ℂ)) {φ φ₁ : (κ → Fv F v) → ℂ}
    (h : Acts (evFin F v) T φ φ₁) (c : ℂ) : Acts (evFin F v) T (c • φ) (c • φ₁) := by
  intro r hr
  by_cases hc : c = 0
  · subst hc
    rw [tens_smul, tens_smul, zero_smul, zero_smul, map_zero]
  · have hr' : Rest (evFin F v) φ r := by
      refine ⟨hr.1, ?_⟩
      have e : tens (evFin F v) φ r = c⁻¹ • tens (evFin F v) (c • φ) r := by
        rw [tens_smul, smul_smul, inv_mul_cancel₀ hc, one_smul]
      rw [e]; exact (schA F κ).smul_mem _ hr.2
    rw [tens_smul, tens_smul, map_smul, h r hr']

end Local

end GlobalTheory.DblSwap

namespace GlobalTheory.DblSwap
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip

theorem conj_apow {F : Type} [Field F] [NumberField F] {v : Pl F} (x : (Fv F v)ˣ) (z : ℂ) (hz : starRingEnd ℂ z = z) :
    starRingEnd ℂ (apow x z) = apow x z := by
  unfold apow
  have harg : ((nabs (Fv F v) x : ℝ) : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg (nabs_pos (Fv F v) x).le]; exact Real.pi_ne_zero.symm
  have e := Complex.cpow_conj _ z harg
  rw [hz, Complex.conj_ofReal] at e
  exact e.symm

theorem conj_omB {F : Type} [Field F] [NumberField F] {v : Pl F} {A' D : Type} [Fintype A'] [DecidableEq A'] [Fintype D]
    [DecidableEq D] (ν α : (Fv F v)ˣ →* ℂˣ) (g : GL A' (Fv F v)) (Ψ : Matrix A' D (Fv F v) → ℂ) (Y : Matrix A' D (Fv F v)) :
    starRingEnd ℂ (omB ν α g 1 Ψ Y) =
      (starRingEnd ℂ (ν (gdet g) : ℂ) / (ν (gdet g) : ℂ)) * omB ν α g 1 (fun Z => starRingEnd ℂ (Ψ Z)) Y := by
  have hν : (ν (gdet g) : ℂ) ≠ 0 := Units.ne_zero _
  have h1 : gdet (1 : GL D (Fv F v)) = 1 := map_one _
  have hz : starRingEnd ℂ ((Fintype.card D : ℂ) / 2) = (Fintype.card D : ℂ) / 2 := by
    rw [map_div₀, map_natCast, map_ofNat]
  simp only [omB, h1, map_one, Units.val_one, apow_one, mul_one, map_mul, conj_apow _ _ hz]
  field_simp

end GlobalTheory.DblSwap

namespace GlobalTheory.DblSwap
open Matrix

theorem diagR_acts : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v → ∀ (t : E →ₐ[F] Fv F v)
    (K : GL (Fin a') (Fv F v) →* UA σ G.V'.J), (∀ g, K g ∈ UAt σ G.V' (evFin F v) ∧
      (mat (K g)).map (piW t) = g.val ∧
      (mat (K g)).map (piW (t.comp σ)) = (G.V'.J.map t)⁻¹ * ((g⁻¹ : GL _ _).val)ᵀ * G.V'.J.map t) →
    ∀ (S : GL (Fin a') (Fv F v) → (((Fin a' × Fin (a + a')) → Fv F v) → ℂ) → ((Fin a' × Fin (a + a')) → Fv F v) → ℂ),
    (∀ g, ∀ φ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v), S g φ ∈ SB _ ∧ Acts (evFin F v) (om' (K g, 1)) φ (S g φ)) →
    ∀ (ν α : (Fv F v)ˣ →* ℂˣ) (ι : (((Fin a' × Fin (a + a')) → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv F v) → ℂ)),
    G.M'.IsLinBar B.ψ t 1 1 ι → (∀ g, ∀ φ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v), ι (S g φ) = GlobalTheory.SplitFlip.omB ν α g 1 (ι φ)) →
    ∀ (d' : Darboux (symp (cA σ) (-1) (incM F G.W.J) (incM F G.V'.J)) (Fin a' × Fin (a + a'))),
    (∀ x : Matrix (Fin a') (Fin (a + a')) (AE F E), d'.e xᵀ = G.M'.co.e x) →
    ∀ (dd : Darboux (symp (cA σ) (-1) (incM F G.W.J) (dbl (incM F G.V'.J))) ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')))),
    IsDblCoord (cA σ) (-1) (incM F G.W.J) (incM F G.V'.J) d' dd →
    ∀ (omd : UG (cA σ) (dbl (incM F G.V'.J)) →* Module.End ℂ (((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → AF F) → ℂ)),
    IsUSplitting (adeleClass F) B.ψ dd (actB (cA σ)) omd →
    (∀ (g : UA σ G.V'.J) (gd : UG (cA σ) (dbl (incM F G.V'.J))),
      ((gd : GL (Fin a' ⊕ Fin a') (AE F E)) : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (AE F E)) =
        Matrix.fromBlocks (mat g) 0 0 1 →
      ∀ φ₁ ∈ schA F (Fin a' × Fin (a + a')), ∀ φ₂ ∈ schA F (Fin a' × Fin (a + a')), omd gd (boxFun φ₁ φ₂) = boxFun (om' (g, 1) φ₁) φ₂) →
    ∀ (g : GL (Fin a') (Fv F v)) (gd' : UG (cA σ) (dbl (incM F G.V'.J))),
      ((gd' : GL (Fin a' ⊕ Fin a') (AE F E)) : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (AE F E)) =
        Matrix.fromBlocks 1 0 0 (mat (K g)) →
    ∀ φ₁ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v), ∀ φ₂ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v),
      Acts (evFin F v) (omd gd') (boxFun φ₁ φ₂) (boxFun φ₁ (fun x =>
        ((ν (GlobalTheory.SplitFlip.gdet g) : ℂ) / starRingEnd ℂ (ν (GlobalTheory.SplitFlip.gdet g) : ℂ)) *
          starRingEnd ℂ (S g (fun y => starRingEnd ℂ (φ₂ y)) x))) := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hT v hv t K hK S hS ν α ι hι hint d' hd' dd hdd omd hspl hres g gd' hgd'
    φ₁ h₁ φ₂ h₂
  obtain ⟨f, hf1, hf2, hf3, hf4, hf5⟩ := GlobalTheory.T.local_idempotent_conjugation_sign σ hT.base.cm v t
  obtain ⟨w, hwm, -, hww, hconj⟩ := GlobalTheory.T.local_weyl_element_doubled σ G.V'.J v f hf1 hf2 hf3
  obtain ⟨c, hc⟩ := GlobalTheory.T.linear_model_local_good_place F E σ B a a' G X om om' hT v hv t ι hι d' hd' dd hdd omd hspl f hf1 hf2 hf3 hf4 hf5 w hwm
  set k := K g with hk
  let gd := leftDiag (cA σ) k
  have hgd : ((gd : GL (Fin a' ⊕ Fin a') (AE F E)) : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (AE F E)) =
      Matrix.fromBlocks (mat k) 0 0 1 := rfl
  have hAt : At (evFin F v) (((gd : GL (Fin a' ⊕ Fin a') (AE F E)) : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (AE F E)) - 1) := by
    intro u hu
    have hk1 : u • (mat k - 1) = 0 := (hK g).1 u hu
    have e : Matrix.fromBlocks (mat k) 0 0 (1 : Matrix (Fin a') (Fin a') (AE F E)) - 1 =
        Matrix.fromBlocks (mat k - 1) 0 0 0 := by
      rw [← Matrix.fromBlocks_one, sub_eq_add_neg, Matrix.fromBlocks_neg, Matrix.fromBlocks_add]; simp [sub_eq_add_neg]
    rw [hgd, e, Matrix.fromBlocks_smul]
    simp [hk1]
  have hpres : ∀ p, ∀ Φ ∈ schA F ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a'))), omd p Φ ∈ schA F _ :=
    fun p Φ hΦ => hspl.pres p Φ hΦ

  have hL : ∀ ψ₁ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v), ∀ ψ₂ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v),
      Acts (evFin F v) (omd gd) (boxFun ψ₁ ψ₂) (boxFun (S g ψ₁) ψ₂) := by
    intro ψ₁ hψ₁ ψ₂ hψ₂
    obtain ⟨φ', -, hA⟩ := GlobalTheory.T.doubledUnitaryElement_acts_localOperatorAtPlace F E σ B a a' G hT.base dd omd hspl v gd hAt _ (box_mem_SB hψ₁ hψ₂)
    obtain ⟨r₁, hr₁, x₁, hx₁⟩ := GlobalTheory.RestComplement.exists_rest_ne_zero v ψ₁ hψ₁
    obtain ⟨r₂, hr₂, x₂, hx₂⟩ := GlobalTheory.RestComplement.exists_rest_ne_zero v ψ₂ hψ₂
    have hR := rest_box v hr₁ hr₂
    have e := hA _ hR
    rw [tens_box, hres k gd hgd _ hr₁.2 _ hr₂.2, (hS g ψ₁ hψ₁).2 r₁ hr₁, ← tens_box] at e
    have h0 : boxFun r₁ r₂ (Sum.elim x₁ x₂) ≠ 0 := by
      simp only [boxFun, Sum.elim_comp_inl, Sum.elim_comp_inr]; exact mul_ne_zero hx₁ hx₂
    have e2 : φ' = boxFun (S g ψ₁) ψ₂ := eq_of_tens_ne v hR.1 h0 e.symm
    rw [e2] at hA; exact hA

  have pair : ∀ φa ∈ SB ((Fin a' × Fin (a + a')) → Fv F v), ∀ φb ∈ SB ((Fin a' × Fin (a + a')) → Fv F v),
      ∃ ψa ∈ SB ((Fin a' × Fin (a + a')) → Fv F v), ∃ ψb ∈ SB ((Fin a' × Fin (a + a')) → Fv F v),
        ι ψa = (fun Y => starRingEnd ℂ (ι (fun y => starRingEnd ℂ (φb y)) (-Y))) ∧
        ι (fun y => starRingEnd ℂ (ψb y)) = (fun Y => starRingEnd ℂ (ι φa (-Y))) := by
    intro φa ha φb hb
    have m1 : ι (fun y => starRingEnd ℂ (φb y)) ∈ SB (Matrix (Fin a') (Fin (a + a')) (Fv F v)) := hι.bij.mapsTo (conjSB hb)
    have m2 : ι φa ∈ SB (Matrix (Fin a') (Fin (a + a')) (Fv F v)) := hι.bij.mapsTo ha
    obtain ⟨ψa, hψa, ea⟩ := hι.bij.surjOn (conjSB (negSB m1))
    obtain ⟨χ, hχ, eb⟩ := hι.bij.surjOn (conjSB (negSB m2))
    refine ⟨ψa, hψa, fun y => starRingEnd ℂ (χ y), conjSB hχ, ea, ?_⟩
    have e : (fun y => starRingEnd ℂ (starRingEnd ℂ (χ y))) = χ := funext fun y => Complex.conj_conj _
    rw [e, eb]
  have inv : ∀ φa φb ψa ψb : ((Fin a' × Fin (a + a')) → Fv F v) → ℂ,
      ι ψa = (fun Y => starRingEnd ℂ (ι (fun y => starRingEnd ℂ (φb y)) (-Y))) →
      ι (fun y => starRingEnd ℂ (ψb y)) = (fun Y => starRingEnd ℂ (ι φa (-Y))) →
      ι φa = (fun Y => starRingEnd ℂ (ι (fun y => starRingEnd ℂ (ψb y)) (-Y))) ∧
      ι (fun y => starRingEnd ℂ (φb y)) = (fun Y => starRingEnd ℂ (ι ψa (-Y))) := by
    intro φa φb ψa ψb e1 e2
    refine ⟨?_, ?_⟩
    · rw [e2]; funext Y; simp only [neg_neg, Complex.conj_conj]
    · rw [e1]; funext Y; simp only [neg_neg, Complex.conj_conj]

  have hww' : ∀ Φ, omd w (omd w Φ) = Φ := fun Φ => by
    rw [← Module.End.mul_apply, ← map_mul, hww, map_one, Module.End.one_apply]
  have hc2 : c * c = 1 := by
    let φ0 : ((Fin a' × Fin (a + a')) → Fv F v) → ℂ := Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1
    have h0 : φ0 ∈ SB _ := GlobalTheory.StdVacuum.indicator_mem_SB v
    obtain ⟨ψa, ha, ψb, hb, e1, e2⟩ := pair φ0 h0 φ0 h0
    obtain ⟨e3, e4⟩ := inv _ _ _ _ e1 e2
    have A1 := hc φ0 h0 φ0 h0 ψa ha ψb hb e1 e2
    have A2 := actsSmul v (omd w) (hc ψa ha ψb hb φ0 h0 φ0 h0 e3 e4) c
    have A3 := actsComp v (fun Φ hΦ => hpres w Φ hΦ) A1 A2
    simp only [hww'] at A3
    have e5 := GlobalTheory.TensUniq.eq_of_tens_eq v (boxFun φ0 φ0) _ _ (box_mem_SB h0 h0) fun r hr => A3 r hr
    have e6 := congrFun e5 (fun _ => 0)
    have hv0 : φ0 (fun _ => 0) = 1 := by
      show Set.indicator _ _ _ = _
      rw [Set.indicator_of_mem (show (fun _ => (0 : Fv F v)) ∈
        {x : (Fin a' × Fin (a + a')) → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from fun i => zero_mem _)]
      rfl
    simp only [boxFun, Pi.smul_apply, smul_eq_mul] at e6
    rw [show ((fun _ => (0 : Fv F v)) : (Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v) ∘ Sum.inl = fun _ => 0
      from rfl, show ((fun _ => (0 : Fv F v)) : (Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v) ∘ Sum.inr =
      fun _ => 0 from rfl, hv0] at e6
    linear_combination -e6

  set cν : ℂ := (ν (GlobalTheory.SplitFlip.gdet g) : ℂ) / starRingEnd ℂ (ν (GlobalTheory.SplitFlip.gdet g) : ℂ) with hcν
  set T₂ : ((Fin a' × Fin (a + a')) → Fv F v) → ℂ :=
    fun x => cν * starRingEnd ℂ (S g (fun y => starRingEnd ℂ (φ₂ y)) x) with hT₂
  have hT₂sb : T₂ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v) :=
    (SB _).smul_mem cν (conjSB (hS g _ (conjSB h₂)).1)
  obtain ⟨ψ₁, hψ₁, ψ₂, hψ₂, e1, e2⟩ := pair φ₁ h₁ φ₂ h₂
  obtain ⟨e3, -⟩ := inv _ _ _ _ e1 e2
  have hSψ := (hS g ψ₁ hψ₁).1
  have key : ι (fun y => starRingEnd ℂ (T₂ y)) = (fun Y => starRingEnd ℂ (ι (S g ψ₁) (-Y))) := by
    have ec : (fun y => starRingEnd ℂ (T₂ y)) = starRingEnd ℂ cν • S g (fun y => starRingEnd ℂ (φ₂ y)) := by
      funext y; simp only [hT₂, map_mul, Complex.conj_conj, Pi.smul_apply, smul_eq_mul]
    rw [ec, map_smul, hint g _ (conjSB h₂), hint g ψ₁ hψ₁, e1]
    funext Y
    rw [conj_omB]
    simp only [Pi.smul_apply, smul_eq_mul, GlobalTheory.SplitFlip.omB, Complex.conj_conj, Matrix.mul_neg, Matrix.neg_mul, neg_neg]
    have hν : (ν (GlobalTheory.SplitFlip.gdet g) : ℂ) ≠ 0 := Units.ne_zero _
    have hν' : starRingEnd ℂ (ν (GlobalTheory.SplitFlip.gdet g) : ℂ) ≠ 0 := (map_ne_zero _).mpr hν
    rw [hcν, map_div₀, Complex.conj_conj]
  have A1 := hc φ₁ h₁ φ₂ h₂ ψ₁ hψ₁ ψ₂ hψ₂ e1 e2
  have A2 := actsSmul v (omd gd) (hL ψ₁ hψ₁ ψ₂ hψ₂) c
  have A3 := actsSmul v (omd w) (hc (S g ψ₁) hSψ ψ₂ hψ₂ φ₁ h₁ T₂ hT₂sb e3 key) c
  have A12 := actsComp v (fun Φ hΦ => hpres w Φ hΦ) A1 A2
  have A123 := actsComp v (fun Φ hΦ => hpres gd _ (hpres w Φ hΦ)) A12 A3
  rw [smul_smul, hc2, one_smul] at A123
  have eg : omd gd' = omd w * omd gd * omd w := by rw [← map_mul, ← map_mul, hconj k (hK g).1 gd gd' hgd hgd']
  rw [eg]
  exact A123

end GlobalTheory.DblSwap
end
end
