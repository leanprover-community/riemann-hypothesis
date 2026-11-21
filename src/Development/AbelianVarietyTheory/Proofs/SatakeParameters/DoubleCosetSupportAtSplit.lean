import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoOneOfSummable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceHeckeOperatorScalarOnSpherical
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalHeckeScalarOnTypeSpacesAllPlaces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceLocalComponentExistsUniqueClass
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FixedVectorsNeBotOfMemSumIntertwiningRanges

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BiInvScalar

open GlobalTheory.SphLabelOps GlobalTheory.HeckeScalarSph

theorem biInv_scalar : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (GQ L n) W) (S : Submodule ℂ (GAf L n → W)), NG.IsIrrRep ρ S → ∀ (s : SplitPlace L) (Ds : Set (GAf L n)), (∀ x ∈ Ds, TrivOutside {s.v} x) → (∀ x ∈ Ds, ∀ κ ∈ Umax L n, TrivOutside {s.v} κ → x * κ ∈ Ds ∧ κ * x ∈ Ds) → ∀ R : Finset (GAf L n), (∀ γ ∈ R, γ ∈ Ds) → (∀ x ∈ Ds, ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ Umax L n) → ∃ c : ℂ, ∀ f ∈ S, (∀ κ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, NG.rt L n κ f = f) → ∑ γ ∈ R, NG.rt L n γ f = c • f := by
  intro L _ _ _ n W _ _ ρ S hS s Ds hDt hDs R hRD hRu
  classical
  obtain ⟨hdec, hcomm, -⟩ := GlobalTheory.T.unitaryFiniteAdeles_splitPlace_decomposition L n s
  choose Rb hRb using exists_repsU (L := L) (n := n) s.v
  let K := locK (L := L) n s.v
  let dc : GAf L n → Set (GAf L n) := fun a => {x | ∃ k₁ ∈ K, ∃ k₂ ∈ K, x = k₁ * a * k₂}

  have hdcD : ∀ a ∈ Ds, ∀ x ∈ dc a, x ∈ Ds := by
    rintro a ha _ ⟨k₁, h₁, k₂, h₂, rfl⟩
    exact (hDs _ (hDs a ha k₁ h₁.1 h₁.2).2 k₂ h₂.1 h₂.2).1
  have hdc_eq : ∀ a b, b ∈ dc a → dc b = dc a := by
    rintro a _ ⟨k₁, h₁, k₂, h₂, rfl⟩
    ext x
    constructor
    · rintro ⟨l₁, i₁, l₂, i₂, rfl⟩
      exact ⟨l₁ * k₁, K.mul_mem i₁ h₁, k₂ * l₂, K.mul_mem h₂ i₂, by group⟩
    · rintro ⟨l₁, i₁, l₂, i₂, rfl⟩
      exact ⟨l₁ * k₁⁻¹, K.mul_mem i₁ (K.inv_mem h₁), k₂⁻¹ * l₂, K.mul_mem (K.inv_mem h₂) i₂, by group⟩
  have hself : ∀ a, a ∈ dc a := fun a => ⟨1, K.one_mem, 1, K.one_mem, by group⟩

  let fib : GAf L n → Finset (GAf L n) := fun a => R.filter (fun γ => dc γ = dc a)
  have hfib : ∀ α ∈ R, (∀ γ ∈ fib α, ∃ k₁ ∈ K, ∃ k₂ ∈ K, γ = k₁ * α * k₂) ∧
      ∀ x, (∃ k₁ ∈ K, ∃ k₂ ∈ K, x = k₁ * α * k₂) → ∃! γ, γ ∈ fib α ∧ γ⁻¹ * x ∈ Umax L n := by
    intro α hα
    refine ⟨fun γ hγ => ?_, fun x hx => ?_⟩
    · have e := (Finset.mem_filter.1 hγ).2
      have : γ ∈ dc α := e ▸ hself γ
      exact this
    · have hxD : x ∈ Ds := hdcD α (hRD α hα) x hx
      obtain ⟨γ, ⟨hγ, hu⟩, huniq⟩ := hRu x hxD
      have ht : TrivOutside {s.v} (γ⁻¹ * x) := triv_mul (triv_inv (hDt γ (hRD γ hγ))) (hDt x hxD)
      have hγdc : γ ∈ dc x := ⟨1, K.one_mem, (γ⁻¹ * x)⁻¹, K.inv_mem ⟨hu, ht⟩, by group⟩
      have e : dc γ = dc α := (hdc_eq x γ hγdc).trans (hdc_eq α x hx)
      exact ⟨γ, ⟨Finset.mem_filter.2 ⟨hγ, e⟩, hu⟩, fun δ hδ => huniq δ ⟨(Finset.mem_filter.1 hδ.1).1, hδ.2⟩⟩
  have hfibTriv : ∀ α ∈ R, TrivOutside {s.v} α := fun α hα => hDt α (hRD α hα)
  have conv : ∀ {b x : GAf L n}, (∃ k₁ ∈ Umax L n, ∃ k₂ ∈ Umax L n, TrivOutside {s.v} k₁ ∧ TrivOutside {s.v} k₂ ∧ x = k₁ * b * k₂) ↔
      ∃ k₁ ∈ locK n s.v, ∃ k₂ ∈ locK n s.v, x = k₁ * b * k₂ :=
    ⟨fun ⟨k₁, h₁, k₂, h₂, t₁, t₂, e⟩ => ⟨k₁, ⟨h₁, t₁⟩, k₂, ⟨h₂, t₂⟩, e⟩,
      fun ⟨k₁, h₁, k₂, h₂, e⟩ => ⟨k₁, h₁.1, k₂, h₂.1, h₁.2, h₂.2, e⟩⟩

  have hsplit : ∀ (F : GAf L n → (GAf L n → W)), ∑ γ ∈ R, F γ = ∑ D ∈ R.image dc, ∑ γ ∈ R.filter (fun γ => dc γ = D), F γ :=
    fun F => (Finset.sum_fiberwise_of_maps_to (fun γ hγ => Finset.mem_image_of_mem dc hγ) F).symm
  have hD : ∀ D ∈ R.image dc, ∃ α ∈ R, R.filter (fun γ => dc γ = D) = fib α := by
    intro D hD
    obtain ⟨α, hα, rfl⟩ := Finset.mem_image.1 hD
    exact ⟨α, hα, rfl⟩
  let T : (GAf L n → W) →ₗ[ℂ] (GAf L n → W) := ∑ γ ∈ R, rtHom L n W γ
  have hT : ∀ x, T x = ∑ γ ∈ R, rtHom L n W γ x := fun x => LinearMap.sum_apply _ _ _
  obtain ⟨c, hc⟩ : ∃ c : ℂ, ∀ x ∈ GlobalTheory.SphScalar.fixS (rtHom L n W) S (locK n s.v), T x = c • x := by
    refine GlobalTheory.SphScalar.abs_scalar (rtHom L n W) S hS.1.stable
      (fun S' hle hst => hS.2.2 S' ⟨hle.trans hS.1.le, hst⟩ hle) (rank_le hS) (locK n s.v)
      {x | TrivOutside {s.v} x} {y | TrivOutside {s.v}ᶜ y}
      (fun g => by obtain ⟨x, y, hx, hy, e⟩ := hdec g; exact ⟨x, hx, y, hy, e⟩)
      (fun κ hκ b hb => (hcomm κ b hκ.2 hb).eq) Rb (fun b hb => reps_of_repsU hb (hRb b)) T ?_ ?_ ?_
    · intro x hx
      rw [hT]
      refine ⟨S.sum_mem fun γ _ => hS.1.stable γ x hx.1, fun κ hκ => ?_⟩
      rw [hsplit, map_sum]
      refine Finset.sum_congr rfl fun D hDm => ?_
      obtain ⟨α, hα, e⟩ := hD D hDm
      rw [e]
      have hRα := reps_of_repsU (hfibTriv α hα) (hfib α hα)
      rw [map_sum]
      have := hRα.sum_eq hRα hκ (fun g => rtHom L n W g x)
        (fun y l hl => by rw [map_mul, Module.End.mul_apply, hx.2 l hl])
      simpa only [map_mul, Module.End.mul_apply] using this
    · intro b hb x _
      rw [hT, hT, map_sum]
      refine Finset.sum_congr rfl fun γ hγ => ?_
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, (hcomm γ b (hfibTriv γ hγ) hb).eq]
    · intro b hb x hx
      rw [hT, hT]
      rw [hsplit (fun γ => rtHom L n W γ (∑ δ ∈ Rb b, rtHom L n W δ x)), hsplit (fun γ => rtHom L n W γ x)]
      refine Eq.trans ?_ ((Finset.sum_congr rfl fun δ _ => map_sum (rtHom L n W δ) _ _).trans Finset.sum_comm).symm
      refine Finset.sum_congr rfl fun D hDm => ?_
      obtain ⟨α, hα, e⟩ := hD D hDm
      rw [e]
      exact GlobalTheory.T.splitPlace_doubleCosetOperators_commute_spherical L n W s α b (fib α) (Rb b) (hfibTriv α hα) hb (fun y hy => (hfib α hα).2 y (conv.1 hy))
        (fun γ hγ => conv.2 ((hfib α hα).1 γ hγ)) (fun y hy => (hRb b).2 y (conv.1 hy))
        (fun γ hγ => conv.2 ((hRb b).1 γ hγ)) x (fun κ h1 h2 => hx.2 κ ⟨h1, h2⟩)
  refine ⟨c, fun f hf hfix => ?_⟩
  have e := hc f ⟨hf, fun κ hκ => hfix κ hκ⟩
  rw [hT] at e
  exact e

end GlobalTheory.BiInvScalar

end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.biInvariant_heckeOp_scalar_on_spherical_irreducible : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (GQ L n) W) (S : Submodule ℂ (GAf L n → W)), NG.IsIrrRep ρ S → ∀ (s : SplitPlace L) (Ds : Set (GAf L n)), (∀ x ∈ Ds, TrivOutside {s.v} x) → (∀ x ∈ Ds, ∀ κ ∈ Umax L n, TrivOutside {s.v} κ → x * κ ∈ Ds ∧ κ * x ∈ Ds) → ∀ R : Finset (GAf L n), (∀ γ ∈ R, γ ∈ Ds) → (∀ x ∈ Ds, ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ Umax L n) → ∃ c : ℂ, ∀ f ∈ S, (∀ κ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, NG.rt L n κ f = f) → ∑ γ ∈ R, NG.rt L n γ f = c • f := by
  atlas_forward_decl GlobalTheory.BiInvScalar.biInv_scalar
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RtSumScalar

section Main

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]

theorem rtSum_iso {ρ : Representation ℂ (GQ L n) W} {S S' : Submodule ℂ (GAf L n → W)} (hS : NG.IsSubrep ρ S)
    (hiso : NG.IsoRep S S') (K : Subgroup (GAf L n)) (R : Finset (GAf L n)) (c : ℂ)
    (hc : ∀ f ∈ S, (∀ κ ∈ K, NG.rt L n κ f = f) → ∑ γ ∈ R, NG.rt L n γ f = c • f)
    (f' : GAf L n → W) (hf' : f' ∈ S') (hfix : ∀ κ ∈ K, NG.rt L n κ f' = f') :
    ∑ γ ∈ R, NG.rt L n γ f' = c • f' := by
  classical
  obtain ⟨T, hT⟩ := hiso
  set f : S := T.symm ⟨f', hf'⟩ with hfdef
  have hTf : T f = ⟨f', hf'⟩ := T.apply_symm_apply _
  have hrt : ∀ h : GAf L n, ((T ⟨NG.rt L n h f, hS.stable h _ f.2⟩ : S') : GAf L n → W) = NG.rt L n h f' := by
    intro h
    have := hT h f ⟨_, hS.stable h _ f.2⟩ rfl
    rw [this, hTf]
  have hffix : ∀ κ ∈ K, NG.rt L n κ (f : GAf L n → W) = f := by
    intro κ hκ
    have h1 := hrt κ
    rw [hfix κ hκ] at h1
    have h2 : T ⟨_, hS.stable κ _ f.2⟩ = T f := Subtype.ext (by rw [h1, hTf])
    exact congrArg Subtype.val (T.injective h2)
  have hcf := hc f f.2 hffix
  let σ : S := ∑ γ ∈ R, (⟨NG.rt L n γ f, hS.stable _ _ f.2⟩ : S)
  have hσ : (σ : GAf L n → W) = ∑ γ ∈ R, NG.rt L n γ f := by
    rw [Submodule.coe_sum]
  have hTσ : ((T σ : S') : GAf L n → W) = ∑ γ ∈ R, NG.rt L n γ f' := by
    rw [map_sum, Submodule.coe_sum]
    exact Finset.sum_congr rfl fun γ _ => hrt γ
  have key : σ = c • f := Subtype.ext (by rw [hσ, Submodule.coe_smul]; exact hcf)
  have h3 := congrArg (fun y => ((T y : S') : GAf L n → W)) key
  simp only [map_smul, Submodule.coe_smul, hTσ, hTf] at h3
  exact h3

theorem rtSum_finset_sum {ρ : Representation ℂ (GQ L n) W} {S : Submodule ℂ (GAf L n → W)} (hS : NG.IsIrrRep ρ S)
    (K : Subgroup (GAf L n)) (R : Finset (GAf L n)) (c : ℂ)
    (hc : ∀ f ∈ S, (∀ κ ∈ K, NG.rt L n κ f = f) → ∑ γ ∈ R, NG.rt L n γ f = c • f)
    (t : Finset (Submodule ℂ (GAf L n → W))) :
    (↑t ⊆ {S' | NG.IsIrrRep ρ S' ∧ NG.IsoRep S S'}) → ∀ f ∈ (⨆ i ∈ t, i),
      (∀ κ ∈ K, NG.rt L n κ f = f) → ∑ γ ∈ R, NG.rt L n γ f = c • f := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    intro _ f hf _
    simp only [Finset.notMem_empty, iSup_false, iSup_bot, Submodule.mem_bot] at hf
    subst hf
    simp
  | insert a t ha ih =>
    intro hsub f hf hfix
    have haF : NG.IsIrrRep ρ a ∧ NG.IsoRep S a := hsub (Finset.mem_insert_self a t)
    have htF : (↑t : Set _) ⊆ {S' | NG.IsIrrRep ρ S' ∧ NG.IsoRep S S'} :=
      fun x hx => hsub (Finset.mem_insert_of_mem hx)
    rw [Finset.iSup_insert] at hf
    have hMst : ∀ h, ∀ g ∈ (⨆ i ∈ t, i), NG.rt L n h g ∈ (⨆ i ∈ t, i) :=
      GlobalTheory.HeckeScalarAll.iSup_finset_stable' t (fun i hi => (htF hi).1.1.stable)
    have hsubrep : NG.IsSubrep ρ (a ⊓ ⨆ i ∈ t, i) :=
      ⟨inf_le_left.trans haF.1.1.le, fun h g hg => ⟨haF.1.1.stable h g hg.1, hMst h g hg.2⟩⟩
    rcases haF.1.2.2 _ hsubrep inf_le_left with h0 | htop
    · obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hf
      have hyfix : ∀ κ ∈ K, NG.rt L n κ y = y := by
        intro κ hκ
        have e := hfix κ hκ
        rw [map_add] at e
        have hd : NG.rt L n κ y - y ∈ a ⊓ ⨆ i ∈ t, i := by
          refine ⟨Submodule.sub_mem _ (haF.1.1.stable κ y hy) hy, ?_⟩
          have h4 : NG.rt L n κ y - y = z - NG.rt L n κ z := by
            rw [sub_eq_sub_iff_add_eq_add, e]
            exact add_comm _ _
          rw [h4]
          exact Submodule.sub_mem _ hz (hMst κ z hz)
        rw [h0, Submodule.mem_bot, sub_eq_zero] at hd
        exact hd
      have hzfix : ∀ κ ∈ K, NG.rt L n κ z = z := by
        intro κ hκ
        have e := hfix κ hκ
        rw [map_add, hyfix κ hκ] at e
        exact add_left_cancel e
      have e1 := rtSum_iso hS.1 haF.2 K R c hc y hy hyfix
      have e2 := ih htF z hz hzfix
      simp only [map_add, Finset.sum_add_distrib, e1, e2, smul_add]
    · have hle : a ≤ ⨆ i ∈ t, i := inf_eq_left.1 htop
      exact ih htF f ((sup_le hle le_rfl) hf) hfix

end Main

theorem rtSum_isoTyp : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (GQ L n) W) (S : Submodule ℂ (GAf L n → W)), NG.IsIrrRep ρ S → ∀ (K : Subgroup (GAf L n)) (R : Finset (GAf L n)) (c : ℂ), (∀ f ∈ S, (∀ κ ∈ K, NG.rt L n κ f = f) → ∑ γ ∈ R, NG.rt L n γ f = c • f) → ∀ f ∈ NG.isoTyp ρ S, (∀ κ ∈ K, NG.rt L n κ f = f) → ∑ γ ∈ R, NG.rt L n γ f = c • f := by
  intro L _ _ _ n W _ _ ρ S hS K R c hc f hf hfix
  obtain ⟨t, ht, hft⟩ := Submodule.mem_sSup_iff_exists_finset.1 hf
  exact rtSum_finset_sum hS K R c hc t ht f hft hfix

end GlobalTheory.RtSumScalar
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rightTranslationSum_scalar_on_isotypicPart : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (GQ L n) W) (S : Submodule ℂ (GAf L n → W)), NG.IsIrrRep ρ S → ∀ (K : Subgroup (GAf L n)) (R : Finset (GAf L n)) (c : ℂ), (∀ f ∈ S, (∀ κ ∈ K, NG.rt L n κ f = f) → ∑ γ ∈ R, NG.rt L n γ f = c • f) → ∀ f ∈ NG.isoTyp ρ S, (∀ κ ∈ K, NG.rt L n κ f = f) → ∑ γ ∈ R, NG.rt L n γ f = c • f := by
  atlas_forward_decl GlobalTheory.RtSumScalar.rtSum_isoTyp
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.IsoTypFixLoc

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]

theorem rt_rt (h h' : GAf L n) (f : GAf L n → W) : NG.rt L n h (NG.rt L n h' f) = NG.rt L n (h * h') f := by
  funext g; simp [NG.rt, mul_assoc]

def LocEq (s : SplitPlace L) (τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L)))
    (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L) (T : τ.V →ₗ[ℂ] (GAf L n → W)) : Prop :=
  ∀ x : GAf L n, TrivOutside {s.v} x → ∀ a, T (τ.ρ (Matrix.GeneralLinearGroup.map i.toRingHom (s.loc n x)) a) = NG.rt L n x (T a)

theorem le_iSup_range (ρ : Representation ℂ (GQ L n) W) (S : Submodule ℂ (GAf L n → W)) (hS : NG.IsIrrRep ρ S)
    (s : SplitPlace L) (τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L)))
    (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L) (T0 : τ.V →ₗ[ℂ] (GAf L n → W))
    (hT0inj : Function.Injective T0) (hT0S : ∀ a, T0 a ∈ S) (hT0eq : LocEq s τ i T0) :
    S ≤ ⨆ T : {T : τ.V →ₗ[ℂ] (GAf L n → W) // LocEq s τ i T}, LinearMap.range T.1 := by
  obtain ⟨hdec, hcomm, -⟩ := GlobalTheory.T.unitaryFiniteAdeles_splitPlace_decomposition L n s
  have hnt : Nontrivial τ.V := by
    haveI := τ.irr
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    apply (bot_ne_top : (⊥ : Subrepresentation τ.ρ) ≠ ⊤)
    have : ∀ W : Subrepresentation τ.ρ, W = ⊥ := by
      intro W
      ext x
      simp [Subsingleton.elim x 0]
    rw [this ⊤]
  let Good : (τ.V →ₗ[ℂ] (GAf L n → W)) → Prop := fun T => LocEq s τ i T ∧ ∀ u, T u ∈ S
  let Wd : Submodule ℂ (GAf L n → W) := ⨆ T : {T // Good T}, LinearMap.range T.1
  have hWdS : Wd ≤ S := by
    refine iSup_le fun T => ?_
    rintro _ ⟨u, rfl⟩
    exact T.2.2 u
  have hWdle : Wd ≤ ⨆ T : {T : τ.V →ₗ[ℂ] (GAf L n → W) // LocEq s τ i T}, LinearMap.range T.1 :=
    iSup_le fun T => le_iSup_of_le (⟨T.1, T.2.1⟩ : {T : τ.V →ₗ[ℂ] (GAf L n → W) // LocEq s τ i T}) le_rfl
  have htr : ∀ (T : τ.V →ₗ[ℂ] (GAf L n → W)) (y : GAf L n), Good T → TrivOutside {s.v}ᶜ y → Good ((NG.rt L n y).comp T) := by
    intro T y hT hy
    refine ⟨fun x hx u => ?_, fun u => hS.1.stable y _ (hT.2 u)⟩
    simp only [LinearMap.comp_apply]
    rw [hT.1 x hx u, rt_rt, rt_rt, (hcomm x y hx hy).eq]
  have hstab : ∀ h, ∀ f ∈ Wd, NG.rt L n h f ∈ Wd := by
    intro h f hf
    refine Submodule.iSup_induction _ (motive := fun f => NG.rt L n h f ∈ Wd) hf ?_ ?_ ?_
    · rintro T _ ⟨u, rfl⟩
      obtain ⟨x, y, hx, hy, he⟩ := hdec h
      have e : NG.rt L n h (T.1 u) = ((NG.rt L n y).comp T.1) (τ.ρ (Matrix.GeneralLinearGroup.map i.toRingHom (s.loc n x)) u) := by
        rw [LinearMap.comp_apply, T.2.1 x hx u, rt_rt, he, (hcomm x y hx hy).eq]
      rw [e]
      exact Submodule.mem_iSup_of_mem (⟨_, htr T.1 y T.2 hy⟩ : {T // Good T}) ⟨_, rfl⟩
    · simp
    · intro f₁ f₂ h₁ h₂; rw [map_add]; exact Submodule.add_mem _ h₁ h₂
  have hT0 : Good T0 := ⟨hT0eq, hT0S⟩
  rcases hS.2.2 Wd ⟨hWdS.trans hS.1.le, hstab⟩ hWdS with h0 | h0
  · exfalso
    obtain ⟨u, hu⟩ := exists_ne (0 : τ.V)
    have hmem : T0 u ∈ Wd := Submodule.mem_iSup_of_mem (⟨T0, hT0⟩ : {T // Good T}) ⟨u, rfl⟩
    rw [h0, Submodule.mem_bot] at hmem
    exact hu (hT0inj (hmem.trans (map_zero T0).symm))
  · rw [← h0]
    exact hWdle

theorem isoTyp_le (ρ : Representation ℂ (GQ L n) W) (S : Submodule ℂ (GAf L n → W))
    (s : SplitPlace L) (τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L)))
    (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L) (T0 : τ.V →ₗ[ℂ] (GAf L n → W))
    (hT0inj : Function.Injective T0) (hT0S : ∀ a, T0 a ∈ S) (hT0eq : LocEq s τ i T0) :
    NG.isoTyp ρ S ≤ ⨆ T : {T : τ.V →ₗ[ℂ] (GAf L n → W) // LocEq s τ i T}, LinearMap.range T.1 := by
  refine sSup_le ?_
  rintro S' ⟨hS', E, hE⟩
  let T1 : τ.V →ₗ[ℂ] (GAf L n → W) := S'.subtype ∘ₗ (E : S →ₗ[ℂ] S') ∘ₗ LinearMap.codRestrict S T0 hT0S
  refine le_iSup_range ρ S' hS' s τ i T1 ?_ (fun a => (E _).2) ?_
  · intro a b hab
    apply hT0inj
    have := E.injective (Subtype.ext hab)
    exact congrArg Subtype.val this
  · intro x hx a
    exact hE x ⟨T0 a, hT0S a⟩ ⟨_, hT0S _⟩ (hT0eq x hx a)

end GlobalTheory.IsoTypFixLoc

open GlobalTheory.IsoTypFixLoc in

theorem GlobalTheory.IsoTypFixLoc.main : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (GQ L n) W) (S : Submodule ℂ (GAf L n → W)), NG.IsIrrRep ρ S → ∀ (s : SplitPlace L) (τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))), IsLocS S s τ → ∀ (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L), Continuous i → (∀ x : L, i (s.i x) = algebraMap L (s.w.adicCompletion L) x) → ∀ f ∈ NG.isoTyp ρ S, f ≠ 0 → (∀ κ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, NG.rt L n κ f = f) → ∃ a : τ.V, a ≠ 0 ∧ ∀ κ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, τ.ρ (Matrix.GeneralLinearGroup.map i.toRingHom (s.loc n κ)) a = a := by
  intro L _ _ _ n W _ _ ρ S hS s τ hloc i hi hiL f hf hf0 hfix
  classical
  obtain ⟨i', T0, hi', hi'L, hT0inj, hT0S, hT0eq⟩ := hloc
  obtain rfl := GlobalTheory.splitPlace_completion_equiv_unique L s i' i hi' hi hi'L hiL
  have hspan := isoTyp_le ρ S s τ i' T0 hT0inj hT0S hT0eq hf
  have hI := GlobalTheory.T.unitaryFiniteAdeles_splitPlace_decomposition L n s
  let H : Subgroup (GAf L n) :=
    { carrier := {x | TrivOutside {s.v} x}
      mul_mem' := fun hx hy => GlobalTheory.HeckeScalarSph.triv_mul hx hy
      one_mem' := GlobalTheory.HeckeScalarSph.triv_one
      inv_mem' := fun hx => GlobalTheory.HeckeScalarSph.triv_inv hx }
  let φ : H →* GL (Fin n) (s.w.adicCompletion L) :=
    (Matrix.GeneralLinearGroup.map i'.toRingHom).comp ((s.loc n).comp H.subtype)
  have hφ : Function.Surjective φ := by
    intro h
    obtain ⟨x, ⟨hx, e⟩, -⟩ := hI.2.2 (Matrix.GeneralLinearGroup.map i'.symm.toRingHom h)
    refine ⟨⟨x, hx⟩, ?_⟩
    change Matrix.GeneralLinearGroup.map i'.toRingHom (s.loc n x) = h
    rw [e]
    exact Units.ext (Matrix.ext fun a b => i'.apply_symm_apply _)
  let σ' : Representation ℂ H τ.V := τ.ρ.comp φ
  have hσ' : σ'.IsIrreducible := GlobalTheory.LocCompSplit.isIrreducible_comp_of_surjective τ.ρ φ hφ τ.irr
  let ρ' : Representation ℂ H (GAf L n → W) :=
    { toFun := fun x => NG.rt L n (x : GAf L n)
      map_one' := by
        apply LinearMap.ext
        intro g
        funext a
        simp [NG.rt]
      map_mul' := fun x y => by
        apply LinearMap.ext
        intro g
        funext a
        simp [NG.rt, mul_assoc] }
  rw [Submodule.mem_iSup_iff_exists_finset] at hspan
  obtain ⟨t, ht⟩ := hspan
  let T : t → σ'.IntertwiningMap ρ' := fun j =>
    ⟨j.1.1, fun g => LinearMap.ext fun a => j.1.2 g.1 g.2 a⟩
  have hf' : f ∈ ⨆ j, LinearMap.range (T j).toLinearMap := by
    rw [iSup_subtype'] at ht
    exact ht
  let K : Subgroup H := (GlobalTheory.HeckeScalarSph.locK n s.v).comap H.subtype
  have hfixK : ∀ k ∈ K, ρ' k f = f := fun k hk => hfix k.1 hk
  have hne := GlobalTheory.UnrLoc.fixed_ne_bot_of_mem_iSup_range hσ' T K hf' hf0 hfixK
  rw [Submodule.ne_bot_iff] at hne
  obtain ⟨y, hy, hy0⟩ := hne
  refine ⟨y, hy0, fun κ hκ => ?_⟩
  exact (GlobalTheory.Parabolic.mem_fixed.1 hy) ⟨κ, hκ.2⟩ hκ
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitLocalComponent_has_fixedVector_of_isotypic : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (GQ L n) W) (S : Submodule ℂ (GAf L n → W)), NG.IsIrrRep ρ S → ∀ (s : SplitPlace L) (τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))), IsLocS S s τ → ∀ (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L), Continuous i → (∀ x : L, i (s.i x) = algebraMap L (s.w.adicCompletion L) x) → ∀ f ∈ NG.isoTyp ρ S, f ≠ 0 → (∀ κ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, NG.rt L n κ f = f) → ∃ a : τ.V, a ≠ 0 ∧ ∀ κ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, τ.ρ (Matrix.GeneralLinearGroup.map i.toRingHom (s.loc n κ)) a = a := by
  first | exact @GlobalTheory.IsoTypFixLoc.main | exact GlobalTheory.IsoTypFixLoc.main | (intros; apply GlobalTheory.IsoTypFixLoc.main <;> assumption)
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LocEigAgree

theorem main : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D) (i : D.nd.Loc) (Q Q' : D.naut.AV i) (sp : SplitPlace D.host.E), (∀ κ : GAf D.host.E D.R.nV, TrivOutside {sp.v} κ → (κ ∈ (P.M.loc i).J ↔ κ ∈ Umax D.host.E D.R.nV) ∧ ∀ hκ : κ ∈ (P.M.loc i).J, (P.M.loc i).χ ⟨κ, hκ⟩ = 1) → ∀ Ds : Set (GAf D.host.E D.R.nV), (∀ x ∈ Ds, TrivOutside {sp.v} x) → (∀ x ∈ Ds, ∀ κ ∈ Umax D.host.E D.R.nV, TrivOutside {sp.v} κ → x * κ ∈ Ds ∧ κ * x ∈ Ds) → {c : GAf D.host.E D.R.nV ⧸ (P.M.loc i).J | ∃ x ∈ Ds, (x : GAf D.host.E D.R.nV ⧸ (P.M.loc i).J) = c}.Finite → (∀ σ σ', IsLocS (P.H.av.S i Q) sp σ → IsLocS (P.H.av.S i Q') sp σ' → GlobalTheory.LocLanglands.cls σ = GlobalTheory.LocLanglands.cls σ') → ∀ F ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q), F ∈ NG.TypeSp (P.M.loc i).wt.ρ (P.M.loc i).J (P.M.loc i).χ → F ≠ 0 → ∀ F' ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q'), F' ∈ NG.TypeSp (P.M.loc i).wt.ρ (P.M.loc i).J (P.M.loc i).χ → F' ≠ 0 → ∀ c c' : ℂ, NG.heckeD (P.M.loc i).J Ds F = c • F → NG.heckeD (P.M.loc i).J Ds F' = c' • F' → c = c' := by
  intro _hAF hL D P i Q Q' sp hJ Ds hDs hbi hfin hcls F hF hFT hF0 F' hF' hF'T hF'0 c c' hc hc'
  classical

  have hK : ∀ f ∈ NG.TypeSp (P.M.loc i).wt.ρ (P.M.loc i).J (P.M.loc i).χ,
      ∀ κ ∈ GlobalTheory.HeckeScalarSph.locK D.R.nV sp.v, NG.rt D.host.E D.R.nV κ f = f := by
    intro f hf κ hκ
    obtain ⟨h1, h2⟩ := hJ κ hκ.2
    have hJκ : κ ∈ (P.M.loc i).J := h1.2 hκ.1
    have e := hf.2 ⟨κ, hJκ⟩
    rw [h2 hJκ] at e
    simpa using e
  have hJU : ∀ x ∈ Ds, ∀ x' ∈ Ds, (x⁻¹ * x' ∈ (P.M.loc i).J ↔ x⁻¹ * x' ∈ Umax D.host.E D.R.nV) :=
    fun x hx x' hx' => (hJ _ (GlobalTheory.HeckeScalarAll.trivOutside_mul (GlobalTheory.HeckeScalarAll.trivOutside_inv (hDs x hx))
      (hDs x' hx'))).1

  have hfinU : ((fun x : GAf D.host.E D.R.nV => (x : GAf D.host.E D.R.nV ⧸ Umax D.host.E D.R.nV)) '' Ds).Finite := by
    let φ : GAf D.host.E D.R.nV ⧸ (P.M.loc i).J → GAf D.host.E D.R.nV ⧸ Umax D.host.E D.R.nV := fun c =>
      if hc : ∃ x ∈ Ds, (x : GAf D.host.E D.R.nV ⧸ (P.M.loc i).J) = c then (hc.choose : GAf D.host.E D.R.nV ⧸ Umax D.host.E D.R.nV) else ((1 : GAf D.host.E D.R.nV) : GAf D.host.E D.R.nV ⧸ Umax D.host.E D.R.nV)
    refine (hfin.image φ).subset ?_
    rintro _ ⟨x, hx, rfl⟩
    have hc : ∃ y ∈ Ds, (y : GAf D.host.E D.R.nV ⧸ (P.M.loc i).J) = (x : GAf D.host.E D.R.nV ⧸ (P.M.loc i).J) := ⟨x, hx, rfl⟩
    refine ⟨(x : GAf D.host.E D.R.nV ⧸ (P.M.loc i).J), ⟨x, hx, rfl⟩, ?_⟩
    simp only [φ, dif_pos hc]
    have h1 := hc.choose_spec.2
    rw [QuotientGroup.eq] at h1
    exact QuotientGroup.eq.2 ((hJU _ hc.choose_spec.1 _ hx).1 h1)
  obtain ⟨R, hR1, hR2⟩ := GlobalTheory.HeckeScalarSph.exists_reps (Umax D.host.E D.R.nV) Ds hfinU
  have hH : ∀ f : GAf D.host.E D.R.nV → (P.M.loc i).wt.W, (∀ κ ∈ GlobalTheory.HeckeScalarSph.locK D.R.nV sp.v, NG.rt D.host.E D.R.nV κ f = f) →
      NG.heckeD (P.M.loc i).J Ds f = ∑ γ ∈ R, NG.rt D.host.E D.R.nV γ f := by
    intro f hf
    have hf' : ∀ κ ∈ Umax D.host.E D.R.nV, TrivOutside {sp.v} κ → NG.rt D.host.E D.R.nV κ f = f :=
      fun κ hκ ht => hf κ ⟨hκ, ht⟩
    have e1 : NG.heckeD (P.M.loc i).J Ds f = NG.heckeD (Umax D.host.E D.R.nV) Ds f := by
      funext g
      simp only [NG.heckeD]
      refine GlobalTheory.HeckeScalarAll.finsum_cosets_eq (P.M.loc i).J (Umax D.host.E D.R.nV) Ds (fun x => f (g * x)) hJU ?_
      intro x hx x' hx' hu
      have ht := GlobalTheory.HeckeScalarAll.trivOutside_mul (GlobalTheory.HeckeScalarAll.trivOutside_inv (hDs x hx)) (hDs x' hx')
      have h1 := congrFun (hf' _ hu ht) (g * x)
      simp only [NG.rt, LinearMap.coe_mk, AddHom.coe_mk] at h1
      rw [mul_assoc, mul_inv_cancel_left] at h1
      exact h1.symm
    rw [e1]
    exact GlobalTheory.HeckeScalarSph.heckeD_eq_sum (v := sp.v) hDs hR1 hR2 hf'

  obtain ⟨cX, hcX⟩ := GlobalTheory.T.biInvariant_heckeOp_scalar_on_spherical_irreducible D.host.E D.R.nV _ _ _ (P.H.av.irr i Q) sp Ds hDs hbi R hR1 hR2
  obtain ⟨cX', hcX'⟩ := GlobalTheory.T.biInvariant_heckeOp_scalar_on_spherical_irreducible D.host.E D.R.nV _ _ _ (P.H.av.irr i Q') sp Ds hDs hbi R hR1 hR2
  have hcI := GlobalTheory.T.rightTranslationSum_scalar_on_isotypicPart D.host.E D.R.nV _ _ _ (P.H.av.irr i Q) _ R cX hcX
  have hcI' := GlobalTheory.T.rightTranslationSum_scalar_on_isotypicPart D.host.E D.R.nV _ _ _ (P.H.av.irr i Q') _ R cX' hcX'
  have hc1 : c = cX := by
    have e1 := hc
    rw [hH F (hK F hFT), hcI F hF (hK F hFT)] at e1
    exact smul_left_injective ℂ hF0 e1.symm
  have hc2 : c' = cX' := by
    have e1 := hc'
    rw [hH F' (hK F' hF'T), hcI' F' hF' (hK F' hF'T)] at e1
    exact smul_left_injective ℂ hF'0 e1.symm
  rw [hc1, hc2]

  let π : NG.AutRep D.host.E D.R.nV := ⟨(P.M.loc i).wt, P.H.av.S i Q, P.H.av.irr i Q⟩
  let π' : NG.AutRep D.host.E D.R.nV := ⟨(P.M.loc i).wt, P.H.av.S i Q', P.H.av.irr i Q'⟩
  obtain ⟨σ, hσ⟩ := GlobalTheory.LocCompSplit.exists_isLocS π sp
  obtain ⟨σ', hσ'⟩ := GlobalTheory.LocCompSplit.exists_isLocS π' sp
  have hcl := hcls σ σ' hσ hσ'
  obtain ⟨E⟩ : Nonempty (σ.ρ.Equiv σ'.ρ) := by
    have h2 : σ.cl = σ'.cl := eq_of_heq (Sigma.mk.inj hcl).2
    exact GlobalTheory.SmGL.IrrRep.cl_eq_iff.1 h2
  have hσ0 := hσ
  obtain ⟨ι, T0, hι, hιc, hT0i, hT0S, hT0e⟩ := hσ
  obtain ⟨ι', T0', hι', hιc', hT0i', hT0S', hT0e'⟩ := hσ'
  obtain rfl := GlobalTheory.splitPlace_completion_equiv_unique _ sp ι ι' hι hι' hιc hιc'
  obtain ⟨a, ha0, hafix⟩ := GlobalTheory.T.splitLocalComponent_has_fixedVector_of_isotypic D.host.E D.R.nV _ _ _ (P.H.av.irr i Q) sp σ hσ0 ι hι hιc F hF hF0 (hK F hFT)
  have hT0H : ∀ v, T0 (∑ γ ∈ R, σ.ρ (Matrix.GeneralLinearGroup.map ι.toRingHom (sp.loc D.R.nV γ)) v) =
      ∑ γ ∈ R, NG.rt D.host.E D.R.nV γ (T0 v) := by
    intro v
    rw [map_sum]
    exact Finset.sum_congr rfl fun γ hγ => hT0e γ (hDs γ (hR1 γ hγ)) v
  have hT0H' : ∀ v, T0' (∑ γ ∈ R, σ'.ρ (Matrix.GeneralLinearGroup.map ι.toRingHom (sp.loc D.R.nV γ)) v) =
      ∑ γ ∈ R, NG.rt D.host.E D.R.nV γ (T0' v) := by
    intro v
    rw [map_sum]
    exact Finset.sum_congr rfl fun γ hγ => hT0e' γ (hDs γ (hR1 γ hγ)) v
  have hT0fix : ∀ κ ∈ GlobalTheory.HeckeScalarSph.locK D.R.nV sp.v, NG.rt D.host.E D.R.nV κ (T0 a) = T0 a := by
    intro κ hκ
    rw [← hT0e κ hκ.2 a, hafix κ hκ]
  have hHa : ∑ γ ∈ R, σ.ρ (Matrix.GeneralLinearGroup.map ι.toRingHom (sp.loc D.R.nV γ)) a = cX • a := by
    apply hT0i
    rw [hT0H, map_smul]
    exact hcX (T0 a) (hT0S a) hT0fix
  have hE : ∀ g v, E.toLinearEquiv (σ.ρ g v) = σ'.ρ g (E.toLinearEquiv v) := fun g v =>
    LinearMap.congr_fun (E.isIntertwining' g) v
  have ha'0 : E.toLinearEquiv a ≠ 0 := fun h => ha0 (E.toLinearEquiv.injective (by rw [h, map_zero]))
  have hHa' : ∑ γ ∈ R, σ'.ρ (Matrix.GeneralLinearGroup.map ι.toRingHom (sp.loc D.R.nV γ)) (E.toLinearEquiv a) =
      cX • E.toLinearEquiv a := by
    simp only [← hE, ← map_sum, hHa, map_smul]
  have hT0fix' : ∀ κ ∈ GlobalTheory.HeckeScalarSph.locK D.R.nV sp.v,
      NG.rt D.host.E D.R.nV κ (T0' (E.toLinearEquiv a)) = T0' (E.toLinearEquiv a) := by
    intro κ hκ
    rw [← hT0e' κ hκ.2, ← hE, hafix κ hκ]
  have key := hcX' (T0' (E.toLinearEquiv a)) (hT0S' _) hT0fix'
  rw [← hT0H', hHa', map_smul] at key
  have hne : T0' (E.toLinearEquiv a) ≠ 0 := fun h => ha'0 (hT0i' (by rw [h, map_zero]))
  exact smul_left_injective ℂ hne key

end GlobalTheory.LocEigAgree
end
end
