import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenRegularCharacters
import Formalism.LocalToGlobal.GlobalTheory.IrreducibleOfCountSizes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BadPartDimLeSumLocalSharesWhittakerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedIdempotentLocalShareBadTuplesLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWhittakerDatumAndHalfLevels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BadShareSizeBoundsAlongFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteCuspFormsFiniteRegularRepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LactMemDomOfIsom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbedsInRegularRepresentationCopiesOfGroupDeterm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspFormIndependentTranslates
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormPullbackIsBoundedSection
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.CountAsmPfB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLevelFlagDomainEigenspaceShare
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLevelFlagDomainCuspFormRanksShiftedWeights
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWhittakerCharacterPairStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LemmaLSeriesWeightsOfGreenCuspidalParametrisatioStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumRangeEqRoots
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankIInfKerEqOfIsBaseChangeFamily
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsRingEquivComplexCompEq
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted

section
noncomputable section

namespace GlobalTheory.TwistedRepresentationEmbedding

open Module

def twist {K G V : Type} [Field K] [Group G] [AddCommGroup V] [Module K V] (ρ : Representation K G V) (χ : G →* Kˣ) :
    Representation K G V where
  toFun g := ((χ g : Kˣ) : K) • ρ g
  map_one' := by simp
  map_mul' g h := by
    ext v
    simp only [map_mul, Units.val_mul, Module.End.mul_apply, LinearMap.smul_apply, map_smul, smul_smul]
    ring_nf

theorem twist_apply {K G V : Type} [Field K] [Group G] [AddCommGroup V] [Module K V] (ρ : Representation K G V)
    (χ : G →* Kˣ) (g : G) (v : V) : twist ρ χ g v = ((χ g : Kˣ) : K) • ρ g v := rfl

def embV {K : Type} [Field K] (σ : K →+* ℂ) (N : ℕ) : (Fin N → K) →ₛₗ[σ] (Fin N → ℂ) where
  toFun v k := σ (v k)
  map_add' v w := by funext k; simp
  map_smul' a v := by funext k; simp

def repE {K G : Type} [Field K] [Group G] {N : ℕ} (σ : K →+* ℂ) (ρ : Representation K G (Fin N → K)) :
    Representation ℂ G (Fin N → ℂ) where
  toFun g := Matrix.toLin' ((LinearMap.toMatrix' (ρ g)).map σ)
  map_one' := by
    rw [map_one, LinearMap.toMatrix'_one, Matrix.map_one σ (map_zero σ) (map_one σ), Matrix.toLin'_one]; rfl
  map_mul' g h := by
    rw [map_mul, LinearMap.toMatrix'_mul, Matrix.map_mul, Matrix.toLin'_mul]; rfl

theorem repE_embV {K G : Type} [Field K] [Group G] {N : ℕ} (σ : K →+* ℂ) (ρ : Representation K G (Fin N → K)) (g : G)
    (v : Fin N → K) : repE σ ρ g (embV σ N v) = embV σ N (ρ g v) := by
  funext k
  change (Matrix.toLin' ((LinearMap.toMatrix' (ρ g)).map σ)) (fun j => σ (v j)) k = σ (ρ g v k)
  have h := RingHom.map_mulVec σ (LinearMap.toMatrix' (ρ g)) v k
  rw [LinearMap.toMatrix'_mulVec] at h
  rw [Matrix.toLin'_apply, h]
  rfl

theorem embV_single {K : Type} [Field K] (σ : K →+* ℂ) (N : ℕ) (k : Fin N) :
    embV σ N (Pi.single k 1) = Pi.single k 1 := by
  funext j
  change σ ((Pi.single k (1 : K) : Fin N → K) j) = (Pi.single k (1 : ℂ) : Fin N → ℂ) j
  by_cases h : j = k
  · subst h; simp
  · simp [Pi.single_apply, h]

theorem embV_li {K : Type} [Field K] (σ : K →+* ℂ) (N : ℕ) :
    LinearIndependent ℂ fun k => embV σ N (Pi.single k 1) := by
  convert (Pi.basisFun ℂ (Fin N)).linearIndependent using 1
  funext k
  simp [embV_single]

theorem embV_span {K : Type} [Field K] (σ : K →+* ℂ) (N : ℕ) :
    Submodule.span ℂ (Set.range (embV σ N)) = ⊤ := by
  refine eq_top_iff.2 ((Pi.basisFun ℂ (Fin N)).span_eq.ge.trans (Submodule.span_mono ?_))
  rintro _ ⟨k, rfl⟩
  exact ⟨Pi.single k 1, by simp [embV_single]⟩

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

theorem isPullRep_twist {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {U C : Type} [Group U]
    [MulAction U C] {M : TwoLevels E r U C} {la : Wt M.Ψ r} {ρ : Representation ℂ U (M.cusp la)}
    (h : IsPullRep M la ρ) (χ : U →* ℂˣ) : IsPullRep M la (twist ρ χ) := by
  obtain ⟨a, ha⟩ := h
  refine ⟨fun u c => χ u⁻¹ * a u c, fun u F hF c x => ?_⟩
  rw [twist_apply, Submodule.coe_smul, Pi.smul_apply, Pi.smul_apply, ha u F hF c x]
  simp [mul_assoc]

end GlobalTheory.TwistedRepresentationEmbedding

end
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_whittakerDatum_and_halfLevels : ∀ (D : D7) (ψ : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), AddChar (ZMod (D.host.g kv.1)) ℂ), (∀ kv, ψ kv ≠ 1) → (∃ (P : Subgroup (G0g D.nd)) (lam : P →* ℂˣ), IsWhit D P lam ψ) ∧ ∀ k, ∃ H, IsHalf D k H := by
  first | exact @GlobalTheory.BadCount.Inh.exists_whit_half | exact GlobalTheory.BadCount.Inh.exists_whit_half | (intros; apply GlobalTheory.BadCount.Inh.exists_whit_half <;> assumption)
end

section
section
set_option autoImplicit false

noncomputable section

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn GlobalTheory.CuspEmb

namespace GlobalTheory.CuspEmb

theorem pull_mem_SS : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C]
    (M : TwoLevels E r U C) (la : Wt M.Ψ r) (F : C → Frame M.Ψ r → ℂ) (h : U), F ∈ M.SS la → M.pull h F ∈ M.SS la := by
  intro E _ _ _ r U C _ _ M la F h hF c
  have hm : GlobalTheory.LevelCusp.IsMatch (M.comp c).toData (M.comp (h • c)).toData (M.tr h c) :=
    { psi := (M.comp_Ψ c).trans (M.comp_Ψ (h • c)).symm
      p0 := (M.comp_basePoint c).trans (M.comp_basePoint (h • c)).symm
      xi := (M.comp_ξ0 c).trans (M.comp_ξ0 (h • c)).symm
      iso := fun u v => by
        show herm (M.comp (h • c)).Gm _ _ = herm (M.comp c).Gm u v
        rw [M.comp_Gm, M.comp_Gm]
        exact M.tr_herm h c u v
      lat := fun v => M.tr_Λ h c v }
  exact GlobalTheory.LevelCusp.mem_SS_of_isMatch E r _ _ (M.tr h c) hm (castWt (M.comp_Ψ c) la)
    (castWt (M.comp_Ψ (h • c)) la) (fun τ i => rfl) _ (fun y => F (h • c) (castFrame (M.comp_Ψ (h • c)) y)) 1
    (GlobalTheory.PullBdd.pull_isBddSec E r U C M la F hF h c).1 (hF (h • c)) (fun x _ => by rw [one_mul]; rfl)

end GlobalTheory.CuspEmb

end
end

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn GlobalTheory.CuspEmb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twoLevelCuspForms_pull_mem : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C] (M : TwoLevels E r U C) (la : Wt M.Ψ r) (F : C → Frame M.Ψ r → ℂ) (h : U), F ∈ M.SS la → M.pull h F ∈ M.SS la := by
  atlas_forward_decl GlobalTheory.CuspEmb.pull_mem_SS
end

section
section
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn GlobalTheory.CuspEmb

namespace GlobalTheory.CuspEmb

theorem twoLevels_mul_mem_SS : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C] (M : TwoLevels E r U C) (la mu : Wt M.Ψ r) (F G : C → Frame M.Ψ r → ℂ), F ∈ M.SS la → G ∈ M.SS mu → F * G ∈ M.SS (la + mu) := by
  intro E _ _ _ r U C _ _ M la mu F G hF hG c
  have hP := hF c
  have hQ := (hG c).1
  have h := ReciprocityTheory.ChartRestriction.G.AR.Up.ss_mul_pow (M.comp c).toData hP hQ 1
  have hw : castWt (M.comp_Ψ c) (la + mu) =
      castWt (M.comp_Ψ c) la + 1 • castWt (M.comp_Ψ c) mu := by
    rw [one_smul]; funext τ; rfl
  rw [hw]
  rw [pow_one] at h
  exact h

end GlobalTheory.CuspEmb
end

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn GlobalTheory.CuspEmb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twoLevelCuspForms_mul_mem_add_weight : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C] (M : TwoLevels E r U C) (la mu : Wt M.Ψ r) (F G : C → Frame M.Ψ r → ℂ), F ∈ M.SS la → G ∈ M.SS mu → F * G ∈ M.SS (la + mu) := by
  atlas_forward_decl GlobalTheory.CuspEmb.twoLevels_mul_mem_SS
end

section
section
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn GlobalTheory.CuspEmb

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CuspEmb

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem isSec_cast (X : Data E r) (Ψ : Finset (E →+* ℂ)) (Gm : Matrix (Fin r) (Fin r) E) (p0 : ℕ)
    (h1 : X.Ψ = Ψ) (h2 : X.Gm = Gm) (h3 : X.p0 = p0) (la : Wt Ψ r) (G : Frame Ψ r → ℂ)
    (hG : X.IsSec (castWt h1 la) (fun x => G (castFrame h1 x))) :
    DifferentiableOn ℂ G (GG Ψ Gm p0) ∧
      ∀ γ ∈ X.Γ, ∀ x ∈ GG Ψ Gm p0, G (lact γ x) = X.χ (castWt h1 la) γ * G x := by
  subst h1 h2 h3
  exact ⟨hG.1, hG.2.2⟩

theorem res_mem_HA (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C]
    (M : TwoLevels E r U C) (la : Wt M.Ψ r) (F : C → Frame M.Ψ r → ℂ) (hF : F ∈ M.SS la) : M.res F ∈ HA M := by
  have key := fun c => isSec_cast (M.comp c).toData M.Ψ M.Gm M.p0 (M.comp_Ψ c) (M.comp_Gm c) (M.comp_basePoint c) la (F c)
    (hF c).1.1
  refine ⟨fun c => ⟨F c, (key c).1, fun x => rfl⟩, fun c γ hγ x hx => ?_⟩
  show F c (lact γ x.1) = F c x.1
  rw [(key c).2 γ hγ x.1 x.2, M.χ_one c _ γ hγ, one_mul]

end GlobalTheory.CuspEmb

end
end

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn GlobalTheory.CuspEmb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twoLevelCuspForms_restrict_holInvariant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C] (M : TwoLevels E r U C) (la : Wt M.Ψ r) (F : C → Frame M.Ψ r → ℂ), F ∈ M.SS la → M.res F ∈ HA M := by
  atlas_forward_decl GlobalTheory.CuspEmb.res_mem_HA
end

section
section
set_option autoImplicit false

noncomputable section

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn GlobalTheory.CuspEmb

namespace GlobalTheory.PullCocycle

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {U C : Type} [Group U] [MulAction U C]

theorem formula_span (M : TwoLevels E r U C) (ka : Wt M.Ψ r) (ρ : Representation ℂ U (M.cusp ka))
    (a : U → C → ℂˣ)
    (ha : ∀ (h : U) (F : C → Frame M.Ψ r → ℂ) (hF : F ∈ M.SS ka) (c : C) (x : M.dom),
      ((ρ h⁻¹ ⟨M.res F, Submodule.subset_span ⟨F, hF, rfl⟩⟩ : M.cusp ka) : C → M.dom → ℂ) c x =
        (a h c : ℂ) * M.pull h F c x.1)
    (h : U) (c : C) (x : M.dom) (g : C → M.dom → ℂ) (hg : g ∈ Submodule.span ℂ (M.res '' M.SS ka)) :
    ((ρ h⁻¹ ⟨g, hg⟩ : M.cusp ka) : C → M.dom → ℂ) c x = (a h c : ℂ) * g (h • c) (Lmap M h c x) := by
  induction hg using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨F, hF, rfl⟩ := hy
    exact ha h F hF c x
  | zero =>
    show ((ρ h⁻¹ 0 : M.cusp ka) : C → M.dom → ℂ) c x = _
    simp
  | add y z hy hz ihy ihz =>
    show ((ρ h⁻¹ ((⟨y, hy⟩ : M.cusp ka) + ⟨z, hz⟩) : M.cusp ka) : C → M.dom → ℂ) c x = _
    rw [map_add, Submodule.coe_add, Pi.add_apply, Pi.add_apply, ihy, ihz]
    simp [mul_add]
  | smul t y hy ih =>
    show ((ρ h⁻¹ (t • (⟨y, hy⟩ : M.cusp ka)) : M.cusp ka) : C → M.dom → ℂ) c x = _
    rw [map_smul, Submodule.coe_smul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, ih]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

theorem rho_inv_rho (M : TwoLevels E r U C) (ka : Wt M.Ψ r) (ρ : Representation ℂ U (M.cusp ka)) (h : U)
    (f : M.cusp ka) : ρ h⁻¹ (ρ h f) = f := by
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem pull_mul_eq (M : TwoLevels E r U C) (f : C → M.dom → ℂ) (hf : IsInv M f) (g h : U) (c : C) (x : M.dom) :
    f ((h * g) • c) (Lmap M (h * g) c x) = f (h • g • c) (Lmap M h (g • c) (Lmap M g c x)) := by
  set γ := M.tr (h * g) c * (M.tr h (g • c) * M.tr g c)⁻¹ with hγdef
  have hγ : γ ∈ (M.comp ((h * g) • c)).Γ := M.tr_mul h g c
  have e : lact γ (Lmap M h (g • c) (Lmap M g c x)).1 = (Lmap M (h * g) c x).1 := by
    show lact γ (lact (M.tr h (g • c)) (lact (M.tr g c) x.1)) = lact (M.tr (h * g) c) x.1
    rw [← ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf.lact_mul (M.tr h (g • c)) (M.tr g c),
      ← ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf.lact_mul γ, hγdef, inv_mul_cancel_right]
  have hx : lact γ (Lmap M h (g • c) (Lmap M g c x)).1 ∈ M.dom := e ▸ (Lmap M (h * g) c x).2
  have := hf ((h * g) • c) γ hγ (Lmap M h (g • c) (Lmap M g c x)) hx
  have e2 : (⟨lact γ (Lmap M h (g • c) (Lmap M g c x)).1, hx⟩ : M.dom) = Lmap M (h * g) c x := Subtype.ext e
  rw [e2] at this
  rw [this, mul_smul]

theorem exists_cocycle : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C] (M : TwoLevels E r U C) (ka : Wt M.Ψ r) (ρ : Representation ℂ U (M.cusp ka)), IsPullRep M ka ρ → (∀ f ∈ M.cusp ka, IsInv M f) → ∃ a : U → C → ℂˣ, (∀ (g h : U) (c : C), a (h * g) c = a g c * a h (g • c)) ∧ ∀ (h : U) (f : M.cusp ka) (c : C) (x : M.dom), ((ρ h⁻¹ f : M.cusp ka) : C → M.dom → ℂ) c x = (a h c : ℂ) * (f : C → M.dom → ℂ) (h • c) (Lmap M h c x) := by
  intro E _ _ _ r U C _ _ M ka ρ hρ hinv
  obtain ⟨a, ha⟩ := hρ
  have hform : ∀ (h : U) (f : M.cusp ka) (c : C) (x : M.dom),
      ((ρ h⁻¹ f : M.cusp ka) : C → M.dom → ℂ) c x = (a h c : ℂ) * (f : C → M.dom → ℂ) (h • c) (Lmap M h c x) := by
    rintro h ⟨g, hg⟩ c x
    exact formula_span M ka ρ a ha h c x g hg
  classical
  let C0 : C → Prop := fun c => ∃ f : M.cusp ka, ∃ x : M.dom, (f : C → M.dom → ℂ) c x ≠ 0
  have hstab : ∀ (h : U) (c : C), C0 c → C0 (h • c) := by
    rintro h c ⟨f, x, hfx⟩
    refine ⟨ρ h f, Lmap M h c x, fun h0 => hfx ?_⟩
    calc (f : C → M.dom → ℂ) c x = ((ρ h⁻¹ (ρ h f) : M.cusp ka) : C → M.dom → ℂ) c x := by
          rw [rho_inv_rho]
      _ = (a h c : ℂ) * ((ρ h f : M.cusp ka) : C → M.dom → ℂ) (h • c) (Lmap M h c x) := hform h _ c x
      _ = 0 := by rw [h0, mul_zero]
  have hstab' : ∀ (h : U) (c : C), ¬ C0 c → ¬ C0 (h • c) := fun h c hc h1 => hc (by
    have := hstab h⁻¹ (h • c) h1
    rwa [inv_smul_smul] at this)
  have hcoc : ∀ (g h : U) (c : C) (x : M.dom) (f : M.cusp ka),
      (a (h * g) c : ℂ) * (f : C → M.dom → ℂ) ((h * g) • c) (Lmap M (h * g) c x) =
        (a g c : ℂ) * (a h (g • c) : ℂ) * (f : C → M.dom → ℂ) ((h * g) • c) (Lmap M (h * g) c x) := by
    intro g h c x f
    have L := hform (h * g) f c x
    have R : ((ρ (h * g)⁻¹ f : M.cusp ka) : C → M.dom → ℂ) c x =
        (a g c : ℂ) * ((a h (g • c) : ℂ) * (f : C → M.dom → ℂ) (h • g • c) (Lmap M h (g • c) (Lmap M g c x))) := by
      rw [mul_inv_rev, map_mul, Module.End.mul_apply, hform g, hform h]
    rw [← L, R, pull_mul_eq M _ (hinv _ f.2) g h c x]
    ring
  refine ⟨fun h c => if C0 c then a h c else 1, ?_, ?_⟩
  · intro g h c
    by_cases hc : C0 c
    · have hgc : C0 (g • c) := hstab g c hc
      have hhgc : C0 ((h * g) • c) := hstab (h * g) c hc
      simp only [hc, hgc, if_true]
      obtain ⟨f', x, hfx⟩ := hc
      set f := ρ (h * g) f' with hfdef
      have hV : (f : C → M.dom → ℂ) ((h * g) • c) (Lmap M (h * g) c x) ≠ 0 := by
        intro h0
        apply hfx
        calc (f' : C → M.dom → ℂ) c x = ((ρ (h * g)⁻¹ f : M.cusp ka) : C → M.dom → ℂ) c x := by
              rw [hfdef, rho_inv_rho]
          _ = 0 := by rw [hform, h0, mul_zero]
      ext
      push_cast
      exact mul_right_cancel₀ hV (hcoc g h c x f)
    · have hgc : ¬ C0 (g • c) := hstab' g c hc
      simp [hc, hgc]
  · intro h f c x
    by_cases hc : C0 c
    · simp only [hc, if_true]
      exact hform h f c x
    · have hhc : ¬ C0 (h • c) := hstab' h c hc
      simp only [hc, if_false, Units.val_one, one_mul]
      have l0 : ((ρ h⁻¹ f : M.cusp ka) : C → M.dom → ℂ) c x = 0 := by
        by_contra hne
        exact hc ⟨ρ h⁻¹ f, x, hne⟩
      have r0 : (f : C → M.dom → ℂ) (h • c) (Lmap M h c x) = 0 := by
        by_contra hne
        exact hhc ⟨f, _, hne⟩
      rw [l0, r0]

end GlobalTheory.PullCocycle

end
end

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn GlobalTheory.CuspEmb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cocycle_pullbackRepresentation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C] (M : TwoLevels E r U C) (ka : Wt M.Ψ r) (ρ : Representation ℂ U (M.cusp ka)), IsPullRep M ka ρ → (∀ f ∈ M.cusp ka, IsInv M f) → ∃ a : U → C → ℂˣ, (∀ (g h : U) (c : C), a (h * g) c = a g c * a h (g • c)) ∧ ∀ (h : U) (f : M.cusp ka) (c : C) (x : M.dom), ((ρ h⁻¹ f : M.cusp ka) : C → M.dom → ℂ) c x = (a h c : ℂ) * (f : C → M.dom → ℂ) (h • c) (Lmap M h c x) := by
  atlas_forward_decl GlobalTheory.PullCocycle.exists_cocycle
end

section
section
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn GlobalTheory.CuspEmb

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CuspEmb

theorem isOpen_isPreconnected_dom {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {U C : Type} [Group U]
    [MulAction U C] (M : TwoLevels E r U C) (c : C) : IsOpen M.dom ∧ IsPreconnected M.dom := by
  have key : ∀ (X : Data E r) (Ψ : Finset (E →+* ℂ)) (Gm : Matrix (Fin r) (Fin r) E) (p0 : ℕ),
      X.Ψ = Ψ → X.Gm = Gm → X.p0 = p0 → IsOpen (GG Ψ Gm p0) ∧ IsPreconnected (GG Ψ Gm p0) := by
    intro X Ψ Gm p0 h1 h2 h3
    subst h1 h2 h3
    exact ⟨FourierCoefficientDomain.isOpen_dom X, (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.flag_domain_frames_connected r X).isPreconnected⟩
  exact key (M.comp c).toData M.Ψ M.Gm M.p0 (M.comp_Ψ c) (M.comp_Gm c) (M.comp_basePoint c)

theorem C_mem_nonZeroDivisors : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U]
    [MulAction U C] (M : TwoLevels E r U C) (D : HA M), (∀ c, ∃ x : M.dom, (D : C → M.dom → ℂ) c x ≠ 0) →
    Polynomial.C D ∈ nonZeroDivisors (Polynomial (HA M)) := by
  intro E _ _ _ r U C _ _ M D hD
  have key : ∀ p : Polynomial (HA M), p * Polynomial.C D = 0 → p = 0 := by
    intro p hp
    ext i : 1
    have hq : p.coeff i * D = 0 := by
      have := congrArg (fun q => Polynomial.coeff q i) hp
      simp only [Polynomial.coeff_mul_C, Polynomial.coeff_zero] at this
      exact this
    have hq' : ((p.coeff i : HA M) : C → M.dom → ℂ) * (D : C → M.dom → ℂ) = 0 := by
      have := congrArg (fun f : HA M => (f : C → M.dom → ℂ)) hq
      exact this
    rw [Polynomial.coeff_zero]
    apply Subtype.ext
    funext c x
    obtain ⟨x0, hx0⟩ := hD c
    obtain ⟨GD, hGD, hGD'⟩ := D.2.1 c
    obtain ⟨Gq, hGq, hGq'⟩ := (p.coeff i).2.1 c
    obtain ⟨hO, hC⟩ := isOpen_isPreconnected_dom M c
    have h0 : GD x0.1 ≠ 0 := by rw [← hGD']; exact hx0
    have hz := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.eq_zero_of_mul_eq_zero hO hC hGD hGq
      (fun y hy => by
        have := congrFun (congrFun hq' c) ⟨y, hy⟩
        simp only [Pi.mul_apply, Pi.zero_apply] at this
        rw [← hGD' ⟨y, hy⟩, ← hGq' ⟨y, hy⟩, mul_comm]
        exact this) x0.2 h0 x.1 x.2
    show ((p.coeff i : HA M) : C → M.dom → ℂ) c x = ((0 : HA M) : C → M.dom → ℂ) c x
    rw [hGq' x, hz]
    rfl
  refine mem_nonZeroDivisors_iff.2 ⟨fun x hx => key x ?_, key⟩
  rwa [mul_comm] at hx

end GlobalTheory.CuspEmb
end
end

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn GlobalTheory.CuspEmb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polynomialC_holInvariant_mem_nonZeroDivisors : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C] (M : TwoLevels E r U C) (D : HA M), (∀ c, ∃ x : M.dom, (D : C → M.dom → ℂ) c x ≠ 0) → Polynomial.C D ∈ nonZeroDivisors (Polynomial (HA M)) := by
  atlas_forward_decl GlobalTheory.CuspEmb.C_mem_nonZeroDivisors
end

section
section
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn GlobalTheory.CuspEmb

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CuspEmb

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {U C : Type} [Group U] [MulAction U C]

theorem pbA_comp (M : TwoLevels E r U C) (u v : U) (f : HA M) :
    pbA M v (pbA M u f) = pbA M (u * v) f := by
  apply Subtype.ext
  funext c x
  show f.1 (u • v • c) ⟨lact (M.tr u (v • c)) (lact (M.tr v c) x.1), _⟩ =
    f.1 ((u * v) • c) ⟨lact (M.tr (u * v) c) x.1, _⟩
  rw [show u • v • c = (u * v) • c from (mul_smul u v c).symm]
  have hγ := M.tr_mul u v c
  have hy : lact (M.tr u (v • c) * M.tr v c) x.1 ∈ M.dom := by
    rw [ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf.lact_mul]
    exact lact_tr_mem M u _ (lact_tr_mem M v c x.2)
  have e : lact (M.tr (u * v) c * (M.tr u (v • c) * M.tr v c)⁻¹) (lact (M.tr u (v • c) * M.tr v c) x.1) =
      lact (M.tr (u * v) c) x.1 := by
    rw [← ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf.lact_mul, inv_mul_cancel_right]
  have hz : lact (M.tr (u * v) c * (M.tr u (v • c) * M.tr v c)⁻¹)
      (⟨lact (M.tr u (v • c) * M.tr v c) x.1, hy⟩ : M.dom).1 ∈ M.dom := by
    show lact _ (lact _ x.1) ∈ M.dom
    rw [e]; exact lact_tr_mem M (u * v) c x.2
  have key := f.2.2 ((u * v) • c) _ hγ ⟨lact (M.tr u (v • c) * M.tr v c) x.1, hy⟩ hz
  rw [show (⟨lact (M.tr (u * v) c) x.1, lact_tr_mem M (u * v) c x.2⟩ : M.dom) =
      ⟨lact (M.tr (u * v) c * (M.tr u (v • c) * M.tr v c)⁻¹) (lact (M.tr u (v • c) * M.tr v c) x.1), hz⟩
      from Subtype.ext e.symm, key]
  exact congrArg (f.1 _) (Subtype.ext (ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf.lact_mul _ _ _).symm)

theorem pbA_one (M : TwoLevels E r U C) (f : HA M) : pbA M 1 f = f := by
  apply Subtype.ext
  funext c x
  show f.1 ((1 : U) • c) ⟨lact (M.tr 1 c) x.1, _⟩ = f.1 c x
  have hγ := M.tr_mul 1 1 c
  simp only [mul_one, one_smul] at hγ
  rw [mul_inv_rev, mul_inv_cancel_left] at hγ
  have hz : lact (M.tr 1 c)⁻¹ (lact (M.tr 1 c) x.1) ∈ M.dom := by
    rw [← ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf.lact_mul, inv_mul_cancel, ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf.lact_one]
    exact x.2
  have key := f.2.2 c _ hγ ⟨lact (M.tr 1 c) x.1, lact_tr_mem M 1 c x.2⟩ hz
  simp only [one_smul]
  rw [← key]
  refine congrArg (f.1 c) (Subtype.ext ?_)
  show lact (M.tr 1 c)⁻¹ (lact (M.tr 1 c) x.1) = x.1
  rw [← ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf.lact_mul, inv_mul_cancel, ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf.lact_one]

theorem tw_law (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C]
    (M : TwoLevels E r U C) (a : U → C → ℂˣ) (ha : ∀ (g h : U) (c : C), a (h * g) c = a g c * a h (g • c)) :
    tw M (fun c => (a 1 c : ℂ)) 1 = AlgHom.id ℂ _ ∧
      ∀ u v : U, (tw M (fun c => (a v c : ℂ)) v).comp (tw M (fun c => (a u c : ℂ)) u) =
        tw M (fun c => (a (u * v) c : ℂ)) (u * v) := by
  refine ⟨?_, fun u v => ?_⟩
  · apply AlgHom.coe_ringHom_injective
    apply Polynomial.ringHom_ext
    · intro f
      show tw M _ 1 (Polynomial.C f) = Polynomial.C f
      rw [tw_C, pbA_one]
    · show tw M _ 1 Polynomial.X = Polynomial.X
      rw [tw_X]
      have h1 : cst M (fun c => (a 1 c : ℂ)) = 1 := by
        apply Subtype.ext
        funext c x
        show (a 1 c : ℂ) = 1
        have h := ha 1 1 c
        rw [one_mul, one_smul] at h
        have h' : a 1 c = 1 := by
          have := congrArg (fun t => (a 1 c)⁻¹ * t) h
          simpa using this.symm
        rw [h', Units.val_one]
      rw [h1, map_one, one_mul]
  · apply AlgHom.coe_ringHom_injective
    apply Polynomial.ringHom_ext
    · intro f
      show tw M _ v (tw M _ u (Polynomial.C f)) = tw M _ (u * v) (Polynomial.C f)
      rw [tw_C, tw_C, tw_C, pbA_comp]
    · show tw M _ v (tw M _ u Polynomial.X) = tw M _ (u * v) Polynomial.X
      rw [tw_X, map_mul, tw_C, tw_X, tw_X, ← mul_assoc, ← Polynomial.C_mul]
      congr 2
      apply Subtype.ext
      funext c x
      show (a u (v • c) : ℂ) * (a v c : ℂ) = (a (u * v) c : ℂ)
      rw [ha v u c, Units.val_mul, mul_comm]

end GlobalTheory.CuspEmb

end
end

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn GlobalTheory.CuspEmb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedPullbackPolynomial_rightAction_of_cocycle : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C] (M : TwoLevels E r U C) (a : U → C → ℂˣ), (∀ (g h : U) (c : C), a (h * g) c = a g c * a h (g • c)) → tw M (fun c => (a 1 c : ℂ)) 1 = AlgHom.id ℂ _ ∧ ∀ u v : U, (tw M (fun c => (a v c : ℂ)) v).comp (tw M (fun c => (a u c : ℂ)) u) = tw M (fun c => (a (u * v) c : ℂ)) (u * v) := by
  atlas_forward_decl GlobalTheory.CuspEmb.tw_law
end

section
section
set_option autoImplicit false

noncomputable section

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

namespace GlobalTheory.CuspEmb

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {U C : Type} [Group U] [MulAction U C]

def deg1 (M : TwoLevels E r U C) (W : Submodule ℂ (C → M.dom → ℂ)) : Submodule ℂ (Polynomial (HA M)) :=
  (W.comap (HA M).val.toLinearMap).map ((Polynomial.monomial 1).restrictScalars ℂ)

theorem mem_homogeneousExponentsOneBlock (M : TwoLevels E r U C) (W : Submodule ℂ (C → M.dom → ℂ)) (p : Polynomial (HA M)) :
    p ∈ deg1 M W ↔ ∃ f : HA M, (f : C → M.dom → ℂ) ∈ W ∧ Polynomial.monomial 1 f = p := Iff.rfl

def deg1Equiv (M : TwoLevels E r U C) (W : Submodule ℂ (C → M.dom → ℂ)) (hW : ∀ f ∈ W, f ∈ HA M) :
    W ≃ₗ[ℂ] deg1 M W :=
  LinearEquiv.ofBijective
    ({ toFun := fun f => ⟨Polynomial.monomial 1 ⟨f, hW f f.2⟩, (mem_homogeneousExponentsOneBlock M W _).2 ⟨⟨f, hW f f.2⟩, f.2, rfl⟩⟩
       map_add' := fun f g => Subtype.ext (by
         show Polynomial.monomial 1 (⟨((f + g : W) : C → M.dom → ℂ), hW _ (f + g).2⟩ : HA M) =
           Polynomial.monomial 1 ⟨f, hW _ f.2⟩ + Polynomial.monomial 1 ⟨g, hW _ g.2⟩
         rw [← map_add]
         rfl)
       map_smul' := fun z f => Subtype.ext (by
         show Polynomial.monomial 1 (⟨((z • f : W) : C → M.dom → ℂ), hW _ (z • f).2⟩ : HA M) =
           z • Polynomial.monomial 1 ⟨f, hW _ f.2⟩
         rw [Polynomial.smul_monomial]
         rfl) } :
      W →ₗ[ℂ] deg1 M W)
    ⟨fun f g hfg => by
      have := congrArg Subtype.val hfg
      have := Polynomial.monomial_injective 1 this
      exact Subtype.ext (congrArg (fun q : HA M => (q : C → M.dom → ℂ)) this),
     fun p => by
      obtain ⟨f, hf, hp⟩ := (mem_homogeneousExponentsOneBlock M W p.1).1 p.2
      exact ⟨⟨f, hf⟩, Subtype.ext hp⟩⟩

theorem deg1Equiv_coe (M : TwoLevels E r U C) (W : Submodule ℂ (C → M.dom → ℂ)) (hW : ∀ f ∈ W, f ∈ HA M) (f : W) :
    ((deg1Equiv M W hW f : deg1 M W) : Polynomial (HA M)) = Polynomial.monomial 1 ⟨f, hW f f.2⟩ := rfl

theorem mul_pb_mem_cusp (M : TwoLevels E r U C) (ka mu : Wt M.Ψ r) (u0 : C → Frame M.Ψ r → ℂ) (hu0 : u0 ∈ M.SS mu)
    (k h : U) {f : C → M.dom → ℂ} (hf : f ∈ M.cusp ka) :
    f * pb M k (M.res u0) * pb M h (M.res u0) ∈ M.cusp (ka + 2 • mu) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨F, hF, rfl⟩ := hf
    have e : M.res F * pb M k (M.res u0) * pb M h (M.res u0) = M.res (F * M.pull k u0 * M.pull h u0) := rfl
    rw [e, two_smul, ← add_assoc]
    exact Submodule.subset_span ⟨_, GlobalTheory.T.twoLevelCuspForms_mul_mem_add_weight E r U C M _ _ _ _ (GlobalTheory.T.twoLevelCuspForms_mul_mem_add_weight E r U C M _ _ _ _ hF
      (GlobalTheory.T.twoLevelCuspForms_pull_mem E r U C M mu u0 k hu0)) (GlobalTheory.T.twoLevelCuspForms_pull_mem E r U C M mu u0 h hu0), rfl⟩
  | zero => simp
  | add f g _ _ hf hg => rw [add_mul, add_mul]; exact add_mem hf hg
  | smul z f _ hf => rw [smul_mul_assoc, smul_mul_assoc]; exact Submodule.smul_mem _ z hf

end GlobalTheory.CuspEmb

open GlobalTheory.CuspEmb in

theorem GlobalTheory.CuspEmb.cusp_embReg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [Finite U]
    [Finite C] [MulAction U C] (M : TwoLevels E r U C), ∀ (ka : Wt M.Ψ r) (ρ : Representation ℂ U (M.cusp ka)),
    IsPullRep M ka ρ → ∀ ep c : ℝ, Ranks M ka (sOf M) ep c → ∀ H : Subgroup U, LevelHyp (sub M H) →
    ∃ n : ℕ, GlobalTheory.BadCount.EmbReg ρ H n ∧ n * Nat.card H ≤ finrank ℂ (M.cusp (ka + 2 • deMul M.Ψ r M.p0 (sOf M))) := by
  intro E _ _ _ r U C _ _ _ _ M ka ρ hρ ep c0 hR H hL
  classical
  haveI : Fintype U := Fintype.ofFinite U
  obtain ⟨u0, hu0, hdet⟩ := GlobalTheory.T.exists_cuspForm_independent_translates E r H C (sub M H) hL (sOf M) (even_sOf M) (le_sOf M)
  have hu0' : u0 ∈ M.SS (deMul M.Ψ r M.p0 (sOf M)) := hu0
  have hVHA : ∀ f ∈ M.cusp ka, f ∈ HA M := fun f hf => by
    refine (Submodule.span_le (p := Subalgebra.toSubmodule (HA M))).2 ?_ hf
    rintro _ ⟨F, hF, rfl⟩
    exact GlobalTheory.T.twoLevelCuspForms_restrict_holInvariant E r U C M ka F hF
  have h2HA : ∀ f ∈ M.cusp (ka + 2 • deMul M.Ψ r M.p0 (sOf M)), f ∈ HA M := fun f hf => by
    refine (Submodule.span_le (p := Subalgebra.toSubmodule (HA M))).2 ?_ hf
    rintro _ ⟨F, hF, rfl⟩
    exact GlobalTheory.T.twoLevelCuspForms_restrict_holInvariant E r U C M _ F hF
  obtain ⟨a, hcoc, hform⟩ := GlobalTheory.T.exists_cocycle_pullbackRepresentation E r U C M ka ρ hρ (fun f hf => (hVHA f hf).2)
  obtain ⟨h1, hlaw⟩ := GlobalTheory.T.twistedPullbackPolynomial_rightAction_of_cocycle E r U C M a hcoc
  let act : U →* (Polynomial (HA M) →ₐ[ℂ] Polynomial (HA M)) :=
    { toFun := fun k => tw M (fun c => (a k⁻¹ c : ℂ)) k⁻¹
      map_one' := by
        show tw M (fun c => (a 1⁻¹ c : ℂ)) 1⁻¹ = 1
        rw [inv_one]
        exact h1
      map_mul' := fun g h => by
        simp only [mul_inv_rev]
        rw [← hlaw]
        rfl }
  let ut : HA M := ⟨M.res u0, GlobalTheory.T.twoLevelCuspForms_restrict_holInvariant E r U C M _ u0 hu0'⟩
  have hact : ∀ k, act k (Polynomial.C ut) = Polynomial.C (pbA M k⁻¹ ut) := fun k => tw_C M _ _ _
  have hactm : ∀ k (f : HA M), act k (Polynomial.monomial 1 f) =
      Polynomial.monomial 1 (cst M (fun c => (a k⁻¹ c : ℂ)) * pbA M k⁻¹ f) := fun k f => tw_monomial_one M _ _ _

  have hnz : (Matrix.of fun h g : H => act ((h : U) * g) (Polynomial.C ut)).det ∈ nonZeroDivisors (Polynomial (HA M)) := by
    have e : (Matrix.of fun h g : H => act ((h : U) * g) (Polynomial.C ut)) =
        (Polynomial.C : HA M →+* Polynomial (HA M)).mapMatrix (Matrix.of fun h g : H => pbA M ((h : U) * g)⁻¹ ut) := by
      refine Matrix.ext fun h g => ?_
      simp only [Matrix.of_apply, RingHom.mapMatrix_apply, Matrix.map_apply, hact, mul_inv_rev]
    rw [e, ← RingHom.map_det]
    refine GlobalTheory.T.polynomialC_holInvariant_mem_nonZeroDivisors E r U C M _ fun c => ?_
    obtain ⟨x, hx, hne⟩ := hdet c
    refine ⟨⟨x, hx⟩, ?_⟩
    let φ : HA M →+* ℂ := ((Pi.evalRingHom _ (⟨x, hx⟩ : M.dom)).comp (Pi.evalRingHom _ c)).comp (HA M).val.toRingHom
    have e2 : ((Matrix.of fun h g : H => pbA M ((h : U) * g)⁻¹ ut).det : C → M.dom → ℂ) c ⟨x, hx⟩ =
        φ (Matrix.of fun h g : H => pbA M ((h : U) * g)⁻¹ ut).det := rfl
    rw [e2, RingHom.map_det]
    have e3 : φ.mapMatrix (Matrix.of fun h g : H => pbA M ((h : U) * g)⁻¹ ut) =
        ((Matrix.of fun h h' : H => M.pull ((h : U) * h') u0 c x).submatrix (Equiv.inv H) (Equiv.inv H)).transpose := by
      ext h g
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.transpose_apply, Matrix.submatrix_apply,
        Equiv.inv_apply, mul_inv_rev]
      rfl
    rw [e3, Matrix.det_transpose, Matrix.det_submatrix_equiv_self]
    exact hne

  let V := deg1 M (M.cusp ka)
  let V2 := deg1 M (M.cusp (ka + 2 • deMul M.Ψ r M.p0 (sOf M)))
  let V1 : Submodule ℂ (Polynomial (HA M)) :=
    Submodule.span ℂ {p | ∃ x ∈ V, ∃ h : H, p = x * act h (Polynomial.C ut)}
  let e := deg1Equiv M (M.cusp ka) hVHA
  let e2 := deg1Equiv M _ h2HA
  haveI : Module.Finite ℂ (M.cusp (ka + 2 • deMul M.Ψ r M.p0 (sOf M))) := hR.2.1
  haveI : FiniteDimensional ℂ V2 := LinearEquiv.finiteDimensional e2
  let ρ' : Representation ℂ U V :=
    { toFun := fun k => e.toLinearMap ∘ₗ ρ k ∘ₗ e.symm.toLinearMap
      map_one' := by ext; simp
      map_mul' := fun g h => by ext; simp }
  have hρ' : ∀ g x, ((ρ' g x : V) : Polynomial (HA M)) = act g x := by
    intro g x
    obtain ⟨f, rfl⟩ := e.surjective x
    have e1 : ρ' g (e f) = e (ρ g f) := by simp [ρ']
    rw [e1, deg1Equiv_coe, deg1Equiv_coe, hactm]
    congr 1
    apply Subtype.ext
    funext c x
    have := hform g⁻¹ f c x
    rw [inv_inv] at this
    exact this
  have hV1 : ∀ h : H, ∀ x ∈ V, x * act h (Polynomial.C ut) ∈ V1 := fun h x hx => Submodule.subset_span ⟨x, hx, h, rfl⟩
  have hactV : ∀ (k : U), ∀ x ∈ V, act k x ∈ V := fun k x hx => by
    have := hρ' k ⟨x, hx⟩
    rw [← this]
    exact (ρ' k ⟨x, hx⟩).2
  have hV1s : ∀ h : H, ∀ x ∈ V1, act h x ∈ V1 := by
    intro h x hx
    induction hx using Submodule.span_induction with
    | mem p hp =>
      obtain ⟨y, hy, k, rfl⟩ := hp
      refine Submodule.subset_span ⟨act h y, hactV h y hy, h * k, ?_⟩
      rw [map_mul, Subgroup.coe_mul, map_mul act]
      rfl
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul z x _ hx => rw [map_smul]; exact Submodule.smul_mem _ z hx
  have hV2 : ∀ h : H, ∀ x ∈ V1, x * act h (Polynomial.C ut) ∈ V2 := by
    intro h x hx
    induction hx using Submodule.span_induction with
    | mem p hp =>
      obtain ⟨y, hy, k, rfl⟩ := hp
      obtain ⟨f, hf, rfl⟩ := (mem_homogeneousExponentsOneBlock M _ y).1 hy
      rw [hact, hact, Polynomial.monomial_mul_C, Polynomial.monomial_mul_C]
      refine (mem_homogeneousExponentsOneBlock M _ _).2 ⟨_, ?_, rfl⟩
      exact mul_pb_mem_cusp M ka _ u0 hu0' _ _ hf
    | zero => simp
    | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
    | smul z x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ z hx
  obtain ⟨n, ⟨j, hj, hjeq⟩, hn⟩ := GlobalTheory.T.embedsInRegularRepresentationCopies_of_groupDeterminant ℂ U (Polynomial (HA M)) act H (Polynomial.C ut) hnz V V1 V2 ρ' hρ' hV1
    hV1s hV2
  refine ⟨n, ⟨j ∘ₗ e.toLinearMap, hj.comp e.injective, fun h v i => ?_⟩, ?_⟩
  · have := hjeq h (e v) i
    have e1 : ρ' h (e v) = e (ρ h v) := by simp [ρ']
    rw [e1] at this
    exact this
  · rw [← e2.finrank_eq] at hn
    exact hn

end
end

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twoLevelCuspForms_embed_regularRepresentation_copies : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [Finite U] [Finite C] [MulAction U C] (M : TwoLevels E r U C), ∀ (ka : Wt M.Ψ r) (ρ : Representation ℂ U (M.cusp ka)), IsPullRep M ka ρ → ∀ ep c : ℝ, Ranks M ka (sOf M) ep c → ∀ H : Subgroup U, LevelHyp (sub M H) → ∃ n : ℕ, GlobalTheory.BadCount.EmbReg ρ H n ∧ n * Nat.card H ≤ finrank ℂ (M.cusp (ka + 2 • deMul M.Ψ r M.p0 (sOf M))) := by
  atlas_forward_decl GlobalTheory.CuspEmb.cusp_embReg
end

section
section
open Module

namespace GlobalTheory.BadCount

theorem finrank_iInf_ker_semilinear : ∀ (K V ι : Type) [Field K] [AddCommGroup V] [Module ℂ V]
    [Finite ι] (σ : K →+* ℂ) (N : ℕ) (f : (Fin N → K) →ₛₗ[σ] V),
    (LinearIndependent ℂ fun k => f (Pi.single k 1)) → Submodule.span ℂ (Set.range f) = ⊤ →
    ∀ (a : ι → (Fin N → K) →ₗ[K] (Fin N → K)) (a' : ι → V →ₗ[ℂ] V),
      (∀ i v, a' i (f v) = f (a i v)) →
      finrank ℂ (⨅ i, LinearMap.ker (a' i) : Submodule ℂ V) =
        finrank K (⨅ i, LinearMap.ker (a i) : Submodule K (Fin N → K)) := by
  intro K V ι _ _ _ _ σ N f hli hsp a a' ha
  letI : Algebra K ℂ := σ.toAlgebra
  letI : Module K V := Module.compHom V σ
  haveI : IsScalarTower K ℂ V := ⟨fun k c v => by
    show (σ k * c) • v = σ k • c • v
    rw [mul_smul]⟩
  let g : (Fin N → K) →ₗ[K] V :=
    { toFun := f, map_add' := f.map_add, map_smul' := fun k x => f.map_smulₛₗ k x }
  have hsp' : Submodule.span ℂ (Set.range fun k => f (Pi.single k 1)) = ⊤ := by
    rw [eq_top_iff, ← hsp, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    rw [← (Pi.basisFun K (Fin N)).sum_repr x, map_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [f.map_smulₛₗ, Pi.basisFun_apply]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  let c : Basis (Fin N) ℂ V := Basis.mk hli hsp'.ge
  have hc : ∀ k, c k = f (Pi.single k 1) := fun k => Basis.mk_apply _ _ _
  let e := (Algebra.TensorProduct.basis ℂ (Pi.basisFun K (Fin N))).equiv c (Equiv.refl _)
  have hbc : IsBaseChange ℂ g := by
    refine IsBaseChange.of_equiv e fun m => ?_
    have h : (e.toLinearMap.restrictScalars K ∘ₗ TensorProduct.mk K ℂ (Fin N → K) 1) = g := by
      refine (Pi.basisFun K (Fin N)).ext fun k => ?_
      have := (Algebra.TensorProduct.basis ℂ (Pi.basisFun K (Fin N))).equiv_apply k c (Equiv.refl _)
      rw [Algebra.TensorProduct.basis_apply] at this
      simp only [LinearMap.coe_comp, Function.comp_apply, TensorProduct.mk_apply,
        LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
      rw [this, Equiv.refl_apply, hc, Pi.basisFun_apply]
      rfl
    exact congrArg (fun φ => φ m) h
  exact (finrank_iInf_ker_baseChange K ℂ (Fin N → K) V ι g hbc a a' ha).1

end GlobalTheory.BadCount
end

open Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_iInf_ker_semilinear_standardBasis : ∀ (K V ι : Type) [Field K] [AddCommGroup V] [Module ℂ V] [Finite ι] (σ : K →+* ℂ) (N : ℕ) (f : (Fin N → K) →ₛₗ[σ] V), (LinearIndependent ℂ fun k => f (Pi.single k 1)) → Submodule.span ℂ (Set.range f) = ⊤ → ∀ (a : ι → (Fin N → K) →ₗ[K] (Fin N → K)) (a' : ι → V →ₗ[ℂ] V), (∀ i v, a' i (f v) = f (a i v)) → finrank ℂ (⨅ i, LinearMap.ker (a' i) : Submodule ℂ V) = finrank K (⨅ i, LinearMap.ker (a i) : Submodule K (Fin N → K)) := by
  atlas_forward_decl GlobalTheory.BadCount.finrank_iInf_ker_semilinear
end

section
section
open Module NumberField

namespace GlobalTheory.BadCount

theorem semilin_eq_sum {K V : Type} [Field K] [AddCommGroup V] [Module ℂ V] {N : ℕ} {σ : K →+* ℂ}
    (f : (Fin N → K) →ₛₗ[σ] V) (x : Fin N → K) : f x = ∑ k, σ (x k) • f (Pi.single k 1) := by
  conv_lhs => rw [pi_eq_sum_univ' x]
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smulₛₗ]

theorem top_le_span_single {K V : Type} [Field K] [AddCommGroup V] [Module ℂ V] {N : ℕ} {σ : K →+* ℂ}
    (f : (Fin N → K) →ₛₗ[σ] V) (h : Submodule.span ℂ (Set.range f) = ⊤) :
    ⊤ ≤ Submodule.span ℂ (Set.range fun k => f (Pi.single k 1)) := by
  rw [← h, Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  rw [semilin_eq_sum f x]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

theorem embReg_of_semilinear {V V' G : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    [Group G] (ρ : Representation ℂ G V) (ρ' : Representation ℂ G V') (τ : ℂ ≃+* ℂ) (T : V' →+ V)
    (hs : ∀ (c : ℂ) v, T (c • v) = τ.symm c • T v) (hi : Function.Injective T)
    (he : ∀ g v, T (ρ' g v) = ρ g (T v)) (H : Subgroup G) (n : ℕ) (h : EmbReg ρ H n) : EmbReg ρ' H n := by
  obtain ⟨j, hj, hje⟩ := h
  let m : MonoidAlgebra ℂ H →+* MonoidAlgebra ℂ H := MonoidAlgebra.mapRingHom H (τ : ℂ →+* ℂ)
  have hm : ∀ x a, (m x).coeff a = τ (x.coeff a) := fun x a => MonoidAlgebra.coeff_mapRingHom _ _ _
  have hmi : Function.Injective m := by
    intro x y hxy
    ext a
    apply τ.injective
    rw [← hm, ← hm, hxy]
  refine ⟨{ toFun := fun v i => m (j (T v) i)
            map_add' := fun v w => ?_
            map_smul' := fun c v => ?_ }, fun v w hvw => ?_, fun g v i => ?_⟩
  · funext i
    simp
  · funext i
    ext a
    simp [hs, hm]
  · exact hi (hj (funext fun i => hmi (congrFun hvw i)))
  · show m (j (T (ρ' g v)) i) = _ * m (j (T v) i)
    rw [he, hje, map_mul]
    congr 1
    exact (MonoidAlgebra.mapRingHom_single _ _ _).trans (by rw [map_one])

theorem embReg_of_baseChange : ∀ (K V V' G : Type) [Field K] [NumberField K] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V'] [Module ℂ V'] [Group G] [Finite G] (N : ℕ) (ρK : Representation K G (Fin N → K))
    (σ σ' : K →+* ℂ) (ρ : Representation ℂ G V) (ρ' : Representation ℂ G V') (f : (Fin N → K) →ₛₗ[σ] V)
    (f' : (Fin N → K) →ₛₗ[σ'] V'), (LinearIndependent ℂ fun k => f (Pi.single k 1)) →
    Submodule.span ℂ (Set.range f) = ⊤ → (LinearIndependent ℂ fun k => f' (Pi.single k 1)) →
    Submodule.span ℂ (Set.range f') = ⊤ → (∀ g v, ρ g (f v) = f (ρK g v)) →
    (∀ g v, ρ' g (f' v) = f' (ρK g v)) → ∀ (H : Subgroup G) (n : ℕ),
    GlobalTheory.BadCount.EmbReg ρ H n → GlobalTheory.BadCount.EmbReg ρ' H n := by
  intro K V V' G _ _ _ _ _ _ _ _ N ρK σ σ' ρ ρ' f f' hl _ hl' hsp' he he' H n h
  haveI : Countable K := (Module.finBasis ℚ K).equivFun.injective.countable
  obtain ⟨τ, hτ⟩ := GlobalTheory.CompRat.exists_ringEquiv_complex_comp_eq K σ σ'
  let b' : Basis (Fin N) ℂ V' := Basis.mk hl' (top_le_span_single f' hsp')
  have hb' : ∀ k, b' k = f' (Pi.single k 1) := fun k => Basis.mk_apply _ _ k
  let T : V' →+ V :=
    { toFun := fun v => ∑ k, τ.symm (b'.repr v k) • f (Pi.single k 1)
      map_zero' := by simp
      map_add' := fun v w => by simp [add_smul, Finset.sum_add_distrib] }
  have hT : ∀ v, T v = ∑ k, τ.symm (b'.repr v k) • f (Pi.single k 1) := fun _ => rfl
  have hs : ∀ (c : ℂ) v, T (c • v) = τ.symm c • T v := fun c v => by
    simp [hT, Finset.smul_sum, mul_smul]
  have hTf : ∀ x, T (f' x) = f x := fun x => by
    have hr : ∀ k, b'.repr (f' x) k = σ' (x k) := fun k => by
      rw [semilin_eq_sum f' x]
      simp only [← hb']
      exact congrFun (b'.repr_sum_self _) k
    rw [hT, semilin_eq_sum f x]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hr, ← hτ, RingEquiv.symm_apply_apply]
  refine embReg_of_semilinear ρ ρ' τ T hs ?_ (fun g v => ?_) H n h
  · rw [injective_iff_map_eq_zero]
    intro v hv
    rw [hT] at hv
    have h0 := Fintype.linearIndependent_iff.1 hl _ hv
    apply b'.repr.injective
    ext k
    simpa using h0 k
  · have hv : v ∈ Submodule.span ℂ (Set.range f') := hsp' ▸ Submodule.mem_top
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨x, rfl⟩ := hx
      rw [he', hTf, hTf, he]
    | zero => simp
    | add x y _ _ hx hy => simp only [map_add, hx, hy]
    | smul c x _ hx => rw [map_smul, hs, hs, map_smul, hx]

end GlobalTheory.BadCount
end

open Module NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.embedsInRegularRepresentationCopies_complexEmbedding_indep : ∀ (K V V' G : Type) [Field K] [NumberField K] [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] [Group G] [Finite G] (N : ℕ) (ρK : Representation K G (Fin N → K)) (σ σ' : K →+* ℂ) (ρ : Representation ℂ G V) (ρ' : Representation ℂ G V') (f : (Fin N → K) →ₛₗ[σ] V) (f' : (Fin N → K) →ₛₗ[σ'] V'), (LinearIndependent ℂ fun k => f (Pi.single k 1)) → Submodule.span ℂ (Set.range f) = ⊤ → (LinearIndependent ℂ fun k => f' (Pi.single k 1)) → Submodule.span ℂ (Set.range f') = ⊤ → (∀ g v, ρ g (f v) = f (ρK g v)) → (∀ g v, ρ' g (f' v) = f' (ρK g v)) → ∀ (H : Subgroup G) (n : ℕ), GlobalTheory.BadCount.EmbReg ρ H n → GlobalTheory.BadCount.EmbReg ρ' H n := by
  atlas_forward_decl GlobalTheory.BadCount.embReg_of_baseChange
end

section
section
namespace GlobalTheory.HodgeMultNum

theorem nat_bound (r f T : ℕ) (hr : 100 ≤ r) (hf : 5 ≤ f) (hT : 11 * (f * r.choose 2) ^ 2 ≤ T) :
    2 * r + 50 * r ^ 2 * (f * (r * r / 4)) + 2 ≤ T := by
  have hq : 4 * (r * r / 4) ≤ r * r := Nat.mul_div_le (r * r) 4
  have hc : 2 * r.choose 2 = r * (r - 1) := by
    rw [Nat.choose_two_right]; exact Nat.mul_div_cancel' (Nat.even_mul_pred_self r).two_dvd
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 100 := ⟨r - 100, by omega⟩
  have h1 : s + 100 - 1 = s + 99 := by omega
  rw [h1] at hc
  set q := (s + 100) * (s + 100) / 4
  set c := (s + 100).choose 2
  have key : 4 * (2 * (s + 100) + 50 * (s + 100) ^ 2 * (f * q) + 2) ≤ 4 * (11 * (f * c) ^ 2) := by
    have e1 : 4 * (11 * (f * c) ^ 2) = 11 * f ^ 2 * ((s + 100) * (s + 99)) ^ 2 := by rw [← hc]; ring
    rw [e1]
    have e2 : 4 * (2 * (s + 100) + 50 * (s + 100) ^ 2 * (f * q) + 2) = 8 * (s + 100) + 8 + 50 * (s+100)^2 * f * (4 * q) := by ring
    rw [e2]
    have h3 : 50 * (s+100)^2 * f * (4 * q) ≤ 50 * (s+100)^2 * f * ((s+100)*(s+100)) := Nat.mul_le_mul_left _ hq
    have h4 : 8 * (s + 100) + 8 + 50 * (s+100)^2 * f * ((s+100)*(s+100)) ≤ 11 * f ^ 2 * ((s + 100) * (s + 99)) ^ 2 := by
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 5 := ⟨f - 5, by omega⟩
      ring_nf
      nlinarith [Nat.zero_le (s * g), Nat.zero_le (s * g ^ 2), Nat.zero_le (s ^ 2 * g), Nat.zero_le (s ^ 2 * g ^ 2),
        Nat.zero_le (s ^ 3 * g), Nat.zero_le (s ^ 3 * g ^ 2), Nat.zero_le (s ^ 4 * g), Nat.zero_le (s ^ 4 * g ^ 2),
        Nat.zero_le (s ^ 2), Nat.zero_le (s ^ 3), Nat.zero_le (s ^ 4), Nat.zero_le (g ^ 2)]
    omega
  omega

theorem five_le_of_pow (r f : ℕ) (hr : 100 ≤ r) (h : (r : ℝ) / 2 * (7 / 8 : ℝ) ^ f ≤ 1 / 16) : 5 ≤ f := by
  by_contra hf
  push_neg at hf
  have h1 : (7 / 8 : ℝ) ^ 4 ≤ (7 / 8 : ℝ) ^ f := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have h2 : (100 : ℝ) ≤ r := by exact_mod_cast hr
  nlinarith [pow_pos (show (0:ℝ) < 7/8 by norm_num) f]

end GlobalTheory.HodgeMultNum

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigOn

theorem GlobalTheory.HodgeMultNum.hodgeMult_le_TO : Closed FamHyp fun Fm _ => ∃ x0 : ℝ, ∀ (x : ℝ) (hx : Fm.x1 < x), x0 ≤ x →
    ∀ ι : Fm.Ix x, 2 * (Fm.D x ι).R.r + 50 * (Fm.D x ι).R.r ^ 2 * ((Fm.D x ι).R.f * ((Fm.D x ι).R.r * (Fm.D x ι).R.r / 4)) + 2 ≤
      (Fm.parT x hx ι).TO := by
  refine Closed.imp GlobalTheory.T.badShareSize_bounds_along_family fun Fm _ _ H => ?_
  obtain ⟨x0, H⟩ := H
  refine ⟨x0, fun x hx h0 ι => ?_⟩
  obtain ⟨hr, -, hE, hk⟩ := H x hx h0 ι
  obtain ⟨hg, hsum⟩ := hk 0
  set D := Fm.D x ι
  set g : ℝ := (D.host.g 0 : ℝ)
  have hg1 : (4096 : ℝ) ≤ g := by simp only [g]; exact_mod_cast hg
  have hlogg : 0 ≤ Real.log g := Real.log_nonneg (by linarith)
  have hr' : (100 : ℝ) ≤ (D.R.r : ℝ) := by exact_mod_cast hr
  have hlogr : 0 ≤ Real.log (D.R.r : ℝ) := Real.log_nonneg (by linarith)
  have hfpos : (0 : ℝ) ≤ (D.R.f : ℝ) := Nat.cast_nonneg _
  have hmpos : (0 : ℝ) ≤ (D.R.m : ℝ) := Nat.cast_nonneg _
  have hA : 0 ≤ 3 * (D.R.f : ℝ) / g := by positivity
  have hB : 0 ≤ 23 * (D.R.f : ℝ) * Real.log g / Real.sqrt g := by positivity
  have hC : 0 ≤ 2 * (D.R.f : ℝ) * (D.R.m : ℝ) * (1 / (4 * ((min D.host.q D.host.d : ℕ) : ℝ)) +
      (1 + Real.log (D.R.r : ℝ)) / (g - 1)) := by
    have : 0 ≤ g - 1 := by linarith
    positivity
  have hE' : 0 ≤ Real.exp (-(D.R.f : ℝ) / (5 * Real.log (D.R.r : ℝ))) := (Real.exp_pos _).le
  have hP : (D.R.r : ℝ) / 2 * (7 / 8 : ℝ) ^ D.R.f ≤ 1 / 16 := by linarith
  have hf := GlobalTheory.HodgeMultNum.five_le_of_pow _ _ hr hP
  have hT := (Fm.parT x hx ι).TO_11D2
  rw [(Fm.parT x hx ι).Dp_eq] at hT
  exact GlobalTheory.HodgeMultNum.nat_bound _ _ _ hr hf hT
end

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeLineMultiple_le_familyThreshold : Closed FamHyp fun Fm _ => ∃ x0 : ℝ, ∀ (x : ℝ) (hx : Fm.x1 < x), x0 ≤ x → ∀ ι : Fm.Ix x, 2 * (Fm.D x ι).R.r + 50 * (Fm.D x ι).R.r ^ 2 * ((Fm.D x ι).R.f * ((Fm.D x ι).R.r * (Fm.D x ι).R.r / 4)) + 2 ≤ (Fm.parT x hx ι).TO := by
  atlas_forward_decl GlobalTheory.HodgeMultNum.hodgeMult_le_TO
end

section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.ShareOn Formalism.MainNotions.ArithmeticCylinders

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BadWOn

open Module GlobalTheory.BadCount GlobalTheory.TwistedRepresentationEmbedding GlobalTheory.CovTop ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds

theorem model_bound {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {U C : Type} [Group U] [Finite U]
    [Finite C] [MulAction U C] (M : TwoLevels E r U C) (ka : Wt M.Ψ r) (ρ : Representation ℂ U (M.cusp ka)) (T : ℕ)
    (hρ : IsPullRep M ka ρ)
    (hc : (M.p0 = 0 ∨ M.p0 = r) ∨ (0 < M.p0 ∧ M.p0 < r ∧ GlobalTheory.ShareOn.ArchOn M ka T ∧ GlobalTheory.ShareOn.sOf M ≤ T ∧
      LevelHyp (GlobalTheory.ShareOn.sub M ⊥)))
    (H P : Subgroup U) (hH : LevelHyp (GlobalTheory.ShareOn.sub M H)) (hP : LevelHyp (GlobalTheory.ShareOn.sub M P)) (lam : P →* ℂˣ) :
    ∃ n : ℕ, EmbReg ρ H n ∧ (n : ℝ) * Nat.card H ≤ 2 * Nat.card P * finrank ℂ (eig ρ P lam) := by
  rcases hc with hdef | ⟨h0, hr, hA, hs, hbot⟩
  · obtain ⟨-, hrest⟩ := GlobalTheory.T.definite_cuspForms_finite_regularRepresentation E r U C M hdef ka ρ hρ
    obtain ⟨⟨n, hn, hnc⟩, -⟩ := hrest H hH
    have hP2 := (hrest P hP).2 lam
    refine ⟨n, hn, ?_⟩
    have e : (n : ℝ) * Nat.card H = Nat.card P * finrank ℂ (eig ρ P lam) := by exact_mod_cast (hnc.trans hP2.symm)
    rw [e]
    have : (0 : ℝ) ≤ Nat.card P * finrank ℂ (eig ρ P lam) := by positivity
    linarith
  · have hR := GlobalTheory.T.twoLevelFlagDomain_cuspForm_ranks_shifted_weights E r U C M hbot h0 hr ka T hA hs
    obtain ⟨n, hn, hb⟩ := GlobalTheory.T.twoLevelCuspForms_embed_regularRepresentation_copies E r U C M ka ρ hρ _ _ hR H hH
    have hS := (GlobalTheory.T.twoLevelFlagDomain_eigenspace_share E r U C M ka ρ hρ _ _ hR P hP lam).1
    refine ⟨n, hn, ?_⟩
    have h4 := hR.2.2.2.1
    have hb' : (n : ℝ) * Nat.card H ≤ finrank ℂ (M.cusp (ka + 2 • deMul M.Ψ r M.p0 (GlobalTheory.ShareOn.sOf M))) := by
      exact_mod_cast hb
    have hS' : (finrank ℂ (M.cusp (ka - deMul M.Ψ r M.p0 (GlobalTheory.ShareOn.sOf M))) : ℝ) ≤
        Nat.card P * finrank ℂ (eig ρ P lam) := by exact_mod_cast hS
    calc (n : ℝ) * Nat.card H ≤ _ := hb'
      _ ≤ 2 * finrank ℂ (M.cusp (ka - deMul M.Ψ r M.p0 (GlobalTheory.ShareOn.sOf M))) := h4
      _ ≤ 2 * (Nat.card P * finrank ℂ (eig ρ P lam)) := by linarith
      _ = 2 * Nat.card P * finrank ℂ (eig ρ P lam) := by ring

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

set_option maxHeartbeats 1000000 in

theorem point (p : PtAt ex Csz) (i : Fin D.R.m) (T : ℕ) (del : ℝ) (hGr : GlobalTheory.GLq.Green) (hRows : p.Rows)
    (hRec : RecTies p) (hmod : ModelAt p i T) (hr : 100 ≤ D.R.r) (hA : TieAdmG D)
    (hg : ∀ k : Fin 2, 2 ^ 12 ≤ D.host.g k ∧ 4 * (3 * (D.R.f : ℝ) / (D.host.g k : ℝ) + 23 * (D.R.f : ℝ) *
      Real.log (D.host.g k : ℝ) / Real.sqrt (D.host.g k : ℝ) + 2 * (D.R.f : ℝ) * (D.R.m : ℝ) *
      (1 / (4 * ((min D.host.q D.host.d : ℕ) : ℝ)) + (1 + Real.log (D.R.r : ℝ)) / ((D.host.g k : ℝ) - 1)) +
      (D.R.r : ℝ) / 2 * (7 / 8 : ℝ) ^ D.R.f + Real.exp (-(D.R.f : ℝ) / (5 * Real.log (D.R.r : ℝ)))) ≤ del)
    (hsT : 2 * D.R.r + 50 * D.R.r ^ 2 * (D.R.f * (D.R.r * D.R.r / 4)) + 2 ≤ T) : BadW p i del := by

  classical
  obtain ⟨C, hCf, hact, M, ka, ρ, σ, f, hpull, hequiv, hli, hspan, hlev, hcard, hcase⟩ := hmod
  obtain ⟨lam, ψ, hW, hlam, hhalf⟩ := GlobalTheory.T.exists_whittaker_character_pair D L hT Gi Gl Kc Y cX ex Csz p hRows
  obtain ⟨-, hHex⟩ := GlobalTheory.T.exists_whittakerDatum_and_halfLevels D ψ hW.1
  choose Hh hHh using hHex
  let e : p.P.Gp ≃* G0g D.nd := p.R.eG.trans p.cG
  let π : p.P.Gp →* G0g D.nd := e.toMonoidHom
  let ιs : G0g D.nd →* p.P.Gp := e.symm.toMonoidHom
  let P : Subgroup (G0g D.nd) := p.P.P0.map π
  let P' : Subgroup p.P.Gp := P.comap π
  have hle : P' ≤ p.P.P0 := fun g hg => (Subgroup.mem_map_iff_mem e.injective).1 hg
  have hge : p.P.P0 ≤ P' := fun g hg => (Subgroup.mem_map_iff_mem e.injective).2 hg

  have hbot : LevelHyp (GlobalTheory.ShareOn.sub M ⊥) := hlev ⊥ ⟨0, fun g hg v => by
    rw [Subgroup.mem_bot] at hg
    subst hg
    intro a b
    simp only [map_one]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · exact Matrix.one_apply_ne (ne_of_gt h)
    · subst h; exact Matrix.one_apply_eq a⟩
  have hP'lev : LevelHyp (GlobalTheory.ShareOn.sub M P') := by
    obtain ⟨k, hk⟩ := hhalf
    exact hlev P' ⟨k, fun g hg v => hk g (hle hg) v⟩
  have hHlev : ∀ k, LevelHyp (GlobalTheory.ShareOn.sub M ((Hh k).comap π)) := fun k => hlev _ ⟨k + 1, fun g hg v =>
    ((hHh k (π g)).1 hg) ⟨k + 1, v⟩ (by simp)⟩

  have hsOf : GlobalTheory.ShareOn.sOf M ≤ T := by
    have key : ∀ a b : ℕ, a * (b - a) * 4 ≤ b * b := by
      intro a b
      rcases le_total a b with h | h
      · obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le h
        rw [Nat.add_sub_cancel_left]
        nlinarith [sq_nonneg ((a : ℤ) - q)]
      · rw [Nat.sub_eq_zero_of_le h]; simp
    have hq : M.p0 * (D.R.r - M.p0) ≤ D.R.r * D.R.r / 4 := (Nat.le_div_iff_mul_le (by norm_num)).2 (key _ _)
    have hX : M.dimX ≤ D.R.f * (D.R.r * D.R.r / 4) := by
      unfold TwoLevels.dimX; rw [hcard]; exact Nat.mul_le_mul_left _ hq
    unfold GlobalTheory.ShareOn.sOf
    have := Nat.mul_le_mul_left (50 * D.R.r ^ 2) hX
    omega
  have hc : (M.p0 = 0 ∨ M.p0 = D.R.r) ∨ (0 < M.p0 ∧ M.p0 < D.R.r ∧ GlobalTheory.ShareOn.ArchOn M ka T ∧
      GlobalTheory.ShareOn.sOf M ≤ T ∧ LevelHyp (GlobalTheory.ShareOn.sub M ⊥)) := by
    rcases hcase with h | ⟨h1, h2, h3⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, h2, h3, hsOf, hbot⟩

  let A := p.R.toRealDat.FW i
  let N := p.R.toRealDat.nW i
  let ρK : Representation D.what₂.LL p.P.Gp (Fin N → D.what₂.LL) := GlobalTheory.TwistedRepresentationEmbedding.twist A.ρ A.chi⁻¹
  let χM : p.P.Gp →* ℂˣ := (Units.map σ.toMonoidHom).comp A.chi⁻¹
  let ρM : Representation ℂ p.P.Gp (M.cusp ka) := GlobalTheory.TwistedRepresentationEmbedding.twist ρ χM
  let ρE : Representation ℂ p.P.Gp (Fin N → ℂ) := GlobalTheory.TwistedRepresentationEmbedding.repE D.what₂.embLL ρK
  have hequivM : ∀ g v, ρM g (f v) = f (ρK g v) := by
    intro g v
    rw [GlobalTheory.TwistedRepresentationEmbedding.twist_apply, GlobalTheory.TwistedRepresentationEmbedding.twist_apply, hequiv, map_smulₛₗ]
    rfl
  have hequivE : ∀ g v, ρE g (GlobalTheory.TwistedRepresentationEmbedding.embV D.what₂.embLL N v) = GlobalTheory.TwistedRepresentationEmbedding.embV D.what₂.embLL N (ρK g v) := fun g v => GlobalTheory.TwistedRepresentationEmbedding.repE_embV _ _ _ _
  let ψ0' : P' →* D.what₂.LLˣ := p.P.ψ0⁻¹.comp (Subgroup.inclusion hle)
  let lamM : P' →* ℂˣ := (Units.map σ.toMonoidHom).comp ψ0'
  let lamb : P' →* ℂˣ := lam.comp (π.subgroupComap P)

  have hemb : ∀ k, ∃ n : ℕ, EmbReg ρE ((Hh k).comap π) n ∧
      (n : ℝ) * Nat.card ((Hh k).comap π) ≤ 2 * Nat.card P' * finrank ℂ (eig ρM P' lamM) := by
    intro k
    obtain ⟨n, hn, hb⟩ := model_bound M ka ρM T (GlobalTheory.TwistedRepresentationEmbedding.isPullRep_twist hpull χM) hc _ P' (hHlev k) hP'lev lamM
    exact ⟨n, GlobalTheory.T.embedsInRegularRepresentationCopies_complexEmbedding_indep D.what₂.LL _ _ p.P.Gp N ρK σ D.what₂.embLL ρM ρE f (GlobalTheory.TwistedRepresentationEmbedding.embV D.what₂.embLL N) hli hspan
      (GlobalTheory.TwistedRepresentationEmbedding.embV_li _ _) (GlobalTheory.TwistedRepresentationEmbedding.embV_span _ _) hequivM hequivE _ n hn, hb⟩
  choose n hnE hnb using hemb

  have alg : ∀ (u w : D.what₂.LLˣ) (x y : Fin N → D.what₂.LL), y = ((u * w : D.what₂.LLˣ) : D.what₂.LL) • x ↔
      ((u⁻¹ : D.what₂.LLˣ) : D.what₂.LL) • y - ((w : D.what₂.LLˣ) : D.what₂.LL) • x = 0 := by
    intro u w x y
    rw [sub_eq_zero]
    constructor
    · rintro rfl
      rw [smul_smul, ← Units.val_mul, inv_mul_cancel_left]
    · intro h
      rw [Units.val_mul, mul_smul, ← h, smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul]
  let aK : P' → (Fin N → D.what₂.LL) →ₗ[D.what₂.LL] (Fin N → D.what₂.LL) := fun γ =>
    ρK γ - ((ψ0' γ : D.what₂.LLˣ) : D.what₂.LL) • LinearMap.id
  have haK : ∀ γ F, aK γ F = (((A.chi γ)⁻¹ : D.what₂.LLˣ) : D.what₂.LL) • A.ρ γ F -
      ((p.P.ψ0⁻¹ ⟨γ, hle γ.2⟩ : D.what₂.LLˣ) : D.what₂.LL) • F := fun γ F => rfl
  have hsp : spType p.R.toRealDat p.F.lv2 i = ⨅ γ : P', LinearMap.ker (aK γ) := by
    ext F
    simp only [Submodule.mem_iInf, LinearMap.mem_ker]
    change F ∈ A.typeP p.P.P0 p.P.ψ0⁻¹ ↔ _
    rw [Formalism.IndefR.Arith.FormsL.mem_typeP]
    constructor
    · intro h γ
      rw [haK]
      exact (alg _ _ _ _).1 (h ⟨γ, hle γ.2⟩)
    · intro h q
      have := h ⟨q, hge q.2⟩
      rw [haK] at this
      exact (alg _ _ _ _).2 this
  have dM : finrank ℂ (eig ρM P' lamM) = finrank D.what₂.LL (spType p.R.toRealDat p.F.lv2 i) := by
    rw [hsp]
    refine GlobalTheory.T.finrank_iInf_ker_semilinear_standardBasis D.what₂.LL (M.cusp ka) P' σ N f hli hspan aK (fun γ => ρM γ - ((lamM γ : ℂˣ) : ℂ) • LinearMap.id) ?_
    intro γ v
    show _ = f (ρK γ v - ((ψ0' γ : D.what₂.LLˣ) : D.what₂.LL) • v)
    rw [map_sub, map_smulₛₗ, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, hequivM]
    rfl
  have hlamb : ∀ γ : P', ((lamb γ : ℂˣ) : ℂ) = D.what₂.embLL ((ψ0' γ : D.what₂.LLˣ) : D.what₂.LL) :=
    fun γ => hlam ⟨γ, hle γ.2⟩ γ.2
  have haE : ∀ (γ : P') v, (ρE γ - ((lamb γ : ℂˣ) : ℂ) • LinearMap.id : (Fin N → ℂ) →ₗ[ℂ] (Fin N → ℂ))
      (GlobalTheory.TwistedRepresentationEmbedding.embV D.what₂.embLL N v) = GlobalTheory.TwistedRepresentationEmbedding.embV D.what₂.embLL N (aK γ v) := by
    intro γ v
    show _ = GlobalTheory.TwistedRepresentationEmbedding.embV D.what₂.embLL N (ρK γ v - ((ψ0' γ : D.what₂.LLˣ) : D.what₂.LL) • v)
    rw [map_sub, map_smulₛₗ, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, hequivE, hlamb]
  have dE : finrank ℂ (eig ρE P' lamb) = finrank D.what₂.LL (spType p.R.toRealDat p.F.lv2 i) := by
    rw [hsp]
    exact GlobalTheory.T.finrank_iInf_ker_semilinear_standardBasis D.what₂.LL (Fin N → ℂ) P' D.what₂.embLL N (GlobalTheory.TwistedRepresentationEmbedding.embV D.what₂.embLL N) (GlobalTheory.TwistedRepresentationEmbedding.embV_li _ _) (GlobalTheory.TwistedRepresentationEmbedding.embV_span _ _) aK
      (fun γ => ρE γ - ((lamb γ : ℂˣ) : ℂ) • LinearMap.id) haE

  haveI : Fintype (G0g D.nd) := Fintype.ofEquiv p.P.Gp e.toEquiv
  have hsumE : Representation.asAlgebraHom (ρE.comp ιs) D.ntypes.e0 =
      ∑ g : p.P.Gp, D.ntypes.e0.coeff (e g) • ρE g := by
    rw [Representation.asAlgebraHom_def, MonoidAlgebra.lift_apply, Finsupp.sum_fintype D.ntypes.e0.coeff (fun a b => b • (ρE.comp ιs) a) (fun a => zero_smul ℂ _)]
    exact (Fintype.sum_equiv e.toEquiv (fun g => D.ntypes.e0.coeff (e g) • ρE g)
      (fun h => D.ntypes.e0.coeff h • (ρE.comp ιs) h) (fun g => by simp [ιs])).symm
  obtain ⟨-, -, -, hid, -, -⟩ := p.grpRecPin
  have hE0 : ∀ v, Representation.asAlgebraHom (ρE.comp ιs) D.ntypes.e0 (GlobalTheory.TwistedRepresentationEmbedding.embV D.what₂.embLL N v) =
      GlobalTheory.TwistedRepresentationEmbedding.embV D.what₂.embLL N (eGood p.R.toRealDat i v) := by
    intro v
    have hG : eGood p.R.toRealDat i v = ∑ g : p.P.Gp, (idemOf p.P.A3.A.X).coeff g • ρK g v := by
      show ((∑ g, ((idemOf p.P.A3.A.X).coeff g * ((A.chi g)⁻¹ : D.what₂.LLˣ)) • A.ρ g :
        (Fin N → D.what₂.LL) →ₗ[D.what₂.LL] (Fin N → D.what₂.LL)) v) = _
      rw [LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [LinearMap.smul_apply, mul_smul]
      rfl
    rw [hsumE, LinearMap.sum_apply, hG, map_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [LinearMap.smul_apply, hequivE, map_smulₛₗ, hid]
  let aO : Option P' → (Fin N → D.what₂.LL) →ₗ[D.what₂.LL] (Fin N → D.what₂.LL) := fun o =>
    o.elim (eGood p.R.toRealDat i) aK
  let aO' : Option P' → (Fin N → ℂ) →ₗ[ℂ] (Fin N → ℂ) := fun o =>
    o.elim (Representation.asAlgebraHom (ρE.comp ιs) D.ntypes.e0) (fun γ => ρE γ - ((lamb γ : ℂˣ) : ℂ) • LinearMap.id)
  have dBad : finrank ℂ (eig ρE P' lamb ⊓ LinearMap.ker (Representation.asAlgebraHom (ρE.comp ιs) D.ntypes.e0) :
      Submodule ℂ (Fin N → ℂ)) = finrank D.what₂.LL (spType p.R.toRealDat p.F.lv2 i ⊓
      LinearMap.ker (eGood p.R.toRealDat i) : Submodule D.what₂.LL (Fin N → D.what₂.LL)) := by
    have h1 : (eig ρE P' lamb ⊓ LinearMap.ker (Representation.asAlgebraHom (ρE.comp ιs) D.ntypes.e0) :
        Submodule ℂ (Fin N → ℂ)) = ⨅ o, LinearMap.ker (aO' o) := by
      rw [iInf_option, inf_comm]; rfl
    have h2 : (spType p.R.toRealDat p.F.lv2 i ⊓ LinearMap.ker (eGood p.R.toRealDat i) :
        Submodule D.what₂.LL (Fin N → D.what₂.LL)) = ⨅ o, LinearMap.ker (aO o) := by
      rw [iInf_option, inf_comm, hsp]; rfl
    rw [h1, h2]
    refine GlobalTheory.T.finrank_iInf_ker_semilinear_standardBasis D.what₂.LL (Fin N → ℂ) (Option P') D.what₂.embLL N (GlobalTheory.TwistedRepresentationEmbedding.embV D.what₂.embLL N) (GlobalTheory.TwistedRepresentationEmbedding.embV_li _ _) (GlobalTheory.TwistedRepresentationEmbedding.embV_span _ _)
      aO aO' ?_
    rintro (_ | γ) v
    · exact hE0 v
    · exact haE γ v

  have hsplit : IsSplit π ιs := ⟨fun g => e.apply_symm_apply g, fun g γ h => by
    have hγ : γ = 1 := e.injective (h.trans e.map_one.symm)
    subst hγ; simp⟩
  let ψ₀ : ∀ k : Fin 2, AddChar (ZMod (D.host.g k)) ℂ := fun k =>
    haveI : NeZero (D.host.g k) := ⟨(D.host.g_prime k).ne_zero⟩
    ZMod.stdAddChar
  have hψ₀ : ∀ k, ψ₀ k ≠ 1 := by
    intro k h
    haveI : NeZero (D.host.g k) := ⟨(D.host.g_prime k).ne_zero⟩
    haveI : Fact (1 < D.host.g k) := ⟨(D.host.g_prime k).one_lt⟩
    have := ZMod.isPrimitive_stdAddChar (D.host.g k) (one_ne_zero)
    rw [AddChar.mulShift_one] at this
    exact this h
  have hbd : ∀ k, (n k : ℝ) * Nat.card ((Hh k).comap π) ≤
      2 * Nat.card (P.comap π) * finrank ℂ (eig ρE (P.comap π) lamb) := by
    intro k; rw [dE, ← dM]; exact hnb k
  obtain ⟨S, hSbad, hineq⟩ := GlobalTheory.T.bad_part_dim_le_sum_local_shares_whittaker D p.P.Gp (Fin N → ℂ) π ιs hsplit ρE P lam ψ hW lamb (fun γ => rfl) Hh hHh n 2
    hnE hbd ψ₀ hψ₀
  have hadm := GlobalTheory.T.admLq_of_green_of_eSerTie hGr D hRec.eSer
  have hloc : ∀ k, 4 * locShare D (fun k _ => eUk D k (ψ₀ k)) k (S k) ≤ del := fun k =>
    le_trans (by linarith [GlobalTheory.T.weightedIdempotent_localShare_bad_tuples_le D ψ₀ hψ₀ hadm hA hr (fun k => (hg k).1) k (S k) (hSbad k)]) (hg k).2
  rw [dBad, dE] at hineq
  unfold GlobalTheory.ShareOn.BadW
  have h0 := hloc 0
  have h1 := hloc 1
  have hd : (0 : ℝ) ≤ finrank D.what₂.LL (spType p.R.toRealDat p.F.lv2 i) := Nat.cast_nonneg _
  refine hineq.trans ?_
  nlinarith

end Point

theorem badWSt_of (hG : GlobalTheory.Published.GreenCuspidal) (hM : ModelSt) : BadWSt := by
  have hGr := hG.green
  refine Closed.imp ((hM.and GlobalTheory.T.badShareSize_bounds_along_family).and GlobalTheory.T.hodgeLineMultiple_le_familyThreshold) ?_
  rintro eps Fm CH - ⟨⟨⟨x1, hx1⟩, ⟨x2, hx2⟩⟩, ⟨x3, hx3⟩⟩
  refine ⟨max x1 (max x2 x3), fun x hx hle ι p hp hMore r hr hown i => ?_⟩
  have h1 : x1 ≤ x := (le_max_left _ _).trans hle
  have h2 : x2 ≤ x := ((le_max_left _ _).trans (le_max_right _ _)).trans hle
  have h3 : x3 ≤ x := ((le_max_right _ _).trans (le_max_right _ _)).trans hle
  obtain ⟨hr100, hA, -, hg⟩ := hx2 x hx h2 ι
  exact point p i _ _ hGr hp hMore.2.2 (hx1 x hx h1 ι p hp hMore r hr hown i) hr100 hA hg (hx3 x hx h3 ι)


end GlobalTheory.BadWOn

end
end
