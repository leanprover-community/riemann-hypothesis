module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.BigLineBundleMoriwaki
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.ProjectionIntoHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.RieszHermitianHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.SameGenusFix
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AlgebraMapIntCastSmul
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.FormMemOfDual
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.JordanExists
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.GmapEqSelfOfFix
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DiscIsoOfProj
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ApplyMemSmulOfMemAutSub
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CardEqRelIndex
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.FormRightMem
import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SummandLocalization
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsBasisLocF
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.SimpleRing.Principal

section
@[expose] public section

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G6

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.HermitianLattices.Ext.L3.LocalSpans

theorem summand_localization : SummandLoc := by
  rintro K F V _ _ _ _ _ _ _ _ _ _ X 𝔭 h𝔭 Λ ⟨L, hL, rfl⟩
  let W := Submodule.span K (L : Set V)
  let i := W.subtype.restrictScalars (𝓞 K)
  let L' := L.comap i
  have hmap : L'.map i = L := by
    apply Submodule.map_comap_eq_self
    change L ≤ LinearMap.range (W.restrictScalars (𝓞 K)).subtype
    rw [Submodule.range_subtype]
    exact fun _ hx => Submodule.subset_span hx
  have hfull : Submodule.IsFullLattice K L' := by
    have hfg : L'.FG := Submodule.fg_of_fg_map_injective i Subtype.val_injective
      (hmap.symm ▸ hL.fg)
    letI : Submodule.IsLattice K L' := Submodule.IsLattice.of_fg K hfg
    refine ⟨?_⟩
    apply Submodule.map_injective_of_injective (f := W.subtype) Subtype.val_injective
    have himage : W.subtype '' (L' : Set W) = (L : Set V) := by
      rw [← hmap, Submodule.map_coe]
      rfl
    rw [Submodule.map_span, himage, Submodule.map_top, Submodule.range_subtype]
  let X' := X.comap W.subtype
  let Lloc := UpperTheory.Reformulated.B.SummandLocalization.locF 𝔭 L'
  obtain ⟨p, hpX, hpId, hpL⟩ :=
    UpperTheory.Reformulated.B.SummandLocalization.summand_localization
      K F W X' 𝔭 h𝔭 Lloc ⟨L', hfull, rfl⟩
  let N := (LinearMap.ker p).map W.subtype
  have hNX : Disjoint N X := by
    rw [Submodule.disjoint_def]
    rintro _ ⟨w, hw, rfl⟩ hx
    have hzero : p w = 0 := hw
    rw [hpId w hx] at hzero
    exact congrArg Subtype.val hzero
  obtain ⟨Y, hNY, hYX⟩ := hNX.exists_isCompl
  let π := X.projection Y hYX.symm
  have hπ (w : W) : π w = (p w : V) := by
    have hdiff : (w : V) - (p w : V) ∈ Y := hNY ⟨w - p w, by
      change p (w - p w) = 0
      rw [map_sub, hpId _ (hpX w), sub_self], rfl⟩
    have he := Submodule.projection_apply_of_mem_right hYX.symm hdiff
    change π ((w : V) - (p w : V)) = 0 at he
    have hp : (p w : V) ∈ X := hpX w
    have hproj : π (p w : V) = (p w : V) :=
      Submodule.projection_apply_of_mem_left hYX.symm hp
    rwa [map_sub, hproj, sub_eq_zero] at he
  refine ⟨π, Submodule.projection_apply_mem hYX.symm,
    fun _ hx => Submodule.projection_apply_of_mem_left hYX.symm hx, ?_⟩
  letI := h𝔭.isPrime
  intro y hy
  obtain ⟨t, ht, hty⟩ := (LocalSpans.mem_locF 𝔭 L y).1 hy
  have ht0 : t ≠ 0 := fun ht0 => ht (ht0 ▸ 𝔭.zero_mem)
  let a := algebraMap (𝓞 F) (𝓞 K) t
  have ha : algebraMap (𝓞 K) K a ≠ 0 := by
    intro h
    apply ht0
    apply RingOfIntegers.algebraMap.injective F K
    apply (RingOfIntegers.coe_injective)
    simpa [a] using h
  have hyW : y ∈ W := by
    have hs : algebraMap (𝓞 K) K a • y ∈ W := by
      rw [algebraMap_smul]
      exact Submodule.subset_span hty
    have h := W.smul_mem (algebraMap (𝓞 K) K a)⁻¹ hs
    rwa [smul_smul, inv_mul_cancel₀ ha, one_smul] at h
  let w : W := ⟨y, hyW⟩
  have hwL : w ∈ Lloc := (LocalSpans.mem_locF 𝔭 L' w).2 ⟨t, ht, hty⟩
  rw [show y = (w : V) from rfl, hπ w]
  obtain ⟨u, hu, hpu⟩ := (LocalSpans.mem_locF 𝔭 L' (p w)).1 (hpL w hwL)
  exact (LocalSpans.mem_locF 𝔭 L (p w : V)).2 ⟨u, hu, hpu⟩

end Formalism.L2.SG.Pf.G6
end
end
end


section
@[expose] public section

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.ProjectionDiscriminantModule

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G6

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem mem_of_isLatIn {X : Submodule K V} {L : Submodule (𝓞 K) V} (hL : IsLatIn X L) :
    ∀ x ∈ L, x ∈ X := fun x hx => hL.2 ▸ Submodule.subset_span hx

theorem isLattice_sup {X Y : Submodule K V} (hc : IsCompl X Y) {A B : Submodule (𝓞 K) V}
    (hA : IsLatIn X A) (hB : IsLatIn Y B) : Submodule.IsLattice K (A ⊔ B) :=
  Submodule.IsLattice.of_fg K (hA.1.sup hB.1)

theorem prO_sup {X Y : Submodule K V} (hc : IsCompl X Y) {A B : Submodule (𝓞 K) V}
    (hA : ∀ x ∈ A, x ∈ X) (hB : ∀ y ∈ B, y ∈ Y) {z : V} (hz : z ∈ A ⊔ B) : prO hc z ∈ A := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hz
  rw [map_add (f := _), prO_apply, prO_apply, Submodule.projection_apply_of_mem_left hc (hA a ha),
    (Submodule.projection_apply_eq_zero_iff hc).2 (hB b hb), add_zero]
  exact ha

theorem prO_locF {X Y : Submodule K V} (hc : IsCompl X Y) {𝔭 : Ideal (𝓞 F)} (hp : 𝔭.IsPrime)
    {A B : Submodule (𝓞 K) V} (hA : ∀ x ∈ A, x ∈ X) (hB : ∀ y ∈ B, y ∈ Y) {z : V}
    (hz : z ∈ locF 𝔭 (A ⊔ B)) : prO hc z ∈ locF 𝔭 A := by
  obtain ⟨t, ht, htz⟩ := (LocF.mem_locF_iff hp _ z).1 hz
  refine (LocF.mem_locF_iff hp _ _).2 ⟨t, ht, ?_⟩
  rw [← LinearMap.map_smul]
  exact prO_sup hc hA hB htz

theorem discMod_finite [FiniteDimensional K V] {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V}
    (hc : IsCompl U (orthK h U)) {M T Λ₀ N₀ : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) (hM : IsLatIn U M) (hT : IsLatIn (orthK h U) T)
    (hN₀ : Submodule.IsLattice K N₀) (hΛ₀ : locF 𝔭 N₀ = Λ₀)
    (hW : Λ₀ ⊓ (orthK h U).restrictScalars (𝓞 K) = locF 𝔭 T)
    (hiW : ∀ x ∈ Λ₀, prO hc.symm x ∈ locF 𝔭 (dualIn h (orthK h U) T))
    (hpr : ∀ v ∈ locF 𝔭 (dualIn h (orthK h U) T), ∃ x ∈ Λ₀, prO hc.symm x = v) :
    Finite (DiscMod h (orthK h U) T 𝔭) := by
  subst hΛ₀
  have hp := h𝔭.isPrime
  have hTM : Submodule.IsFullLattice K (T ⊔ M) := by
    refine { toIsLattice := isLattice_sup hc.symm hT hM, span_eq_top := ?_ }
    rw [eq_top_iff, ← hc.symm.sup_eq_top, ← hT.2, ← hM.2]
    exact sup_le
      (Submodule.span_mono (SetLike.coe_subset_coe.mpr le_sup_left))
      (Submodule.span_mono (SetLike.coe_subset_coe.mpr le_sup_right))
  obtain ⟨r, hr⟩ := LIOrb.exists_pow_smul_le hN₀ hTM h𝔭
  have hsurj := toDisc_surj h hc.symm T (locF 𝔭 N₀) 𝔭 hiW hpr
  have hker : ((extP K 𝔭) ^ r • ⊤ : Submodule (𝓞 K) ↥(locF 𝔭 N₀)) ≤
      LinearMap.ker (toDisc h hc.symm T (locF 𝔭 N₀) 𝔭 hiW) := by
    rw [Submodule.smul_le]
    intro a ha y _
    rw [mem_ker_toDisc]
    have h1 : a • (y : V) ∈ locF 𝔭 (T ⊔ M) := hr (Submodule.smul_mem_smul ha y.2)
    exact prO_locF hc.symm hp (mem_of_isLatIn hT) (mem_of_isLatIn hM) h1
  haveI := LIOrb.finite_quot hN₀ h𝔭 r
  refine Finite.of_surjective (((extP K 𝔭) ^ r • ⊤ : Submodule (𝓞 K) ↥(locF 𝔭 N₀)).liftQ
    (toDisc h hc.symm T (locF 𝔭 N₀) 𝔭 hiW) hker) ?_
  intro d
  obtain ⟨y, rfl⟩ := hsurj d
  exact ⟨Submodule.Quotient.mk y, Submodule.liftQ_apply _ _ _⟩

theorem exists_lattice_locF {Λ L₁ L₂ : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    (hL₁ : Submodule.IsFullLattice K L₁) (hL₂ : L₂.FG) (hΛ : locF 𝔭 Λ = Λ) (h1 : L₁ ≤ Λ)
    (h2 : Λ ≤ locF 𝔭 L₂) : ∃ Λ', Submodule.IsLattice K Λ' ∧ locF 𝔭 Λ' = Λ := by
  refine ⟨(L₁ ⊔ L₂) ⊓ Λ, ⟨(hL₁.fg.sup hL₂).of_le inf_le_left, ?_⟩, ?_⟩
  · intro s hs hli
    exact (LinearIndependent.iff_fractionRing _ _).mp hli
  · have e := LIOrb.IA.locF_inf 𝔭 h𝔭.isPrime (L₁ ⊔ L₂) Λ
    rw [hΛ] at e
    rw [e]
    exact le_antisymm inf_le_right (le_inf (h2.trans (LocF.locF_mono 𝔭 le_sup_right)) le_rfl)

end Formalism.L2.SG.Pf.ProjectionDiscriminantModule
end
end
end


section
@[expose] public section

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.OrthogonalProjections

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G6

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V} {hc : IsCompl U (orthK h U)}
  {M T Λ Λ₀ : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)}
  {P : Module.End (𝓞 K) (DiscMod h (orthK h U) T 𝔭)}

theorem memW (hG : Good hc M T 𝔭 Λ) {b : V} (hb : b ∈ locF 𝔭 (dualIn h (orthK h U) T)) :
    b ∈ orthK h U := by
  obtain ⟨x, -, rfl⟩ := hG.oW b hb
  first
  | exact Submodule.projection_apply_mem _ _

theorem mem_glue_of (hG₀ : Good hc M T 𝔭 Λ₀) {y : V} (hy : y ∈ Λ₀)
    (x' : ↥(locF 𝔭 (dualIn h (orthK h U) T)))
    (hx' : Submodule.Quotient.mk x' = P (Submodule.Quotient.mk ⟨prO hc.symm y, hG₀.iW y hy⟩)) :
    prO hc y + x' ∈ glue hc T 𝔭 Λ₀ P := by
  have hx'W : (x' : V) ∈ orthK h U := memW hG₀ x'.2
  have hyU : prO hc y ∈ U := by
    first
    | exact Submodule.projection_apply_mem _ _
  have h0 : prO hc.symm (prO hc y) = 0 := by
    first
    | (rw [prO_apply]; simp [hyU])
  refine ⟨x', ?_, y, hy, ⟨prO hc.symm y, hG₀.iW y hy⟩, rfl, ?_, hx'⟩
  · rw [map_add (f := _), orth_projection_symm_of_mem (hc' := hc) hx'W, h0, zero_add]
  · rw [map_add (f := _), prO_of_mem_U (hc' := hc) hyU, orth_projection_of_mem_compl (hc' := hc) hx'W, add_zero]

theorem glue_inf_U (hG₀ : Good hc M T 𝔭 Λ₀) (hd₀ : dualF h 𝔭 Λ₀ = Λ₀) (hP : FP P) :
    glue hc T 𝔭 Λ₀ P ⊓ U.restrictScalars (𝓞 K) = locF 𝔭 M := by
  ext x
  simp only [Submodule.mem_inf, Submodule.restrictScalars_mem]
  constructor
  · rintro ⟨⟨b, hb, y, hy, c, hcy, hU, hPb⟩, hxU⟩
    have hb0 : b = 0 :=
      Subtype.ext (hb.trans ((prO_symm_of_mem_U (hc' := hc) hxU).trans Submodule.coe_zero.symm))
    rw [hb0, Submodule.Quotient.mk_zero] at hPb
    have hxy : prO hc y = x := by rw [hU, prO_of_mem_U (hc' := hc) hxU]
    have hcW : (c : V) ∈ orthK h U := by
      rw [hcy]
      first
      | exact Submodule.projection_apply_mem _ _
    have hcO : ∀ u ∈ U, h u (c : V) = 0 := by
      intro u hu
      simp only [orthK, Submodule.mem_iInf, LinearMap.mem_ker] at hcW
      exact hcW u hu
    have hcΛ : (c : V) ∈ Λ₀ := by
      rw [← hd₀]
      intro z hz
      have hzW := hG₀.iW z hz
      obtain ⟨d, hd⟩ := Submodule.Quotient.mk_surjective _
        (P (Submodule.Quotient.mk (⟨prO hc.symm z, hzW⟩ : ↥(locF 𝔭 (dualIn h (orthK h U) T)))))
      have h2 := hP ⟨prO hc.symm z, hzW⟩ c d 0 hd (by rw [Submodule.Quotient.mk_zero]; exact hPb)
      have e : h z (c : V) =
          -(h (d : V) (((0 : ↥(locF 𝔭 (dualIn h (orthK h U) T))) : V)) - h (prO hc.symm z) (c : V)) := by
        have e1 : h z (c : V) = h (prO hc z) (c : V) + h (prO hc.symm z) (c : V) := by
          conv_lhs => rw [← prO_add hc z]
          rw [map_add (f := _), LinearMap.add_apply]
        rw [e1, hcO (prO hc z) ?_]
        · simp
        · first
      | exact Submodule.projection_apply_mem _ _
      rw [e]
      exact Submodule.neg_mem _ h2
    have hxΛ : x ∈ Λ₀ := by
      have e := prO_add hc y
      rw [hxy, ← hcy] at e
      have ex : x = y - (c : V) := eq_sub_of_add_eq e
      rw [ex]
      exact Λ₀.sub_mem hy hcΛ
    rw [← hG₀.cU]
    exact Submodule.mem_inf.2 ⟨hxΛ, hxU⟩
  · intro hx
    have hxΛU : x ∈ Λ₀ ⊓ U.restrictScalars (𝓞 K) := by
      rw [hG₀.cU]
      exact hx
    obtain ⟨hxΛ, hxU⟩ := Submodule.mem_inf.1 hxΛU
    have hxU' : x ∈ U := hxU
    have hps : prO hc.symm x = 0 := prO_symm_of_mem_U (hc' := hc) hxU'
    have hmem : prO hc.symm x ∈ locF 𝔭 (dualIn h (orthK h U) T) := hG₀.iW x hxΛ
    refine ⟨⟨0, Submodule.coe_zero.trans hps.symm, x, hxΛ, ⟨prO hc.symm x, hmem⟩, rfl, rfl, ?_⟩, hxU'⟩
    have hz : (⟨prO hc.symm x, hmem⟩ : ↥(locF 𝔭 (dualIn h (orthK h U) T))) = 0 := Subtype.ext hps
    rw [hz, Submodule.Quotient.mk_zero, map_zero]

theorem glue_inf_orthK_eq_locF (hG₀ : Good hc M T 𝔭 Λ₀) :
    glue hc T 𝔭 Λ₀ P ⊓ (orthK h U).restrictScalars (𝓞 K) = locF 𝔭 T := by
  ext x
  simp only [Submodule.mem_inf, Submodule.restrictScalars_mem]
  constructor
  · rintro ⟨⟨b, hb, y, hy, c, hcy, hU, hP⟩, hxW⟩
    have hx0 : prO hc x = 0 := orth_projection_of_mem_compl (hc' := hc) hxW
    have hxb : (b : V) = x := by rw [hb, orth_projection_symm_of_mem (hc' := hc) hxW]
    have hyc : (c : V) = y := by
      rw [hcy]
      have e := prO_add hc y
      rw [hU, hx0, zero_add] at e
      exact e
    have hyW : y ∈ orthK h U := by
      rw [← hyc, hcy]
      first
      | exact Submodule.projection_apply_mem _ _
    have hyT : y ∈ locF 𝔭 T := by
      rw [← hG₀.cW]
      exact Submodule.mem_inf.2 ⟨hy, hyW⟩
    have hc0 : (Submodule.Quotient.mk c : DiscMod h (orthK h U) T 𝔭) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).2
        (Submodule.mem_comap.2 (by rw [Submodule.subtype_apply, hyc]; exact hyT))
    rw [hc0, map_zero] at hP
    have hb' := Submodule.mem_comap.1 ((Submodule.Quotient.mk_eq_zero _).1 hP)
    rw [Submodule.subtype_apply, hxb] at hb'
    exact hb'
  · intro hx
    have hxΛW : x ∈ Λ₀ ⊓ (orthK h U).restrictScalars (𝓞 K) := by
      rw [hG₀.cW]
      exact hx
    obtain ⟨hxΛ, hxW⟩ := Submodule.mem_inf.1 hxΛW
    have hxW' : x ∈ orthK h U := hxW
    have hps : prO hc.symm x = x := orth_projection_symm_of_mem (hc' := hc) hxW'
    have hmem : prO hc.symm x ∈ locF 𝔭 (dualIn h (orthK h U) T) := hG₀.iW x hxΛ
    refine ⟨⟨⟨prO hc.symm x, hmem⟩, rfl, x, hxΛ, ⟨prO hc.symm x, hmem⟩, rfl, rfl, ?_⟩, hxW'⟩
    have hc0 : (Submodule.Quotient.mk (⟨prO hc.symm x, hmem⟩ : ↥(locF 𝔭 (dualIn h (orthK h U) T))) :
        DiscMod h (orthK h U) T 𝔭) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).2
        (Submodule.mem_comap.2 (by rw [hps] at hmem ⊢; exact hx : prO hc.symm x ∈ locF 𝔭 T))
    rw [hc0, map_zero]

theorem glue_int (hs : h.IsSymm) (hd₀ : dualF h 𝔭 Λ₀ = Λ₀) (hP : FP P) {a b : V}
    (ha : a ∈ glue hc T 𝔭 Λ₀ P) (hb : b ∈ glue hc T 𝔭 Λ₀ P) :
    h a b ∈ locF 𝔭 (1 : Submodule (𝓞 K) K) := by
  obtain ⟨ba, hba, ya, hya, ca, hca, hUa, hPa⟩ := ha
  obtain ⟨bb, hbb, yb, hyb, cb, hcb, hUb, hPb⟩ := hb
  rw [split hs hc a b, ← hUa, ← hUb, ← hba, ← hbb]
  have hy : h (prO hc ya) (prO hc yb) = h ya yb - h ca cb := by
    rw [split hs hc ya yb, ← hca, ← hcb]
    ring
  rw [hy]
  have h1 : h ya yb ∈ locF 𝔭 (1 : Submodule (𝓞 K) K) := by
    have hmemd : yb ∈ dualF h 𝔭 Λ₀ := by
      rw [hd₀]
      exact hyb
    exact hmemd ya hya
  have h2 := hP ca cb ba bb hPa hPb
  have e : h ya yb - h ca cb + h ba bb = h ya yb + (h ba bb - h ca cb) := by ring
  rw [e]
  exact Submodule.add_mem _ h1 h2

theorem glue_le_dual (hs : h.IsSymm) (hd₀ : dualF h 𝔭 Λ₀ = Λ₀) (hP : FP P) :
    glue hc T 𝔭 Λ₀ P ≤ dualF h 𝔭 (glue hc T 𝔭 Λ₀ P) := by
  intro x hx y hy
  exact glue_int hs hd₀ hP hy hx

theorem dual_le_glue (hs : h.IsSymm) (hG₀ : Good hc M T 𝔭 Λ₀) (hd₀ : dualF h 𝔭 Λ₀ = Λ₀)
    (hM : IsLatIn U M) (hT : IsLatIn (orthK h U) T) (hP : FP P) (hsurj : Function.Surjective P) :
    dualF h 𝔭 (glue hc T 𝔭 Λ₀ P) ≤ glue hc T 𝔭 Λ₀ P := by
  intro x hx
  have hx' : ∀ z ∈ glue hc T 𝔭 Λ₀ P, h z x ∈ locF 𝔭 (1 : Submodule (𝓞 K) K) := hx
  have hLM : locF 𝔭 M ≤ glue hc T 𝔭 Λ₀ P := by
    intro m hm
    rw [← glue_inf_U hG₀ hd₀ hP] at hm
    exact hm.1
  have hLT : locF 𝔭 T ≤ glue hc T 𝔭 Λ₀ P := by
    intro m hm
    rw [← glue_inf_orthK_eq_locF (P := P) hG₀] at hm
    exact hm.1
  have hxU : prO hc x ∈ locF 𝔭 (dualIn h U M) := by
    apply mem_locF_dualIn hM.1 𝔭 (prO_mem hc x)
    intro m hm
    have hmU := le_of_isLatIn hM m hm
    have e : h m x = h m (prO hc x) + h m (prO hc.symm x) := by rw [← map_add (f := _), prO_add]
    rw [h_UW hmU (prO_symm_mem hc x), add_zero] at e
    rw [← e]
    exact hx' m (hLM (LocF.le_locF 𝔭 M hm))
  have hxW : prO hc.symm x ∈ locF 𝔭 (dualIn h (orthK h U) T) := by
    apply mem_locF_dualIn hT.1 𝔭 (prO_symm_mem hc x)
    intro m hm
    have hmW := le_of_isLatIn hT m hm
    have e : h m x = h m (prO hc x) + h m (prO hc.symm x) := by rw [← map_add (f := _), prO_add]
    rw [h_WU hs hmW (prO_mem hc x), zero_add] at e
    rw [← e]
    exact hx' m (hLT (LocF.le_locF 𝔭 T hm))
  obtain ⟨y, hy, hyU⟩ := hG₀.oU _ hxU
  obtain ⟨x'', hx''⟩ := Submodule.Quotient.mk_surjective _
    (P (Submodule.Quotient.mk ⟨prO hc.symm y, hG₀.iW y hy⟩))
  have hz := mem_glue_of hG₀ hy x'' hx''
  have hx''W := memW hG₀ x''.2
  have hdW : prO hc.symm x - (x'' : V) ∈ orthK h U := (orthK h U).sub_mem (prO_symm_mem hc x) hx''W
  have hdx : prO hc.symm x - (x'' : V) = x - (prO hc y + x'') := by
    calc prO hc.symm x - (x'' : V) = (prO hc x + prO hc.symm x) - (prO hc x + x'') := by abel
      _ = _ := by rw [prO_add, hyU]
  have hdT : prO hc.symm x - (x'' : V) ∈ locF 𝔭 T := by
    apply mem_T_of hG₀ hd₀ hdW
    intro b' hb'
    obtain ⟨e, he⟩ := hsurj (Submodule.Quotient.mk ⟨b', hb'⟩)
    induction e using Submodule.Quotient.induction_on with
    | H e₀ =>
      obtain ⟨y₁, hy₁, he₀⟩ := hG₀.oW e₀ e₀.2
      have hz₁ : prO hc y₁ + b' ∈ glue hc T 𝔭 Λ₀ P := by
        refine mem_glue_of hG₀ hy₁ ⟨b', hb'⟩ ?_
        rw [← he]
        congr 2
        exact Subtype.ext he₀.symm
      have h1 := hx' _ hz₁
      have h2 := glue_int hs hd₀ hP hz₁ hz
      have := sub_mem h1 h2
      rw [← map_sub, ← hdx, map_add (f := _), LinearMap.add_apply, h_UW (prO_mem hc y₁) hdW, zero_add] at this
      exact this
  refine ⟨⟨prO hc.symm x, hxW⟩, rfl, y, hy, ⟨prO hc.symm y, hG₀.iW y hy⟩, rfl, hyU, ?_⟩
  rw [← hx'']
  exact (mk_eq_iff _ _).2 hdT

end Formalism.L2.SG.Pf.OrthogonalProjections
end
end
end


-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.GlueLocOfFibCount, Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.LocFDualF, Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.MemWOfPrOZero, Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.ImportsBis, Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.OrthogonalProjections, Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.LocalGluingHolds

-- ===== clump member: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.GlueLocOfFibCount =====
-- clump-header: {"m": "Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.GlueLocOfFibCount", "h": "module\n\npublic import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.BigLineBundleMoriwaki\npublic import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.ProjectionIntoHolds\npublic import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.SummandLocalization\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\npublic import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.RieszHermitianHolds\n\n"}
section -- clump:auto
@[expose] public section

namespace Formalism.L2.SG.Pf.Cnt

open Formalism.L2.SG.Pf.G6

theorem glueLoc_of_fibCount (hn : FibCount) : GlueLoc :=
  glueLoc_of projection_into_holds (projOnto_of summand_localization riesz_hermitian_holds) hn

end Formalism.L2.SG.Pf.Cnt
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.GlueLocOfFibCount =====

-- ===== clump member: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.LocFDualF =====
-- clump-header: {"m": "Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.LocFDualF", "h": "module\n\npublic import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.SameGenusFix\npublic import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AlgebraMapIntCastSmul\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.ProjectionDiscriminantModule

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem locF_dualF {h : V →ₗ⋆[K] V →ₗ[K] K} {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    (L : Submodule (𝓞 K) V) : locF 𝔭 (dualF h 𝔭 L) = dualF h 𝔭 L := by
  have hp := h𝔭.isPrime
  refine le_antisymm ?_ (LocF.le_locF 𝔭 _)
  intro x hx
  obtain ⟨t, ht, htx⟩ := (LocF.mem_locF_iff hp _ x).1 hx
  show ∀ y ∈ L, h y x ∈ locF 𝔭 (1 : Submodule (𝓞 K) K)
  intro y hy
  have e : h y (algebraMap (𝓞 F) (𝓞 K) t • x) = algebraMap (𝓞 F) (𝓞 K) t • h y x := by
    rw [← algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) t) x, LinearMap.map_smul, algebraMap_smul]
  have h1 := (show ∀ y ∈ L, h y (algebraMap (𝓞 F) (𝓞 K) t • x) ∈ locF 𝔭 (1 : Submodule (𝓞 K) K)
    from htx) y hy
  rw [e] at h1
  obtain ⟨s, hs, hs_mem⟩ := (LocF.mem_locF_iff hp (1 : Submodule (𝓞 K) K) _).1 h1
  have hst : s * t ∉ 𝔭 := fun hm => (hp.mem_or_mem hm).elim hs ht
  refine (LocF.mem_locF_iff hp _ _).2 ⟨s * t, hst, ?_⟩
  simpa only [map_mul, mul_smul] using hs_mem

end Formalism.L2.SG.Pf.ProjectionDiscriminantModule
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.LocFDualF =====

-- ===== clump member: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.MemWOfPrOZero =====
-- clump-header: {"m": "Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.MemWOfPrOZero", "h": "module\n\npublic import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.FormMemOfDual\npublic import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AlgebraMapIntCastSmul\npublic import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DualLeGlue\npublic import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.ExistsLatticeLocF\npublic import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.LocFDualF\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.OrthogonalProjections

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G6 Formalism.L2.SG.Pf.ProjectionDiscriminantModule

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V} {hc : IsCompl U (orthK h U)}
  {M T Λ Λ₀ : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)}

def InFib (h : V →ₗ⋆[K] V →ₗ[K] K) (U : Submodule K V) (𝔭 : Ideal (𝓞 F)) (M T Λ : Submodule (𝓞 K) V) :
    Prop :=
  (∃ Λ₀ : Submodule (𝓞 K) V, Submodule.IsLattice K Λ₀ ∧ locF 𝔭 Λ₀ = Λ) ∧
    dualF h 𝔭 Λ = Λ ∧
    Λ ⊓ U.restrictScalars (𝓞 K) = locF 𝔭 M ∧
    Λ ⊓ (orthK h U).restrictScalars (𝓞 K) = locF 𝔭 T

theorem mem_W_of_prO_zero {x : V} (hx : prO hc x = 0) : x ∈ orthK h U ∧ prO hc.symm x = x := by
  have e := prO_add hc x
  rw [hx, zero_add] at e
  refine ⟨?_, e⟩
  rw [← e]
  rw [prO_apply]
  first
  | exact Submodule.projection_apply_mem ..

theorem prO_symm_locF (hp : 𝔭.IsPrime) {N : Submodule (𝓞 K) V} {y : V} (hy : y ∈ locF 𝔭 N) :
    prO hc.symm y ∈ locF 𝔭 (N.map (prO hc.symm)) := by
  obtain ⟨t, ht, hty⟩ := (LocF.mem_locF_iff hp N y).mp hy
  refine (LocF.mem_locF_iff hp _ _).mpr ⟨t, ht, ?_⟩
  have hs := (prO hc.symm).map_smul (algebraMap (𝓞 F) (𝓞 K) t) y
  rw [← hs]
  exact Submodule.mem_map_of_mem hty

theorem glue_mem [FiniteDimensional K V] (hs : h.IsSymm) (h𝔭 : 𝔭.IsMaximal) (hM : IsLatIn U M)
    (hT : IsLatIn (orthK h U) T) (hG₀ : Good hc M T 𝔭 Λ₀) (h0 : InFib h U 𝔭 M T Λ₀)
    {P : Module.End (𝓞 K) (DiscMod h (orthK h U) T 𝔭)} (hP : FP P) (hsurj : Function.Surjective P) :
    InFib h U 𝔭 M T (glue hc T 𝔭 Λ₀ P) := by
  have hp := h𝔭.isPrime
  obtain ⟨⟨N₀, hN₀, hΛ₀⟩, hd₀, -, -⟩ := h0
  have hd : dualF h 𝔭 (glue hc T 𝔭 Λ₀ P) = glue hc T 𝔭 Λ₀ P :=
    le_antisymm (dual_le_glue hs hG₀ hd₀ hM hT hP hsurj) (glue_le_dual hs hd₀ hP)
  have hIU := glue_inf_U hG₀ hd₀ hP
  have hIW := glue_inf_orthK_eq_locF (P := P) hG₀
  refine ⟨?_, hd, hIU, hIW⟩
  have hspan : Submodule.span K (↑(M ⊔ T) : Set V) = ⊤ := by
    apply top_unique
    rw [← hc.sup_eq_top, ← hT.2, ← hM.2]
    exact sup_le (Submodule.span_mono (show M ≤ M ⊔ T from le_sup_left))
      (Submodule.span_mono (show T ≤ M ⊔ T from le_sup_right))
  have hMT : Submodule.IsFullLattice K (M ⊔ T) :=
    { toIsLattice := Submodule.IsLattice.of_fg K (hM.1.sup hT.1)
      span_eq_top := hspan }
  refine exists_lattice_locF h𝔭 hMT (L₂ := N₀ ⊔ N₀.map (prO hc.symm))
    (hN₀.fg.sup (hN₀.fg.map _)) ?_ ?_ ?_
  · conv_lhs => rw [← hd]
    rw [locF_dualF h𝔭, hd]
  · refine sup_le ?_ ?_
    · intro m hm
      have : m ∈ locF 𝔭 M := LocF.le_locF 𝔭 M hm
      rw [← hIU] at this
      exact this.1
    · intro m hm
      have : m ∈ locF 𝔭 T := LocF.le_locF 𝔭 T hm
      rw [← hIW] at this
      exact this.1
  · rintro x ⟨b, hb, y, hy, c, hcy, hU, hPc⟩
    obtain ⟨z, hz, hzb⟩ := hG₀.oW b b.2
    have hyN : y ∈ locF 𝔭 N₀ := hΛ₀ ▸ hy
    have hzN : z ∈ locF 𝔭 N₀ := hΛ₀ ▸ hz
    have ex : x = y - prO hc.symm y + prO hc.symm z := by
      have e3 : prO hc y = y - prO hc.symm y := eq_sub_of_add_eq (prO_add hc y)
      calc x = prO hc x + prO hc.symm x := (prO_add hc x).symm
        _ = prO hc y + prO hc.symm z := by rw [hU, hzb, hb]
        _ = _ := by rw [e3]
    rw [ex]
    refine Submodule.add_mem _ (Submodule.sub_mem _ ?_ ?_) ?_
    · exact LocF.locF_mono 𝔭 le_sup_left hyN
    · exact LocF.locF_mono 𝔭 le_sup_right (prO_symm_locF (hc := hc) hp hyN)
    · exact LocF.locF_mono 𝔭 le_sup_right (prO_symm_locF (hc := hc) hp hzN)

def isoOf (hG₀ : Good hc M T 𝔭 Λ₀) (hG : Good hc M T 𝔭 Λ) :
    Module.End (𝓞 K) (DiscMod h (orthK h U) T 𝔭) :=
  ((gam hG₀).symm.trans (gam hG)).toLinearMap

theorem isoOf_mk (hG₀ : Good hc M T 𝔭 Λ₀) (hG : Good hc M T 𝔭 Λ) {y w : V} (hy : y ∈ Λ₀) (hw : w ∈ Λ)
    (hwU : prO hc w = prO hc y) :
    isoOf hG₀ hG (Submodule.Quotient.mk ⟨prO hc.symm y, hG₀.iW y hy⟩) =
      Submodule.Quotient.mk ⟨prO hc.symm w, hG.iW w hw⟩ := by
  have key : ∀ {Λ' : Submodule (𝓞 K) V} (hG' : Good hc M T 𝔭 Λ') (b : Λ'),
      gam hG' (toDisc h hc M Λ' 𝔭 hG'.iU b) = toDisc h hc.symm T Λ' 𝔭 hG'.iW b := by
    intro Λ' hG' b
    unfold gam
    simp only [LinearEquiv.trans_apply]
    rw [← LinearMap.quotKerEquivOfSurjective_apply_mk (toDisc h hc M Λ' 𝔭 hG'.iU)
        (toDisc_surj h hc M Λ' 𝔭 hG'.iU hG'.oU) b, LinearEquiv.symm_apply_apply,
      Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk]
  have h1 : (Submodule.Quotient.mk ⟨prO hc.symm y, hG₀.iW y hy⟩ : DiscMod h (orthK h U) T 𝔭) =
      gam hG₀ (toDisc h hc M Λ₀ 𝔭 hG₀.iU ⟨y, hy⟩) := (key hG₀ ⟨y, hy⟩).symm
  have h2 : toDisc h hc M Λ₀ 𝔭 hG₀.iU ⟨y, hy⟩ = toDisc h hc M Λ 𝔭 hG.iU ⟨w, hw⟩ :=
    congrArg Submodule.Quotient.mk (Subtype.ext hwU.symm)
  unfold isoOf
  rw [h1]
  simp only [LinearEquiv.coe_coe, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  rw [h2]
  exact key hG ⟨w, hw⟩

end Formalism.L2.SG.Pf.OrthogonalProjections
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.MemWOfPrOZero =====

-- ===== clump member: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.ImportsBis =====
-- clump-header: {"m": "Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.ImportsBis", "h": "module\n\npublic import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.MemWOfPrOZero\nimport Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DualLeGlue\nimport Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.ExistsLatticeLocF\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.OrthogonalProjections

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G6 Formalism.L2.SG.Pf.ProjectionDiscriminantModule

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V} {hc : IsCompl U (orthK h U)}
  {M T Λ₀ : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)}

theorem card_eq [FiniteDimensional K V] (hs : h.IsSymm) (h𝔭 : 𝔭.IsMaximal) (hM : IsLatIn U M)
    (hT : IsLatIn (orthK h U) T) (hgood : ∀ Λ, InFib h U 𝔭 M T Λ → Good hc M T 𝔭 Λ)
    (h0 : InFib h U 𝔭 M T Λ₀) :
    Nat.card {Λ // InFib h U 𝔭 M T Λ} =
      Nat.card {P : Module.End (𝓞 K) (DiscMod h (orthK h U) T 𝔭) // FP P} := by
  classical
  have G0 : Good hc M T 𝔭 Λ₀ := hgood Λ₀ h0
  have hd₀ : dualF h 𝔭 Λ₀ = Λ₀ := h0.2.1

  have hTW : ∀ {d : V}, d ∈ locF 𝔭 T → d ∈ orthK h U := by
    intro d hd
    have : d ∈ Λ₀ ⊓ (orthK h U).restrictScalars (𝓞 K) := by rw [G0.cW]; exact hd
    exact this.2
  have hTL : ∀ {Λ : Submodule (𝓞 K) V}, Good hc M T 𝔭 Λ → ∀ {d : V}, d ∈ locF 𝔭 T → d ∈ Λ := by
    intro Λ hG d hd
    have : d ∈ Λ ⊓ (orthK h U).restrictScalars (𝓞 K) := by rw [hG.cW]; exact hd
    exact this.1
  have hsW : ∀ {d : V}, d ∈ orthK h U → prO hc.symm d = d := fun hd =>
    (mem_W_of_prO_zero (hc := hc) (orth_projection_of_mem_compl hd)).2

  have hFP : ∀ Λ (hΛ : InFib h U 𝔭 M T Λ), FP (isoOf G0 (hgood Λ hΛ)) := by
    intro Λ hΛ
    have hG := hgood Λ hΛ
    refine fp_of (hc := hc) hs hd₀ hΛ.2.1 _ ?_
    intro b x' hx'
    obtain ⟨z, hz, hzb⟩ := G0.oW b b.2
    obtain ⟨w, hw, hwz⟩ := hG.oU (prO hc z) (G0.iU z hz)
    have hb : b = ⟨prO hc.symm z, G0.iW z hz⟩ := Subtype.ext hzb.symm
    rw [hb, isoOf_mk G0 hG hz hw hwz, Submodule.Quotient.eq, Submodule.mem_comap] at hx'
    have hd : (x' : V) - prO hc.symm w ∈ locF 𝔭 T := by simpa using hx'
    have hdW := hTW hd
    refine ⟨z, hz, w + ((x' : V) - prO hc.symm w), Λ.add_mem hw (hTL hG hd), hzb, ?_, ?_⟩
    · rw [map_add (f := _), hsW hdW]; abel
    · rw [map_add (f := _), orth_projection_of_mem_compl hdW, add_zero, hwz]
  have hglue : ∀ P, FP P → InFib h U 𝔭 M T (glue hc T 𝔭 Λ₀ P) := by
    intro P hP
    obtain ⟨N₀, hN₀, hloc⟩ := h0.1
    haveI : Finite (DiscMod h (orthK h U) T 𝔭) :=
      Formalism.L2.SG.Pf.ProjectionDiscriminantModule.discMod_finite hc h𝔭 hM hT hN₀ hloc G0.cW G0.iW G0.oW
    exact glue_mem hs h𝔭 hM hT G0 h0 hP (Finite.surjective_of_injective (FP.injective G0 hd₀ hP))
  have hleft : ∀ Λ (hΛ : InFib h U 𝔭 M T Λ), glue hc T 𝔭 Λ₀ (isoOf G0 (hgood Λ hΛ)) = Λ := by
    intro Λ hΛ
    have hG := hgood Λ hΛ
    ext x
    constructor
    · rintro ⟨b, hb, y, hy, c, hcy, hU, hP⟩
      obtain ⟨w, hw, hwy⟩ := hG.oU (prO hc y) (G0.iU y hy)
      have hc' : c = ⟨prO hc.symm y, G0.iW y hy⟩ := Subtype.ext hcy
      rw [hc', isoOf_mk G0 hG hy hw hwy, Submodule.Quotient.eq, Submodule.mem_comap] at hP
      have hd : (b : V) - prO hc.symm w ∈ locF 𝔭 T := by simpa using hP
      rw [hb] at hd
      exact mem_of_proj hG hw (hwy.trans hU) hd
    · intro hx
      obtain ⟨y, hy, hyx⟩ := G0.oU (prO hc x) (hG.iU x hx)
      exact ⟨⟨prO hc.symm x, hG.iW x hx⟩, rfl, y, hy, ⟨prO hc.symm y, G0.iW y hy⟩, rfl, hyx,
        (isoOf_mk G0 hG hy hx hyx.symm).symm⟩
  have hright : ∀ P (hP : FP P), isoOf G0 (hgood _ (hglue P hP)) = P := by
    intro P hP
    have hG := hgood _ (hglue P hP)
    refine LinearMap.ext fun q => ?_
    induction q using Submodule.Quotient.induction_on with
    | _ c =>
    obtain ⟨y, hy, hyc⟩ := G0.oW c c.2
    have hc' : c = ⟨prO hc.symm y, G0.iW y hy⟩ := Subtype.ext hyc.symm
    obtain ⟨x', hx'⟩ := Submodule.Quotient.mk_surjective _ (P (Submodule.Quotient.mk c))
    rw [hc'] at hx' ⊢
    have hmem := mem_glue_of (P := P) G0 hy x' hx'
    have hx'W : (x' : V) ∈ orthK h U := memW G0 x'.2
    have hUeq : prO hc (prO hc y + x') = prO hc y := by
      rw [map_add (f := _), prO_of_mem_U (prO_mem hc y), orth_projection_of_mem_compl hx'W, add_zero]
    rw [isoOf_mk G0 hG hy hmem hUeq, ← hx']
    congr 1
    apply Subtype.ext
    have e := prO_add hc (prO hc y)
    rw [prO_of_mem_U (prO_mem hc y)] at e
    have e0 : prO hc.symm (prO hc y) = 0 := by
      have := congrArg (fun v => v - prO hc y) e
      simpa using this
    simp only [map_add (f := _), e0, zero_add, hsW hx'W]
  exact Nat.card_congr
    { toFun := fun Λ => ⟨isoOf G0 (hgood Λ.1 Λ.2), hFP Λ.1 Λ.2⟩
      invFun := fun P => ⟨glue hc T 𝔭 Λ₀ P.1, hglue P.1 P.2⟩
      left_inv := fun Λ => Subtype.ext (hleft Λ.1 Λ.2)
      right_inv := fun P => Subtype.ext (hright P.1 P.2) }

end Formalism.L2.SG.Pf.OrthogonalProjections
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.ImportsBis =====

-- ===== clump member: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.OrthogonalProjections =====
-- clump-header: {"m": "Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.OrthogonalProjections", "h": "module\n\npublic import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.BigLineBundleMoriwaki\npublic import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.ImportsBis\nimport Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.ProjectionIntoHolds\npublic import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.SummandLocalization\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\npublic import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.FormMemOfDual\npublic import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.RieszHermitianHolds\n\n"}
section -- clump:auto
@[expose] public section

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.Cnt

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.G6 Formalism.L2.SG.Pf.OrthogonalProjections

theorem fibre_counting_holds : FibCount := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hnd U hcU M T hM hT 𝔭 h𝔭 hne
  have oUW : ∀ x ∈ U, ∀ y ∈ orthK h U, h x y = 0 := fun x hx y hy => h_UW hx hy
  have oWU : ∀ x ∈ orthK h U, ∀ y ∈ U, h x y = 0 := fun x hx y hy => h_WU hs hx hy
  have hO := projOnto_of summand_localization riesz_hermitian_holds
  have hgood : ∀ Λ, InFib h U 𝔭 M T Λ → Good hcU M T 𝔭 Λ := fun Λ hΛ =>
    { iU := projection_into_holds K F V hK hF h hs hnd U (orthK h U) hcU oUW M hM 𝔭 h𝔭 Λ hΛ.1 hΛ.2.1 hΛ.2.2.1
      iW := projection_into_holds K F V hK hF h hs hnd (orthK h U) U hcU.symm oWU T hT 𝔭 h𝔭 Λ hΛ.1 hΛ.2.1
        hΛ.2.2.2
      oU := hO K F V hK hF h hs hnd U (orthK h U) hcU oUW M hM 𝔭 h𝔭 Λ hΛ.1 hΛ.2.1 hΛ.2.2.1
      oW := hO K F V hK hF h hs hnd (orthK h U) U hcU.symm oWU T hT 𝔭 h𝔭 Λ hΛ.1 hΛ.2.1 hΛ.2.2.2
      cU := hΛ.2.2.1
      cW := hΛ.2.2.2 }
  obtain ⟨⟨⟨Λ₀, h0⟩⟩, -⟩ := Nat.card_ne_zero.mp hne
  exact card_eq hs h𝔭 hM hT hgood h0

end Formalism.L2.SG.Pf.Cnt
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.OrthogonalProjections =====

-- ===== clump member: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.LocalGluingHolds =====
-- clump-header: {"m": "Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.LocalGluingHolds", "h": "module\n\npublic import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.JordanExists\npublic import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.GlueLocOfFibCount\npublic import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.OrthogonalProjections\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

namespace Formalism.L2.SG.Pf.Cnt

open Formalism.L2.SG.Pf.G6

theorem local_gluing_holds : GlueLoc :=
  glueLoc_of_fibCount fibre_counting_holds

end Formalism.L2.SG.Pf.Cnt
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.LocalGluingHolds =====
