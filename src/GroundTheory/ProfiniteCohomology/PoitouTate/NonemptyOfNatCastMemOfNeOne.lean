import Mathlib
import GroundTheory.ProfiniteCohomology.PoitouTate.RealCup
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseCores
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseFormal
import GroundTheory.ProfiniteCohomology.PoitouTate.PoitouTateNineTermGs
import GroundTheory.ProfiniteCohomology.PoitouTate.RealAbstract
import GroundTheory.ProfiniteCohomology.PoitouTate.RealOdd
import GroundTheory.ProfiniteCohomology.RealPlaces.VanishingUnitsDiv
import GroundTheory.ProfiniteCohomology.RealPlaces.Vanishing
import GroundTheory.ProfiniteCohomology.RealPlaces.Devissage

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory Limits

attribute [local instance 2000] Rep.hV2

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {ι : Type} {Hv : ι → Type} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
  [∀ v, IsTopologicalGroup (Hv v)] [∀ v, CompactSpace (Hv v)] (φ : ∀ v, Hv v →ₜ* G)
  {κ : Type} {F : κ → Type} [∀ w, Group (F w)] [∀ w, TopologicalSpace (F w)]
  [∀ w, IsTopologicalGroup (F w)] [∀ w, Fintype (F w)] (ψ : ∀ w, F w →ₜ* G)
  (U : OpenSubgroup G) (hU : FreeOnCosets ψ (U : Subgroup G))

section Shapiro

theorem tateCoindIso_tateCompactCupRes {N₁ N₂ N₃ : Rep (ULift.{0} ℤ) (U : Subgroup G)} [IsDiscreteRep N₁]
    [IsDiscreteRep N₂] [IsDiscreteRep N₃] (μ : N₁ ⊗ N₂ ⟶ N₃) {a r b : ℕ} (h : (a + 1) + r = b + 1)
    (y : tateCompactCohomologyRes φ ψ (Rep.coind (U : Subgroup G).subtype N₁) (a + 1))
    (x : cohomology (Rep.coind (U : Subgroup G).subtype N₂) r) :
    (tateCoindIso φ ψ U N₃ hU b).hom.hom (tateCompactCupRes φ ψ (coindPairing (U : Subgroup G) μ) h y x) =
      compactCupRes (mackeyFamily U φ) μ h ((tateCoindIso φ ψ U N₁ hU a).hom.hom y)
        ((shapiroMap U N₂ r).hom x) := by
  rw [tateCoindIso_hom, tateCoindIso_hom]
  change (mackeyCompactCohomologyIso U φ N₃ (b + 1)).hom.hom
      ((tateForget φ ψ _ _ (fun _ => 𝟙 _) _ (fun _ => 𝟙 _) (b + 1)).hom
        (tateCompactCupRes φ ψ (coindPairing (U : Subgroup G) μ) h y x)) =
    compactCupRes (mackeyFamily U φ) μ h ((mackeyCompactCohomologyIso U φ N₁ (a + 1)).hom.hom
      ((tateForget φ ψ _ _ (fun _ => 𝟙 _) _ (fun _ => 𝟙 _) (a + 1)).hom y)) ((shapiroMap U N₂ r).hom x)
  rw [tateForget_tateCompactCupRes]
  exact mackeyCompactCohomologyIso_compactCupRes U φ μ h _ x

theorem tateCompactCores_tateCoindIso_hom (A : Rep (ULift.{0} ℤ) G) [IsDiscreteRep A] (b : ℕ)
    (W : tateCompactCohomologyRes φ ψ
      (Rep.coind (U : Subgroup G).subtype (Rep.res (U : Subgroup G).subtype A)) (b + 1)) :
    (tateCompactCores φ ψ U hU A b).hom
        ((tateCoindIso φ ψ U (Rep.res (U : Subgroup G).subtype A) hU b).hom.hom W) =
      (tateCompactCohomologyResMap φ ψ (coindTrace (U : Subgroup G) A) (b + 1)).hom W := by
  change (tateCompactCohomologyResMap φ ψ (coindTrace (U : Subgroup G) A) (b + 1)).hom
    ((tateCoindIso φ ψ U (Rep.res (U : Subgroup G).subtype A) hU b).inv.hom
      ((tateCoindIso φ ψ U (Rep.res (U : Subgroup G).subtype A) hU b).hom.hom W)) = _
  rw [hom_apply_hom_apply_of_comp_eq (tateCoindIso φ ψ U (Rep.res (U : Subgroup G).subtype A) hU b).hom_inv_id W]
  rfl

end Shapiro

section Coind

variable {n : ℕ} [NeZero n] {D : Rep (ULift.{0} ℤ) G} [IsDiscreteRep D] (hD : ∀ d : D, n • d = 0)

def tateCoindDualCompactMap (s : ℕ) :
    tateCompactCohomologyRes φ ψ
        (dualRep D (Rep.coind (U : Subgroup G).subtype (zmodRep.{0} (U : Subgroup G) n))) (s + 1) →+
      compactCohomologyRes (mackeyFamily U φ) (Rep.res (U : Subgroup G).subtype D) (s + 1) :=
  ((compactCohomologyResMap (mackeyFamily U φ)
      (zmodDualIso n (Rep.res (U : Subgroup G).subtype D) hD).hom (s + 1)).hom.comp
    (((tateCoindIso φ ψ U
      (dualRep (Rep.res (U : Subgroup G).subtype D) (zmodRep.{0} (U : Subgroup G) n)) hU s).hom.hom).comp
      (tateCompactCohomologyResMap φ ψ
        (coindDualInv (U : Subgroup G) (ULift.{0} (ZMod n)) D) (s + 1)).hom)).toAddMonoidHom

theorem tateCoindDualCompactMap_apply (s : ℕ)
    (y : tateCompactCohomologyRes φ ψ
      (dualRep D (Rep.coind (U : Subgroup G).subtype (zmodRep.{0} (U : Subgroup G) n))) (s + 1)) :
    tateCoindDualCompactMap φ ψ U hU hD s y =
      (compactCohomologyResMap (mackeyFamily U φ)
        (zmodDualIso n (Rep.res (U : Subgroup G).subtype D) hD).hom (s + 1)).hom
        ((tateCoindIso φ ψ U
          (dualRep (Rep.res (U : Subgroup G).subtype D) (zmodRep.{0} (U : Subgroup G) n)) hU s).hom.hom
          ((tateCompactCohomologyResMap φ ψ
            (coindDualInv (U : Subgroup G) (ULift.{0} (ZMod n)) D) (s + 1)).hom y)) :=
  rfl

theorem bijective_tateCoindDualCompactMap (s : ℕ) :
    Function.Bijective (tateCoindDualCompactMap φ ψ U hU hD s) := by
  have h1 := bijective_compactCohomologyResMap_of_comp_eq_id (mackeyFamily U φ)
    (zmodDualIso n (Rep.res (U : Subgroup G).subtype D) hD).hom
    (zmodDualIso n (Rep.res (U : Subgroup G).subtype D) hD).inv (Iso.hom_inv_id _)
    (Iso.inv_hom_id _) (s + 1)
  have h2 : Function.Bijective (tateCoindIso φ ψ U
      (dualRep (Rep.res (U : Subgroup G).subtype D) (zmodRep.{0} (U : Subgroup G) n)) hU s).hom.hom :=
    Function.bijective_iff_has_inverse.2 ⟨(tateCoindIso φ ψ U _ hU s).inv.hom,
      fun w => hom_apply_hom_apply_of_comp_eq (tateCoindIso φ ψ U _ hU s).hom_inv_id w,
      fun w => hom_apply_hom_apply_of_comp_eq (tateCoindIso φ ψ U _ hU s).inv_hom_id w⟩
  have h3 := bijective_tateCompactCohomologyResMap_of_comp_eq_id φ ψ
    (coindDualInv (U : Subgroup G) (ULift.{0} (ZMod n)) D)
    (coindDualHom (U : Subgroup G) (ULift.{0} (ZMod n)) D)
    (coindDualInv_comp_coindDualHom _ _ _) (coindDualHom_comp_coindDualInv _ _ _) (s + 1)
  exact h1.comp (h2.comp h3)

abbrev tateCoresTrace (t : tateCompactCohomologyRes φ ψ D 3 →+ ZMod n) :
    compactCohomologyRes (mackeyFamily U φ) (Rep.res (U : Subgroup G).subtype D) 3 →+ ZMod n :=
  t.comp (tateCompactCores φ ψ U hU D 2).hom.toAddMonoidHom

theorem tateCompactDualityMap_coind (t : tateCompactCohomologyRes φ ψ D 3 →+ ZMod n) {r s : ℕ}
    (h : r + (s + 1) = 3)
    (x : cohomology (Rep.coind (U : Subgroup G).subtype (zmodRep.{0} (U : Subgroup G) n)) r)
    (y : tateCompactCohomologyRes φ ψ
      (dualRep D (Rep.coind (U : Subgroup G).subtype (zmodRep.{0} (U : Subgroup G) n))) (s + 1)) :
    tateCompactDualityMap φ ψ D h t
        (Rep.coind (U : Subgroup G).subtype (zmodRep.{0} (U : Subgroup G) n)) x y =
      compactZmodDualityMap (mackeyFamily U φ) (Rep.res (U : Subgroup G).subtype D) hD
        (tateCoresTrace φ ψ U hU t) h ((shapiroMap U (zmodRep.{0} (U : Subgroup G) n) r).hom x)
        (tateCoindDualCompactMap φ ψ U hU hD s y) := by
  have hy : (tateCompactCohomologyResMap φ ψ (coindDualHom (U : Subgroup G) (ULift.{0} (ZMod n)) D)
      (s + 1)).hom ((tateCompactCohomologyResMap φ ψ
        (coindDualInv (U : Subgroup G) (ULift.{0} (ZMod n)) D) (s + 1)).hom y) = y := by
    rw [← ConcreteCategory.comp_apply, ← tateCompactCohomologyResMap_comp,
      coindDualInv_comp_coindDualHom, tateCompactCohomologyResMap_id]
    rfl
  have e1 := compactCupRes_compactCohomologyResMap (mackeyFamily U φ)
    (zmodMulPairingRight n (Rep.res (U : Subgroup G).subtype D) hD)
    (dualEvalPairing (Rep.res (U : Subgroup G).subtype D) (zmodRep.{0} (U : Subgroup G) n))
    (zmodDualIso n (Rep.res (U : Subgroup G).subtype D) hD).hom (𝟙 _)
    (by rw [tensorHom_zmodDualIso_zmodMulPairingRight, MonoidalCategory.id_tensorHom_id,
      Category.id_comp]) ((Nat.add_comm (s + 1) r).trans h)
    ((tateCoindIso φ ψ U
      (dualRep (Rep.res (U : Subgroup G).subtype D) (zmodRep.{0} (U : Subgroup G) n)) hU s).hom.hom
      ((tateCompactCohomologyResMap φ ψ
        (coindDualInv (U : Subgroup G) (ULift.{0} (ZMod n)) D) (s + 1)).hom y))
    ((shapiroMap U (zmodRep.{0} (U : Subgroup G) n) r).hom x)
  rw [cohomologyMap_id, ModuleCat.hom_id, LinearMap.id_apply] at e1
  have e2 := tateCoindIso_tateCompactCupRes φ ψ U hU
    (dualEvalPairing (Rep.res (U : Subgroup G).subtype D) (zmodRep.{0} (U : Subgroup G) n))
    (b := 2) ((Nat.add_comm (s + 1) r).trans h)
    ((tateCompactCohomologyResMap φ ψ
        (coindDualInv (U : Subgroup G) (ULift.{0} (ZMod n)) D) (s + 1)).hom y) x
  have e3 := tateCompactCores_tateCoindIso_hom φ ψ U hU D 2
    (tateCompactCupRes φ ψ (coindPairing (U : Subgroup G)
      (dualEvalPairing (Rep.res (U : Subgroup G).subtype D) (zmodRep.{0} (U : Subgroup G) n)))
      ((Nat.add_comm (s + 1) r).trans h)
      ((tateCompactCohomologyResMap φ ψ
        (coindDualInv (U : Subgroup G) (ULift.{0} (ZMod n)) D) (s + 1)).hom y) x)
  rw [tateCompactDualityMap_apply, compactZmodDualityMap_apply, tateCoindDualCompactMap_apply, e1, ← e2]
  refine Eq.trans (congrArg t ?_) (congrArg t e3).symm
  conv_lhs => rw [← hy]
  rw [tateCompactCupRes_tateCompactCohomologyResMap φ ψ _
    ((coindDualHom (U : Subgroup G) (ULift.{0} (ZMod n)) D ⊗ₘ
      𝟙 (Rep.coind (U : Subgroup G).subtype (zmodRep.{0} (U : Subgroup G) n))) ≫
      dualEvalPairing D (Rep.coind (U : Subgroup G).subtype (zmodRep.{0} (U : Subgroup G) n)))
    _ (𝟙 _) (by rw [MonoidalCategory.id_tensorHom_id, Category.id_comp]), cohomologyMap_id,
    tensorHom_coindDualHom_dualEvalPairing, ← tateCompactCohomologyResMap_tateCompactCupRes]
  rfl

theorem bijective_tateCompactDualityMap_coind (t : tateCompactCohomologyRes φ ψ D 3 →+ ZMod n) {r s : ℕ}
    (h : r + (s + 1) = 3)
    (hb : Function.Bijective (compactZmodDualityMap (mackeyFamily U φ) (Rep.res (U : Subgroup G).subtype D)
      hD (tateCoresTrace φ ψ U hU t) h)) :
    Function.Bijective (tateCompactDualityMap φ ψ D h t
      (Rep.coind (U : Subgroup G).subtype (zmodRep.{0} (U : Subgroup G) n))) := by
  have hsh : Function.Bijective (shapiroMap U (zmodRep.{0} (U : Subgroup G) n) r) :=
    Function.bijective_iff_has_inverse.2 ⟨inv (shapiroMap U _ r), inv_shapiroMap_apply U r,
      shapiroMap_inv_apply U r⟩
  exact bijective_of_bijective_comp hb hsh (bijective_tateCoindDualCompactMap φ ψ U hU hD s)
    (tateCompactDualityMap_coind φ ψ U hU hD t h)

end Coind

section Cores

theorem surjective_tateCompactCores_three (D : Rep (ULift.{0} ℤ) G) [IsDiscreteRep D] [Finite D] {n : ℕ}
    (hD : ∀ d : D, n • d = 0)
    (hV : ∀ (M : Rep (ULift.{0} ℤ) G) [IsDiscreteRep M] [Finite M], (∀ m : M, n • m = 0) →
      Subsingleton (tateCompactCohomologyRes φ ψ M 4)) :
    Function.Surjective (tateCompactCores φ ψ U hU D 2).hom := by
  have hS := coindTraceShortComplex_shortExact (U : Subgroup G) D
  have : IsDiscreteRep (coindTraceShortComplex (U : Subgroup G) D).X₂ :=
    inferInstanceAs (IsDiscreteRep (Rep.coind (U : Subgroup G).subtype (Rep.res (U : Subgroup G).subtype D)))
  have : IsDiscreteRep (coindTraceShortComplex (U : Subgroup G) D).X₁ :=
    isDiscreteRep_subrepresentation _ _ _
  have : IsDiscreteRep (coindTraceShortComplex (U : Subgroup G) D).X₃ := inferInstanceAs (IsDiscreteRep D)
  have : Finite (Rep.res (U : Subgroup G).subtype D) := inferInstanceAs (Finite D)
  have : Finite (Rep.coind (U : Subgroup G).subtype (Rep.res (U : Subgroup G).subtype D)) :=
    finite_coind U _
  have : Finite (coindTraceShortComplex (U : Subgroup G) D).X₁ :=
    inferInstanceAs (Finite (coindTraceKer (U : Subgroup G) D))
  have hN : ∀ m : (coindTraceShortComplex (U : Subgroup G) D).X₁, n • m = 0 := fun m =>
    Subtype.ext (Subtype.ext (funext fun x => hD _))
  have h4 := hV _ hN
  have hg : Function.Surjective
      (tateCompactCohomologyResMap φ ψ (coindTrace (U : Subgroup G) D) 3).hom := fun y =>
    (ShortComplex.moduleCat_exact_iff_ker_sub_range _).1 (tateCompactRes_exact₃ φ ψ hS 3)
      (@Subsingleton.elim _ h4 _ _)
  intro y
  refine (hg y).elim fun x hx => ⟨(tateCoindIso φ ψ U (Rep.res (U : Subgroup G).subtype D) hU 2).hom.hom x, ?_⟩
  exact (tateCompactCores_tateCoindIso_hom φ ψ U hU D 2 x).trans hx

end Cores

end GroundTheory.ProfCoh
end
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open IsDedekindDomain NumberField CategoryTheory MonoidalCategory GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

attribute [local instance 2000] Rep.hV2

section Algebra

theorem bijective_of_surjective_of_surjective_dual {A : Type*} [AddCommGroup A] {n : ℕ} [NeZero n]
    (hA : ∀ a : A, n • a = 0) (T : A →+ ZMod n) (hT : Function.Surjective T)
    (e : ZMod n → (A →+ ZMod n)) (he : Function.Surjective e) : Function.Bijective T := by
  have : Finite (A →+ ZMod n) := Finite.of_surjective e he
  have : Finite A := finite_of_finite_addMonoidHom_zmod hA
  let ev : A → ((A →+ ZMod n) →+ ZMod n) := fun a =>
    { toFun := fun χ => χ a
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hev : Function.Injective ev := by
    intro a b hab
    by_contra hne
    obtain ⟨χ, hχ⟩ := zmod_exists_apply_ne_zero hA (sub_ne_zero.2 hne)
    apply hχ
    rw [map_sub, sub_eq_zero]
    exact DFunLike.congr_fun hab χ
  have h1 : Nat.card A ≤ Nat.card ((A →+ ZMod n) →+ ZMod n) := Nat.card_le_card_of_injective ev hev
  have h2 : Nat.card ((A →+ ZMod n) →+ ZMod n) ≤ Nat.card (A →+ ZMod n) :=
    card_addMonoidHom_zmod_le (n := n) (A := A →+ ZMod n)
  have h3 : Nat.card (A →+ ZMod n) ≤ Nat.card (ZMod n) := Nat.card_le_card_of_surjective e he
  exact hT.bijective_of_nat_card_le (h1.trans (h2.trans h3))

end Algebra

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type} {Hv : ι → Type} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
  [∀ v, IsTopologicalGroup (Hv v)] (φ : ∀ v, Hv v →ₜ* G)
  {n : ℕ} [NeZero n] {D : Rep (ULift.{0} ℤ) G} [IsDiscreteRep D] (hD : ∀ d : D, n • d = 0)
  [IsDiscreteRep (dualRep D (zmodRep.{0} G n))]

omit [TopologicalSpace G] [IsTopologicalGroup G] [NeZero n] [IsDiscreteRep D]
  [IsDiscreteRep (dualRep D (zmodRep.{0} G n))] in

theorem tensorHom_zmodDualIso_inv_dualEvalPairing :
    ((zmodDualIso n D hD).inv ⊗ₘ 𝟙 (zmodRep.{0} G n)) ≫ dualEvalPairing D (zmodRep.{0} G n) =
      (𝟙 D ⊗ₘ 𝟙 (zmodRep.{0} G n)) ≫ zmodMulPairingRight n D hD := by
  rw [← tensorHom_zmodDualIso_zmodMulPairingRight D hD, ← Category.assoc,
    MonoidalCategory.tensorHom_comp_tensorHom, Iso.inv_hom_id, Category.comp_id]

omit [NeZero n] in

theorem compactZmodDualityMap_eq_compactDualityMap {m r s : ℕ}
    (T : compactCohomologyRes φ D m →+ ZMod n) (h : r + s = m) (x : cohomology (zmodRep.{0} G n) r)
    (y : compactCohomologyRes φ D s) :
    compactZmodDualityMap φ D hD T h x y =
      compactDualityMap φ D h T (zmodRep.{0} G n) x
        ((compactCohomologyResMap φ (zmodDualIso n D hD).inv s).hom y) := by
  have e := compactCupRes_compactCohomologyResMap φ (dualEvalPairing D (zmodRep.{0} G n))
    (zmodMulPairingRight n D hD) (zmodDualIso n D hD).inv (𝟙 _)
    (tensorHom_zmodDualIso_inv_dualEvalPairing hD) ((Nat.add_comm s r).trans h) y x
  rw [cohomologyMap_id, ModuleCat.hom_id, LinearMap.id_apply] at e
  rw [compactZmodDualityMap_apply, compactDualityMap_apply, e]

theorem bijective_compactZmodDualityMap_of_compactDualityMap {m r s : ℕ}
    (T : compactCohomologyRes φ D m →+ ZMod n) (h : r + s = m)
    (hb : Function.Bijective (compactDualityMap φ D h T (zmodRep.{0} G n))) :
    Function.Bijective (compactZmodDualityMap φ D hD T h) :=
  bijective_of_bijective_comp hb Function.bijective_id
    (bijective_compactCohomologyResMap_of_comp_eq_id φ (zmodDualIso n D hD).inv (zmodDualIso n D hD).hom
      (Iso.inv_hom_id _) (Iso.hom_inv_id _) s)
    (γ := (compactCohomologyResMap φ (zmodDualIso n D hD).inv s).hom.toAddMonoidHom)
    fun x y => compactZmodDualityMap_eq_compactDualityMap φ hD T h x y

end Generic

section Level

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1))) [Fintype S]
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))
  {N : ℕ} [NeZero N] (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((N : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
  (hK : Odd N ∨ IsTotallyComplex K.1)

set_option synthInstance.maxHeartbeats 400000 in
include hS in

theorem bijective_gs_compactZmodDualityMap_of_duality {r s : ℕ} (h : r + s = 3) :
    Function.Bijective (compactZmodDualityMap (gsFinFamily S ιs) (gsRoots S N) (nsmul_gsRoots S N)
      (gsCompactInv S ιs N hK (subsingleton_cohomology_three_gsRoots S hS hK)) h) := by
  have : IsDiscreteRep (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) N) := isDiscreteRep_of_isTrivial _
  have : IsDiscreteRep (dualRep (gsRoots S N) (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) N)) :=
    isDiscreteRep_dualRep _ _
  exact bijective_compactZmodDualityMap_of_compactDualityMap (gsFinFamily S ιs) (nsmul_gsRoots S N) _ h
    (poitouTate_duality_gs S ιs hS hK (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) N)
      (nsmul_zmodRep_eq_zero _ N) h)

include hS in

theorem bijective_gsCompactInv_of_duality [Nonempty S] :
    Function.Bijective (gsCompactInv S ιs N hK (subsingleton_cohomology_three_gsRoots S hS hK)) :=
  bijective_of_surjective_of_surjective_dual
    (nsmul_compactCohomologyRes_eq_zero (gsFinFamily S ιs) (nsmul_gsRoots S N) 3) _
    (surjective_gsCompactInv S N ιs hK (subsingleton_cohomology_three_gsRoots S hS hK) fun v =>
      (bijective_gsLocalInvRoots_of_places S ιs N (fun v hv h => hv (hS v h)) v).2)
    (fun a => compactZmodDualityMap (gsFinFamily S ιs) (gsRoots S N) (nsmul_gsRoots S N)
      (gsCompactInv S ιs N hK (subsingleton_cohomology_three_gsRoots S hS hK)) (show 0 + 3 = 3 from rfl)
      (zmodH0Class a))
    ((bijective_gs_compactZmodDualityMap_of_duality S ιs hS hK (show 0 + 3 = 3 from rfl)).2.comp
      (zmodH0Class_surjective (H := galUnramifiedOutside K.1 ℚ̄ S) (n := N)))

include hS in

theorem gsLevelBijective_gsCompactInv [Nonempty S] :
    GsLevelBijective (gsCompactInv S ιs N hK (subsingleton_cohomology_three_gsRoots S hS hK)) :=
  ⟨bijective_gsCompactInv_of_duality S ιs hS hK, fun h => bijective_gs_compactZmodDualityMap_of_duality S ιs hS hK h⟩

end Level

section OpenSubgroup

variable {K L : FiniteSubfield} [Fact (K ≤ L)] (S : Set (HeightOneSpectrum (𝓞 K.1)))
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))
  (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S) (n : ℕ) [NeZero n]

set_option maxHeartbeats 3200000 in

theorem bijective_compactZmodDualityMap_gsOpenSubgroup_of_surjective
    (τ : compactCohomologyRes (mackeyFamily (gsOpenSubgroup S hL) (gsFinFamily S ιs))
      (Rep.res (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype (gsRoots S n)) 3 →+ ZMod n)
    (hτ : Function.Surjective τ)
    (TL : compactCohomologyRes (gsFinFamily (placesOver S) (gsMackeyEmbeddings hL ιs))
      (gsRoots (K := L) (placesOver S) n) 3 →+ ZMod n) (hLev : GsLevelBijective TL) {r s : ℕ} (h : r + s = 3) :
    Function.Bijective (compactZmodDualityMap (mackeyFamily (gsOpenSubgroup S hL) (gsFinFamily S ιs))
      (Rep.res (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype (gsRoots S n))
      (nsmul_gsRoots S n) τ h) := by
  have hTL := hLev.1
  let f := (gsRootsOfUnityIso S hL n).symm
  let eW := (gsMackeyCompactIso hL ιs f 3).toLinearEquiv.toAddEquiv
  let eY := (gsMackeyCompactIso hL ιs f s).toLinearEquiv.toAddEquiv
  let eX := (cohomologyIsoOfContinuousMulEquiv (gsBaseChange S hL) (zmodRepResIso (gsBaseChange S hL) n) r).toLinearEquiv.toAddEquiv
  have hex := exists_isUnit_mul_of_surjective_of_bijective τ (TL.comp eW.symm.toAddMonoidHom) hτ
    (hTL.comp eW.symm.bijective)
  exact hex.elim fun c hcf => hcf.elim fun hc hfc => bijective_of_transport
    (bilinAddHom (compactCupRes (gsFinFamily (placesOver S) (gsMackeyEmbeddings hL ιs))
      (zmodMulPairingRight n (gsRoots (K := L) (placesOver S) n) (nsmul_gsRoots (K := L) (placesOver S) n))
      ((Nat.add_comm s r).trans h)))
    (bilinAddHom (compactCupRes (mackeyFamily (gsOpenSubgroup S hL) (gsFinFamily S ιs))
      (zmodMulPairingRight n (Rep.res (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype
        (gsRoots S n)) (nsmul_gsRoots S n)) ((Nat.add_comm s r).trans h)))
    TL _ eX eY eW
    (fun y x => (gsMackeyCompactIso_compactCupRes_zmod hL ιs n (nsmul_gsRoots (K := L) (placesOver S) n)
      (nsmul_gsRoots S n) f ((Nat.add_comm s r).trans h) y x).symm)
    c hc (fun w => (hfc _).trans (congrArg (c * TL ·) (eW.symm_apply_apply w))) (hLev.2 h)

end OpenSubgroup

end

end GroundTheory.ProfCoh
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open IsDedekindDomain NumberField CategoryTheory GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

attribute [local instance 2000] Rep.hV2

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
  (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))
  (N : ℕ) [NeZero N]

theorem gsRealInvRootsQZ_ptRes (w : {v : InfinitePlace K.1 // v.IsReal}) (x : cohomology (gsRoots S N) 2) :
    gsRealInvRootsQZ S ιr N w (ptRes (gsRealFamily S ιr) (gsRoots S N) w 2 x) =
      placeInv (.inl w.1) (realLocalEquiv w 2 ((realUnitsRes S ιr 2 w).hom
        ((cohomologyMap (rootsOfUnityToSUnits S (maxUnramifiedOutside K.1 ℚ̄ S) N) 2).hom x))) := by
  have hmor : 𝟙 _ ≫ gsRealRootsToUnits S ιr N w =
      (Rep.resFunctor (gsRealFamily S ιr w).toMonoidHom).map
        (rootsOfUnityToSUnits S (maxUnramifiedOutside K.1 ℚ̄ S) N) ≫ realUnitsMor S ιr w :=
    Rep.Hom.ext (Representation.IntertwiningMap.ext (LinearMap.ext fun _ => rfl))
  have key : (cohomologyMap (gsRealRootsToUnits S ιr N w) 2).hom
      (ptRes (gsRealFamily S ιr) (gsRoots S N) w 2 x) =
      (realUnitsRes S ιr 2 w).hom
        ((cohomologyMap (rootsOfUnityToSUnits S (maxUnramifiedOutside K.1 ℚ̄ S) N) 2).hom x) :=
    (cohomologyMap_cohomologyMapAlong _ _ _ _ x).trans
      ((congrArg (fun f => (cohomologyMapAlong (gsRealFamily S ιr w).toMonoidHom
        (continuous_toMonoidHom _) f 2).hom x) hmor).trans
        (cohomologyMapAlong_cohomologyMap _ _ _ _ x).symm)
  exact (gsRealInvRootsQZ_apply S ιr N w _).trans
    ((realInv_eq_placeInv w.1 _).trans (congrArg _ (congrArg _ key)))

theorem gsLocalInvRootsQZ_ptRes_eq (v : S) (x : cohomology (gsRoots S N) 2) :
    gsLocalInvRootsQZ S ιs N v (ptRes (gsFinFamily S ιs) (gsRoots S N) v 2 x) =
      placeInv (.inr (v : HeightOneSpectrum (𝓞 K.1))) (brauerLocal (gsLocalEmbeddings S ιs)
        (sUnitsBrauer K S ((cohomologyMap (rootsOfUnityToSUnits S (maxUnramifiedOutside K.1 ℚ̄ S) N) 2).hom x))
        (.inr (v : HeightOneSpectrum (𝓞 K.1)))) := by
  refine (gsLocalInvRootsQZ_cohomologyMapAlong S ιs N v x).trans (Eq.symm ?_)
  refine (congrArg (fun z => placeInv (K := K) (.inr (v : HeightOneSpectrum (𝓞 K.1)))
    (brauerLocal (gsLocalEmbeddings S ιs) z (.inr (v : HeightOneSpectrum (𝓞 K.1)))))
    (sUnitsBrauer_apply K S _)).trans ?_
  refine (congrArg (placeInv (K := K) (.inr (v : HeightOneSpectrum (𝓞 K.1))))
    (brauerLocal_gsBrauerInfl_inr K S _ _ _)).trans ?_
  refine (placeInv_inr_apply _ _).trans ?_
  simp only [gsLocalEmbeddings_fin]

theorem gsRealInvRootsQZ_ptRes_eq (w : {v : InfinitePlace K.1 // v.IsReal}) (x : cohomology (gsRoots S N) 2) :
    gsRealInvRootsQZ S ιr N w (ptRes (gsRealFamily S ιr) (gsRoots S N) w 2 x) =
      placeInv (.inl w.1) (brauerLocal (gsLocalEmbeddings S ιs)
        (sUnitsBrauer K S ((cohomologyMap (rootsOfUnityToSUnits S (maxUnramifiedOutside K.1 ℚ̄ S) N) 2).hom x))
        (.inl w.1)) :=
  (gsRealInvRootsQZ_ptRes S ιr N w x).trans (congrArg (placeInv (K := K) (.inl w.1))
    (realLocalEquiv_realUnitsRes S ιr (gsLocalEmbeddings S ιs) (by norm_num) w _).symm)

omit [NeZero N] in

theorem sum_placeInv_inr_add_sum_placeInv_inl [Fintype S] (ι : LocalEmbeddings K) (z : cohomology (unitsLimitRep K) 2)
    (hz : ∀ v : HeightOneSpectrum (𝓞 K.1), v ∉ S → brauerLocal ι z (.inr v) = 0) :
    ∑ v : S, placeInv (.inr (v : HeightOneSpectrum (𝓞 K.1))) (brauerLocal ι z (.inr (v : HeightOneSpectrum (𝓞 K.1)))) +
      ∑ w : {v : InfinitePlace K.1 // v.IsReal}, placeInv (.inl w.1) (brauerLocal ι z (.inl w.1)) = 0 := by
  classical
  let A : Finset (Place K.1) := Finset.univ.image fun v : S => (Sum.inr (v : HeightOneSpectrum (𝓞 K.1)) : Place K.1)
  let B : Finset (Place K.1) := Finset.univ.image fun w : {v : InfinitePlace K.1 // v.IsReal} =>
    (Sum.inl w.1 : Place K.1)
  have hzT : ∀ p ∉ A ∪ B, placeInv p (brauerLocal ι z p) = 0 := by
    intro p hp
    rcases p with w | v
    · have hw : ¬ w.IsReal := fun h => hp (Finset.mem_union_right _
        (Finset.mem_image.2 ⟨⟨w, h⟩, Finset.mem_univ _, rfl⟩))
      have hc : w.IsComplex := InfinitePlace.not_isReal_iff_isComplex.1 hw
      have : Subsingleton (localGaloisCohomology K 2 (.inl w)) :=
        subsingleton_cohomology_two_of_isComplex w hc
      exact (congrArg (placeInv (.inl w)) (Subsingleton.elim _ 0)).trans (map_zero _)
    · have hv : v ∉ S := fun h => hp (Finset.mem_union_left _
        (Finset.mem_image.2 ⟨⟨v, h⟩, Finset.mem_univ _, rfl⟩))
      rw [hz v hv, map_zero]
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro p hpA hpB
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hpA
    obtain ⟨w, -, hw⟩ := Finset.mem_image.1 hpB
    exact Sum.inl_ne_inr hw
  have hsum : brauerSumInv ι z = ∑ v : S, placeInv (.inr (v : HeightOneSpectrum (𝓞 K.1)))
      (brauerLocal ι z (.inr (v : HeightOneSpectrum (𝓞 K.1)))) +
      ∑ w : {v : InfinitePlace K.1 // v.IsReal}, placeInv (.inl w.1) (brauerLocal ι z (.inl w.1)) := by
    refine (AddMonoidHom.comp_apply _ _ _).trans ?_
    rw [sumPlaceInv_eq_sum_of_placeInv (A ∪ B) _ hzT, Finset.sum_union hdisj,
      Finset.sum_image (fun v _ w _ h => Subtype.ext (Sum.inr_injective h)),
      Finset.sum_image (fun v _ w _ h => Subtype.ext (Sum.inl_injective h))]
  exact hsum.symm.trans (brauerSumInv_eq_zero ι z)

theorem gsReciprocityReal [Fintype S] (x : cohomology (gsRoots S N) 2) :
    ∑ v, gsLocalInvRootsQZ S ιs N v (ptRes (gsFinFamily S ιs) (gsRoots S N) v 2 x) +
      ∑ w, gsRealInvRootsQZ S ιr N w (ptRes (gsRealFamily S ιr) (gsRoots S N) w 2 x) = 0 :=
  (congrArg₂ (· + ·) (Finset.sum_congr rfl fun v _ => gsLocalInvRootsQZ_ptRes_eq S ιs N v x)
    (Finset.sum_congr rfl fun w _ => gsRealInvRootsQZ_ptRes_eq S ιr ιs N w x)).trans
    (sum_placeInv_inr_add_sum_placeInv_inl S (gsLocalEmbeddings S ιs) _
      (fun v hv => brauerLocal_sUnitsBrauer_inr K S _ _ v hv))

def gsSumInvReal [Fintype S] : ptTLocal (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) 2 →+ QZ where
  toFun ξ := ∑ v, gsLocalInvRootsQZ S ιs N v (ξ.1 v) + ∑ w, gsRealInvRootsQZ S ιr N w (ξ.2 w)
  map_zero' := by
    refine (congrArg₂ (· + ·) (Finset.sum_eq_zero fun v _ => map_zero _)
      (Finset.sum_eq_zero fun w _ => map_zero _)).trans (add_zero 0)
  map_add' ξ η := by
    change ∑ v, gsLocalInvRootsQZ S ιs N v (ξ.1 v + η.1 v) + ∑ w, gsRealInvRootsQZ S ιr N w (ξ.2 w + η.2 w) = _
    simp only [map_add, Finset.sum_add_distrib]
    abel

omit [NeZero N] in
theorem gsSumInvReal_apply [Fintype S] (ξ : ptTLocal (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) 2) :
    gsSumInvReal S ιr ιs N ξ =
      ∑ v, gsLocalInvRootsQZ S ιs N v (ξ.1 v) + ∑ w, gsRealInvRootsQZ S ιr N w (ξ.2 w) :=
  rfl

theorem gsSumInvReal_eq_zero_of [Fintype S] (ξ : ptTLocal (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) 2)
    (hξ : (ptTLocalToCompact (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) 2).hom ξ = 0) :
    gsSumInvReal S ιr ιs N ξ = 0 := by
  have e := ptTExact_local (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) 1
  have e2 := (e ξ).1 hξ
  obtain ⟨x, hx⟩ := e2
  exact (congrArg (gsSumInvReal S ιr ιs N) hx.symm).trans
    ((congrArg (gsSumInvReal S ιr ιs N) (ptTGlobalToLocal_apply _ _ (gsRoots S N) 2 x)).trans
      (gsReciprocityReal S ιr ιs N x))

end GroundTheory.ProfCoh
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open IsDedekindDomain NumberField CategoryTheory GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

attribute [local instance 2000] Rep.hV2

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
  (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))
  (N : ℕ) [NeZero N] [Fintype S]

theorem exists_gsTraceQZ :
    ∃ χ : tateCompactCohomologyRes (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) 3 →+ QZ,
      χ.comp (ptTLocalToCompact (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) 2).hom.toAddMonoidHom =
        gsSumInvReal S ιr ιs N :=
  QZ.exists_comp_eq_of_ker_le _ _ fun ξ hξ => gsSumInvReal_eq_zero_of S ιr ιs N ξ hξ

def gsTraceQZ : tateCompactCohomologyRes (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) 3 →+ QZ :=
  Classical.choose (exists_gsTraceQZ S ιr ιs N)

theorem gsTraceQZ_comp :
    (gsTraceQZ S ιr ιs N).comp
        (ptTLocalToCompact (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) 2).hom.toAddMonoidHom =
      gsSumInvReal S ιr ιs N :=
  Classical.choose_spec (exists_gsTraceQZ S ιr ιs N)

theorem nsmul_gsTraceQZ
    (z : tateCompactCohomologyRes (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) 3) :
    N • gsTraceQZ S ιr ιs N z = 0 :=
  (map_nsmul (gsTraceQZ S ιr ιs N) N z).symm.trans
    ((congrArg (gsTraceQZ S ιr ιs N) (nsmul_tateCompactCohomologyRes_eq_zero (gsFinFamily S ιs)
      (gsRealFamily S ιr) (nsmul_gsRoots S N) 3 z)).trans (map_zero _))

def gsTrace : tateCompactCohomologyRes (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) 3 →+ ZMod N :=
  zmodOfQZ (gsTraceQZ S ιr ιs N) (nsmul_gsTraceQZ S ιr ιs N)

theorem gsTrace_localToCompact (ξ : ptTLocal (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) 2) :
    zmodToQZ N (gsTrace S ιr ιs N
      ((ptTLocalToCompact (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) 2).hom ξ)) =
      ∑ v, gsLocalInvRootsQZ S ιs N v (ξ.1 v) + ∑ w, gsRealInvRootsQZ S ιr N w (ξ.2 w) :=
  (zmodToQZ_zmodOfQZ _ _ _).trans (DFunLike.congr_fun (gsTraceQZ_comp S ιr ιs N) ξ)

end GroundTheory.ProfCoh
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open IsDedekindDomain NumberField CategoryTheory GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

attribute [local instance 2000] Rep.hV2

theorem isTotallyComplex_of_sq_eq_neg_one {F : Type*} [Field F] (x : F) (hx : x ^ 2 = -1) :
    IsTotallyComplex F := by
  refine ⟨fun w => InfinitePlace.not_isReal_iff_isComplex.1 fun hw => ?_⟩
  have h1 := congrArg (fun f : F →+* ℂ => f x)
    (ComplexEmbedding.isReal_iff.1 (InfinitePlace.isReal_iff.1 hw))
  have h2 : (starRingEnd ℂ) (w.embedding x) = w.embedding x := h1
  obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.1 h2
  have h3 : (w.embedding x) ^ 2 = -1 := by rw [← map_pow, hx, map_neg, map_one]
  rw [hr] at h3
  have h4 : r ^ 2 = -1 := by exact_mod_cast h3
  nlinarith [sq_nonneg r]

section GenericTrace

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type} {Hv : ι → Type} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
  [∀ v, IsTopologicalGroup (Hv v)] (φ : ∀ v, Hv v →ₜ* G) [Fintype ι]
  {κ : Type} {F : κ → Type} [∀ w, Group (F w)] [∀ w, TopologicalSpace (F w)]
  [∀ w, IsTopologicalGroup (F w)] [∀ w, Fintype (F w)] (ψ : ∀ w, F w →ₜ* G) [Fintype κ]
  {n : ℕ} [NeZero n] (D : Rep (ULift.{0} ℤ) G) [IsDiscreteRep D]

theorem surjective_of_ptTLocalToCompact_two (t : tateCompactCohomologyRes φ ψ D 3 →+ ZMod n)
    (inv : ∀ v, cohomology (Rep.res (φ v).toMonoidHom D) 2 →+ QZ)
    (invr : ∀ w, cohomology (Rep.res (ψ w).toMonoidHom D) 2 →+ QZ)
    (ht : ∀ ξ : ptTLocal φ ψ D 2, zmodToQZ n (t ((ptTLocalToCompact φ ψ D 2).hom ξ)) =
      ∑ v, inv v (ξ.1 v) + ∑ w, invr w (ξ.2 w))
    (v : ι) (η : cohomology (Rep.res (φ v).toMonoidHom D) 2) (hη : inv v η = zmodToQZ n 1) :
    Function.Surjective t := by
  classical
  have h1 : t ((ptTLocalToCompact φ ψ D 2).hom ((Pi.single v η, 0) : ptTLocal φ ψ D 2)) = 1 :=
    zmodToQZ_injective ((ht _).trans ((congrArg₂ (· + ·) (sum_apply_pi_single inv v η)
      (Finset.sum_eq_zero fun w _ => map_zero (invr w))).trans ((add_zero _).trans hη)))
  intro a
  refine ⟨a.val • (ptTLocalToCompact φ ψ D 2).hom ((Pi.single v η, 0) : ptTLocal φ ψ D 2), ?_⟩
  rw [map_nsmul, h1, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]

end GenericTrace

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
  (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))

section Places

variable {N : ℕ} (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((N : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S) (hev : Even N)
include hS hev

theorem mem_of_natCast_two_mem_of_even :
    ∀ v : HeightOneSpectrum (𝓞 K.1), ((2 : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S := by
  intro v hv
  apply hS v
  obtain ⟨m, hm⟩ := hev
  rw [hm, ← two_mul, Nat.cast_mul]
  exact v.asIdeal.mul_mem_right _ hv

theorem mem_of_natCast_two_mul_mem_of_even :
    ∀ v : HeightOneSpectrum (𝓞 K.1), ((2 * N : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S := by
  intro v hv
  rw [Nat.cast_mul] at hv
  rcases v.isPrime.mem_or_mem hv with h2 | hN
  · exact mem_of_natCast_two_mem_of_even S hS hev v h2
  · exact hS v hN

end Places

theorem exists_sq_eq_neg_one_of_even {N : ℕ} (hev : Even N) : ∃ z : ℚ̄, z ^ 2 = -1 ∧ z ^ (2 * N) = 1 := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : ℚ̄) (show 0 < 2 by norm_num)
  refine ⟨z, hz, ?_⟩
  obtain ⟨m, hm⟩ := hev
  rw [hm, show 2 * (m + m) = 2 * 2 * m by ring, pow_mul, pow_mul, hz]
  norm_num

theorem gsRealFamily_realConj_ne (w : {v : InfinitePlace K.1 // v.IsReal}) (η : maxUnramifiedOutside K.1 ℚ̄ S)
    (hη : η ^ 2 = -1) : gsRealFamily S ιr w (realConj w.1 w.2) η ≠ η := by
  intro hfix
  have key := gsRealFamily_apply S ιr w (realConj w.1 w.2) η
  rw [hfix] at key
  have hη' : ((η : ℚ̄)) ^ 2 = -1 := by
    have e := congrArg (fun y : maxUnramifiedOutside K.1 ℚ̄ S => (y : ℚ̄)) hη
    push_cast at e
    exact e
  have ha2 : (ιr w (η : ℚ̄)) ^ 2 = -1 := by rw [← map_pow, hη', map_neg, map_one]
  have ha0 : ιr w (η : ℚ̄) ≠ 0 := fun h0 => by
    rw [h0] at ha2
    norm_num at ha2
  have hu : Units.mk0 _ ha0 ^ 4 = 1 := Units.ext (by
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, show (4 : ℕ) = 2 * 2 from rfl, pow_mul, ha2]
    norm_num)
  have hc := realConj_apply_of_pow_eq_one w.1 w.2 (Units.mk0 _ ha0) (by norm_num) hu
  have h3 : ιr w (η : ℚ̄) * ιr w (η : ℚ̄) = 1 :=
    calc ιr w (η : ℚ̄) * ιr w (η : ℚ̄) = ιr w (η : ℚ̄) * realConj w.1 w.2 (ιr w (η : ℚ̄)) :=
          congrArg (fun z => ιr w (η : ℚ̄) * z) key
      _ = ((Units.mk0 _ ha0 : (AlgebraicClosure w.1.Completion)ˣ) : AlgebraicClosure w.1.Completion) *
          (((Units.mk0 _ ha0)⁻¹ : (AlgebraicClosure w.1.Completion)ˣ) : AlgebraicClosure w.1.Completion) :=
          congrArg (fun z => ιr w (η : ℚ̄) * z) hc
      _ = 1 := Units.mul_inv _
  have h4 : (-1 : AlgebraicClosure w.1.Completion) = 1 := by rw [← ha2, sq, h3]
  norm_num at h4

theorem freeOnCosets_gsRealFamily_of_fixes (ζ : maxUnramifiedOutside K.1 ℚ̄ S) (hζ : ζ ^ 2 = -1)
    (W : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) (hW : ∀ σ ∈ W, σ ζ = ζ) :
    FreeOnCosets (gsRealFamily S ιr) W := by
  intro w x h hmem
  rcases eq_one_or_eq_realConj w.1 w.2 h with h1 | h1
  · exact h1
  exfalso
  subst h1
  have hfix : (x * gsRealFamily S ιr w (realConj w.1 w.2) * x⁻¹) ζ = ζ := hW _ hmem
  have h2 : gsRealFamily S ιr w (realConj w.1 w.2) (x⁻¹ ζ) = x⁻¹ ζ :=
    calc gsRealFamily S ιr w (realConj w.1 w.2) (x⁻¹ ζ)
        = x⁻¹ ((x * gsRealFamily S ιr w (realConj w.1 w.2) * x⁻¹) ζ) := (x.symm_apply_apply _).symm
      _ = x⁻¹ ζ := congrArg (fun y => (x⁻¹ : galUnramifiedOutside K.1 ℚ̄ S) y) hfix
  have hη : (x⁻¹ ζ) ^ 2 = -1 := by rw [← map_pow, hζ, map_neg, map_one]
  exact gsRealFamily_realConj_ne S ιr w (x⁻¹ ζ) hη h2

section Hypotheses

variable [Fintype S] {N : ℕ} [NeZero N]
  (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((N : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S) (hev : Even N)

set_option maxHeartbeats 1000000 in
include hS in

theorem surjective_of_localToCompact_two [hne : Nonempty S]
    (t : tateCompactCohomologyRes (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) 3 →+ ZMod N)
    (ht : ∀ ξ : ptTLocal (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) 2,
      zmodToQZ N (t ((ptTLocalToCompact (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) 2).hom ξ)) =
        ∑ v, gsLocalInvRootsQZ S ιs N v (ξ.1 v) + ∑ w, gsRealInvRootsQZ S ιr N w (ξ.2 w)) :
    Function.Surjective t := by
  obtain ⟨v⟩ := hne
  obtain ⟨η, hη⟩ := (bijective_gsLocalInvRoots_of_places S ιs N (fun v hv h => hv (hS v h)) v).2 1
  exact surjective_of_ptTLocalToCompact_two (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) t
    (gsLocalInvRootsQZ S ιs N) (gsRealInvRootsQZ S ιr N) ht v η
    ((zmodToQZ_gsLocalInvRoots S ιs N v η).symm.trans (congrArg (zmodToQZ N) hη))

omit [Fintype S] in
include hS hev in

theorem isTotallyComplex_of_gsOpenSubgroup_le {L : FiniteSubfield} [Fact (K ≤ L)]
    (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
    (W₀ : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S))
    (hW₀ : ∀ σ ∈ W₀, ∀ ζ : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ, ζ ^ (2 * N) = 1 →
      σ (ζ : maxUnramifiedOutside K.1 ℚ̄ S) = ζ)
    (hU : gsOpenSubgroup S hL ≤ W₀) : IsTotallyComplex L.1 := by
  obtain ⟨z, hz2, hzN⟩ := exists_sq_eq_neg_one_of_even hev
  have hn0 : 2 * N ≠ 0 := by have := NeZero.ne N; omega
  have hzL : z ∈ L.1 := rootsOfUnity_mem_of_gsOpenSubgroup_le S (2 * N) hL W₀ hW₀ hU hn0
    (fun v hv h => hv (mem_of_natCast_two_mul_mem_of_even S hS hev v h)) z hzN
  refine isTotallyComplex_of_sq_eq_neg_one (⟨z, hzL⟩ : L.1) ?_
  apply Subtype.ext
  push_cast
  exact hz2

omit [Fintype S] in
include hS hev in

theorem freeOnCosets_gsRealFamily_of_le (W₀ : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S))
    (hW₀ : ∀ σ ∈ W₀, ∀ ζ : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ, ζ ^ (2 * N) = 1 →
      σ (ζ : maxUnramifiedOutside K.1 ℚ̄ S) = ζ)
    (U : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S)) (hU : U ≤ W₀) :
    FreeOnCosets (gsRealFamily S ιr) (U : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) := by
  obtain ⟨z, hz2, hzN⟩ := exists_sq_eq_neg_one_of_even hev
  have hn0 : 2 * N ≠ 0 := by have := NeZero.ne N; omega
  have hzmem : z ∈ maxUnramifiedOutside K.1 ℚ̄ S := mem_maxUnramifiedOutside_of_pow_eq_one S hn0
    (fun v hv h => hv (mem_of_natCast_two_mul_mem_of_even S hS hev v h)) hzN
  have hζ : (⟨z, hzmem⟩ : maxUnramifiedOutside K.1 ℚ̄ S) ^ 2 = -1 := by
    apply Subtype.ext
    push_cast
    exact hz2
  have hne : (⟨z, hzmem⟩ : maxUnramifiedOutside K.1 ℚ̄ S) ≠ 0 := fun h0 => by
    rw [h0] at hζ
    norm_num at hζ
  have hpow : Units.mk0 _ hne ^ (2 * N) = 1 := Units.ext (by
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
    apply Subtype.ext
    push_cast
    exact hzN)
  exact freeOnCosets_gsRealFamily_of_fixes S ιr _ hζ _ fun σ hσ => hW₀ σ (hU hσ) _ hpow

end Hypotheses

end GroundTheory.ProfCoh
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open IsDedekindDomain NumberField CategoryTheory GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

attribute [local instance 2000] Rep.hV2

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))
  [Fintype S] {N : ℕ} [NeZero N]
  (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((N : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S) (hev : Even N)

def GsTauBijective (U : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S)) : Prop :=
  ∀ τ : compactCohomologyRes (mackeyFamily U (gsFinFamily S ιs))
      (Rep.res (U : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype (gsRoots S N)) 3 →+ ZMod N,
    Function.Surjective τ → ∀ {r s : ℕ} (h : r + s = 3),
      Function.Bijective (compactZmodDualityMap (mackeyFamily U (gsFinFamily S ιs))
        (Rep.res (U : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype (gsRoots S N)) (nsmul_gsRoots S N) τ h)

set_option maxHeartbeats 1000000 in
include hS hev in

theorem gsTauBijective_gsOpenSubgroup {L : FiniteSubfield} [Fact (K ≤ L)]
    (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
    (W₀ : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S))
    (hW₀ : ∀ σ ∈ W₀, ∀ ζ : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ, ζ ^ (2 * N) = 1 →
      σ (ζ : maxUnramifiedOutside K.1 ℚ̄ S) = ζ)
    (hU : gsOpenSubgroup S hL ≤ W₀) : GsTauBijective S ιs (N := N) (gsOpenSubgroup S hL) := by
  intro τ hτ r s h
  have hTC := isTotallyComplex_of_gsOpenSubgroup_le S hS hev hL W₀ hW₀ hU
  let := fintypePlacesOver (L := L) S
  have : Nonempty (placesOver S : Set (HeightOneSpectrum (𝓞 L.1))) :=
    nonempty_placesOver_of_natCast_mem S Nat.prime_two (mem_of_natCast_two_mem_of_even S hS hev)
  have hSL : ∀ w : HeightOneSpectrum (𝓞 L.1), ((N : ℕ) : 𝓞 L.1) ∈ w.asIdeal → w ∈ placesOver S :=
    fun w hw => mem_placesOver_of_natCast_mem hS hw
  exact bijective_compactZmodDualityMap_gsOpenSubgroup_of_surjective S ιs hL N τ hτ _
    (gsLevelBijective_gsCompactInv (placesOver S) (gsMackeyEmbeddings hL ιs) hSL (Or.inr hTC)) h

end GroundTheory.ProfCoh
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open IsDedekindDomain NumberField CategoryTheory GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

attribute [local instance 2000] Rep.hV2

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
  (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))

section Hypotheses

variable [Fintype S] {N : ℕ} [NeZero N]
  (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((N : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S) (hev : Even N)

include hS hev in

theorem gsTauBijective_of_le (W₀ : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S))
    (hW₀ : ∀ σ ∈ W₀, ∀ ζ : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ, ζ ^ (2 * N) = 1 →
      σ (ζ : maxUnramifiedOutside K.1 ℚ̄ S) = ζ)
    (U : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S)) (hU : U ≤ W₀) : GsTauBijective S ιs (N := N) U := by
  obtain ⟨L, _, hL, rfl⟩ := exists_gsOpenSubgroup_eq K S U
  exact gsTauBijective_gsOpenSubgroup S ιs hS hev hL W₀ hW₀ hU

set_option maxHeartbeats 1000000 in
include hS hev in

theorem bijective_tateCompactDualityMap_coind_gs_of_even
    (t : tateCompactCohomologyRes (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) 3 →+ ZMod N)
    (ht : Function.Surjective t) (W₀ : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S))
    (hW₀ : ∀ σ ∈ W₀, ∀ ζ : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ, ζ ^ (2 * N) = 1 →
      σ (ζ : maxUnramifiedOutside K.1 ℚ̄ S) = ζ)
    (U : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S)) (hU : U ≤ W₀) {r s : ℕ} (h : r + (s + 1) = 3)
    [IsDiscreteRep (dualRep (gsRoots S N) (Rep.coind (U : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype
      (zmodRep.{0} (U : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) N)))] :
    Function.Bijective (tateCompactDualityMap (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) h t
      (Rep.coind (U : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype
        (zmodRep.{0} (U : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) N))) := by
  have hfree := freeOnCosets_gsRealFamily_of_le S ιr hS hev W₀ hW₀ U hU
  refine bijective_tateCompactDualityMap_coind (gsFinFamily S ιs) (gsRealFamily S ιr) U hfree
    (nsmul_gsRoots S N) t h ?_
  have : Finite (gsRoots S N) :=
    (nonempty_addEquiv_gsRoots_of_mem S hS).elim fun e => Finite.of_equiv _ e.toEquiv.symm
  have hτ : Function.Surjective (tateCoresTrace (gsFinFamily S ιs) (gsRealFamily S ιr) U hfree t) :=
    ht.comp (surjective_tateCompactCores_three (gsFinFamily S ιs) (gsRealFamily S ιr) U hfree (gsRoots S N)
      (nsmul_gsRoots S N) fun M _ _ hM => subsingleton_gsTateCompactCohomology S ιr ιs (NeZero.ne N) hS M hM
        le_rfl)
  have hb := gsTauBijective_of_le S ιs hS hev W₀ hW₀ U hU
    (tateCoresTrace (gsFinFamily S ιs) (gsRealFamily S ιr) U hfree t) hτ h
  convert hb using 1

include hS hev in

theorem exists_tateCompactDualityHypotheses_gs_of_even
    (t : tateCompactCohomologyRes (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) 3 →+ ZMod N)
    (ht : Function.Surjective t) :
    ∃ U₀ : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S),
      TateCompactDualityHypotheses (gsFinFamily S ιs) (gsRealFamily S ιr) N (gsRoots S N) t U₀ := by
  have hn0 : 2 * N ≠ 0 := by have := NeZero.ne N; omega
  obtain ⟨W₀, hW₀⟩ := exists_openSubgroup_fixing_rootsOfUnity K S (2 * N) hn0
  refine ⟨W₀, ⟨nonempty_addEquiv_gsRoots_of_mem S hS, fun M _ _ hM =>
    subsingleton_gsTateCompactCohomology S ιr ιs (NeZero.ne N) hS M hM le_rfl, fun U hU {r s} h hs => ?_⟩⟩
  cases s with
  | zero => exact absurd hs (by norm_num)
  | succ s =>
    have : Finite (Rep.coind (U : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype
        (zmodRep.{0} (U : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) N)) := finite_coind U _
    have : IsDiscreteRep (dualRep (gsRoots S N) (Rep.coind (U : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype
        (zmodRep.{0} (U : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) N))) := isDiscreteRep_dualRep _ _
    convert bijective_tateCompactDualityMap_coind_gs_of_even S ιr ιs hS hev t ht W₀ hW₀ U hU h using 1

include hS hev in

theorem bijective_tateCompactDualityMap_gs_of_even
    (t : tateCompactCohomologyRes (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) 3 →+ ZMod N)
    (ht : Function.Surjective t) (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S))
    [IsDiscreteRep M] [Finite M] (hM : ∀ m : M, N • m = 0) {r s : ℕ} (h : r + s = 3) (hs : 1 ≤ s) :
    Function.Bijective (tateCompactDualityMap (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) h t M) :=
  (exists_tateCompactDualityHypotheses_gs_of_even S ιr ιs hS hev t ht).elim fun _ H =>
    H.bijective_tateCompactDualityMap M hM h hs

include hS hev in

theorem gsEvenTatePoitouTateHypotheses :
    TatePoitouTateHypotheses (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N)
      (gsTrace S ιr ιs N) (gsLocalInvRootsQZ S ιs N) (gsRealInvRootsQZ S ιr N) := by
  have : Nonempty S := nonempty_of_natCast_mem S 2 Nat.prime_two (mem_of_natCast_two_mem_of_even S hS hev)
  have hD := nonempty_addEquiv_gsRoots_of_mem S hS
  have ht := surjective_of_localToCompact_two S ιr ιs hS (gsTrace S ιr ιs N) (gsTrace_localToCompact S ιr ιs N)
  exact
    { nonempty_addEquiv := hD
      duality := @fun M _ _ hM r s h hs =>
        bijective_tateCompactDualityMap_gs_of_even S ιr ιs hS hev (gsTrace S ιr ιs N) ht M hM h hs
      finite_cohomology := fun M _ _ hM r hr =>
        finite_cohomology_gs K S M (fun v hv => hS v (natCast_mem_of_natCard_mem v.isPrime hM hv)) r hr
      localToCompact_two := gsTrace_localToCompact S ιr ιs N
      injective_res_zero := fun M _ => injective_ptRes_zero_gs S ιs M
      surjective_localPairing_zero := fun M _ _ hM v => (bijective_gsLocalPairing S ιs N hD M hM v _).2
      surjective_localPairing_two := fun M _ _ hM v => (bijective_gsLocalPairing S ιs N hD M hM v _).2
      surjective_realPairing_zero := fun M _ _ hM w => surjective_gsRealPairing_zero S ιr N M hD hM w
      surjective_realPairing_two := fun M _ _ hM w χ hχ => exists_gsRealPairing_two S ιr N M hD hM w χ hχ }

end Hypotheses

end GroundTheory.ProfCoh
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open IsDedekindDomain NumberField CategoryTheory GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

attribute [local instance 2000] Rep.hV2

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1))) [Fintype S] [Nonempty S]
  (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))
  {N : ℕ} [NeZero N] (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((N : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
  (hodd : Odd N)
  (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] [Finite M]
  (hM : ∀ m : M, N • m = 0)

include hM in

theorem poitouTateReal_nineTerm_of_odd :
    Function.Injective (ptTGlobalToLocalHat (gsFinFamily S ιs) (gsRealFamily S ιr) M) ∧
    Function.Exact (ptTGlobalToLocalHat (gsFinFamily S ιs) (gsRealFamily S ιr) M)
      (ptTLocalHatDualMap (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) M
        (gsLocalInvRootsQZ S ιs N) (gsRealInvRootsQZ S ιr N)) ∧
    Function.Exact (ptTLocalHatDualMap (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) M
        (gsLocalInvRootsQZ S ιs N) (gsRealInvRootsQZ S ιr N))
      (ptTDualToGlobal (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) (gsOddTrace S ιr ιs hS hodd) M
        (show 1 + 2 = 3 from rfl)
        ((gsOddTatePoitouTateHypotheses S ιr ιs hS hodd).bijective_ptTCompactDualMap M hM _ le_rfl)) ∧
    Function.Exact (ptTDualToGlobal (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N)
        (gsOddTrace S ιr ιs hS hodd) M (show 1 + 2 = 3 from rfl)
        ((gsOddTatePoitouTateHypotheses S ιr ιs hS hodd).bijective_ptTCompactDualMap M hM _ le_rfl))
      (ptTGlobalToLocal (gsFinFamily S ιs) (gsRealFamily S ιr) M 1).hom ∧
    Function.Exact (ptTGlobalToLocal (gsFinFamily S ιs) (gsRealFamily S ιr) M 1).hom
      (ptTLocalDualMap (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) M
        (gsLocalInvRootsQZ S ιs N) (gsRealInvRootsQZ S ιr N) (show 1 + 1 = 2 from rfl)) ∧
    Function.Exact (ptTLocalDualMap (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) M
        (gsLocalInvRootsQZ S ιs N) (gsRealInvRootsQZ S ιr N) (show 1 + 1 = 2 from rfl))
      (ptTDualToGlobal (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) (gsOddTrace S ιr ιs hS hodd) M
        (show 2 + 1 = 3 from rfl)
        ((gsOddTatePoitouTateHypotheses S ιr ιs hS hodd).bijective_ptTCompactDualMap M hM _ (by norm_num))) ∧
    Function.Exact (ptTDualToGlobal (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N)
        (gsOddTrace S ιr ιs hS hodd) M (show 2 + 1 = 3 from rfl)
        ((gsOddTatePoitouTateHypotheses S ιr ιs hS hodd).bijective_ptTCompactDualMap M hM _ (by norm_num)))
      (ptTGlobalToLocal (gsFinFamily S ιs) (gsRealFamily S ιr) M 2).hom ∧
    Function.Exact (ptTGlobalToLocal (gsFinFamily S ιs) (gsRealFamily S ιr) M 2).hom
      (ptTLocalDualMap (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) M
        (gsLocalInvRootsQZ S ιs N) (gsRealInvRootsQZ S ιr N) (show 2 + 0 = 2 from rfl)) ∧
    Function.Surjective (ptTLocalDualMap (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) M
      (gsLocalInvRootsQZ S ιs N) (gsRealInvRootsQZ S ιr N) (show 2 + 0 = 2 from rfl)) :=
  (gsOddTatePoitouTateHypotheses S ιr ιs hS hodd).nineTerm M hM

include hM in

theorem poitouTateReal_sha_of_odd :
    Finite (ptTSha (gsFinFamily S ιs) (gsRealFamily S ιr) M 1) ∧
      Finite (ptTSha (gsFinFamily S ιs) (gsRealFamily S ιr) (dualRep (gsRoots S N) M) 2) ∧
      Function.Bijective (ptTShaPairing (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) M
        (gsOddTrace S ιr ιs hS hodd)) ∧
      Function.Bijective (ptTShaPairing (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) M
        (gsOddTrace S ιr ιs hS hodd)).flip :=
  (gsOddTatePoitouTateHypotheses S ιr ιs hS hodd).sha M hM

include ιs hS hodd hM in

theorem injective_gsRealRes_three_of_odd : Function.Injective (gsRealRes S ιr M 3).hom := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  have h0 : (ptTGlobalToLocal (gsFinFamily S ιs) (gsRealFamily S ιr) M 3).hom x = 0 := by
    refine (ptTGlobalToLocal_apply _ _ M 3 x).trans (Prod.ext (funext fun v => ?_) (funext fun w => ?_))
    · exact (subsingleton_cohomology_gsFinFamily_of_three_le S ιs (NeZero.ne N) M hM v le_rfl).elim _ _
    · exact congrFun hx w
  exact (gsOddTatePoitouTateHypotheses S ιr ιs hS hodd).injective_ptTGlobalToLocal_three M hM
    (h0.trans (map_zero _).symm)

include ιs hS hodd hM in

theorem bijective_gsRealRes_of_odd {r : ℕ} (hr : 3 ≤ r) : Function.Bijective (gsRealRes S ιr M r).hom := by
  refine ⟨?_, surjective_gsRealRes_of_three_le S ιr (NeZero.ne N) hS M hM hr⟩
  rcases r with _ | _ | _ | _ | r
  · exact absurd hr (by norm_num)
  · exact absurd hr (by norm_num)
  · exact absurd hr (by norm_num)
  · exact injective_gsRealRes_three_of_odd S ιr ιs hS hodd M hM
  · exact injective_gsRealRes_of_four_le S ιr (NeZero.ne N) hS M hM (by omega)

end GroundTheory.ProfCoh
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open IsDedekindDomain NumberField CategoryTheory GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

attribute [local instance 2000] Rep.hV2

section Nonempty

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1))) {N : ℕ}

theorem nonempty_of_natCast_mem_of_ne_one (hN : N ≠ 1)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((N : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S) : Nonempty S := by
  obtain ⟨p, hp, hpN⟩ := Nat.exists_prime_and_dvd hN
  obtain ⟨k, rfl⟩ := hpN
  refine nonempty_of_natCast_mem S p hp fun v hv => hS v ?_
  rw [Nat.cast_mul]
  exact v.asIdeal.mul_mem_right _ hv

end Nonempty

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1))) [Fintype S] [Nonempty S]
  (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))
  {N : ℕ} [NeZero N] (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((N : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)

section Hypotheses

set_option maxHeartbeats 1000000 in
include hS in

theorem gsTrace_eq_gsOddTrace (hodd : Odd N) : gsTrace S ιr ιs N = gsOddTrace S ιr ιs hS hodd := by
  have : Finite (gsRoots S N) :=
    (nonempty_addEquiv_gsRoots_of_mem S hS).elim fun e => Finite.of_equiv _ e.toEquiv.symm
  refine AddMonoidHom.ext fun z => ?_
  obtain ⟨ξ, hξ⟩ := (gsOddTatePoitouTateHypotheses S ιr ιs hS hodd).surjective_ptTLocalToCompact_two
    (gsRoots S N) (nsmul_gsRoots S N) z
  calc gsTrace S ιr ιs N z
      = gsTrace S ιr ιs N ((ptTLocalToCompact (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) 2).hom ξ) :=
        congrArg _ hξ.symm
    _ = gsOddTrace S ιr ιs hS hodd
          ((ptTLocalToCompact (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) 2).hom ξ) :=
        zmodToQZ_injective ((gsTrace_localToCompact S ιr ιs N ξ).trans
          (gsOddTrace_localToCompact S ιr ιs hS hodd ξ).symm)
    _ = gsOddTrace S ιr ιs hS hodd z := congrArg _ hξ

include hS in

theorem gsTatePoitouTateHypotheses :
    TatePoitouTateHypotheses (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N)
      (gsTrace S ιr ιs N) (gsLocalInvRootsQZ S ιs N) (gsRealInvRootsQZ S ιr N) := by
  rcases Nat.even_or_odd N with hev | hodd
  · exact gsEvenTatePoitouTateHypotheses S ιr ιs hS hev
  · exact (gsTrace_eq_gsOddTrace S ιr ιs hS hodd).symm ▸ gsOddTatePoitouTateHypotheses S ιr ιs hS hodd

end Hypotheses

variable (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] [Finite M]
  (hM : ∀ m : M, N • m = 0)

include hS hM in

theorem poitouTateReal_duality {r s : ℕ} (h : r + s = 3) (hs : 1 ≤ s) :
    Function.Bijective (tateCompactDualityMap (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) h
      (gsTrace S ιr ιs N) M) :=
  (gsTatePoitouTateHypotheses S ιr ιs hS).duality M hM h hs

include hS hM in

theorem poitouTateReal_compactDual {r s : ℕ} (h : r + s = 3) (hr : 1 ≤ r) :
    Function.Bijective (ptTCompactDualMap (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) M
      (gsTrace S ιr ιs N) h) :=
  (gsTatePoitouTateHypotheses S ιr ιs hS).bijective_ptTCompactDualMap M hM h hr

include hS hM in

theorem poitouTateReal_nineTerm :
    Function.Injective (ptTGlobalToLocalHat (gsFinFamily S ιs) (gsRealFamily S ιr) M) ∧
    Function.Exact (ptTGlobalToLocalHat (gsFinFamily S ιs) (gsRealFamily S ιr) M)
      (ptTLocalHatDualMap (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) M
        (gsLocalInvRootsQZ S ιs N) (gsRealInvRootsQZ S ιr N)) ∧
    Function.Exact (ptTLocalHatDualMap (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) M
        (gsLocalInvRootsQZ S ιs N) (gsRealInvRootsQZ S ιr N))
      (ptTDualToGlobal (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) (gsTrace S ιr ιs N) M
        (show 1 + 2 = 3 from rfl)
        ((gsTatePoitouTateHypotheses S ιr ιs hS).bijective_ptTCompactDualMap M hM _ le_rfl)) ∧
    Function.Exact (ptTDualToGlobal (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N)
        (gsTrace S ιr ιs N) M (show 1 + 2 = 3 from rfl)
        ((gsTatePoitouTateHypotheses S ιr ιs hS).bijective_ptTCompactDualMap M hM _ le_rfl))
      (ptTGlobalToLocal (gsFinFamily S ιs) (gsRealFamily S ιr) M 1).hom ∧
    Function.Exact (ptTGlobalToLocal (gsFinFamily S ιs) (gsRealFamily S ιr) M 1).hom
      (ptTLocalDualMap (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) M
        (gsLocalInvRootsQZ S ιs N) (gsRealInvRootsQZ S ιr N) (show 1 + 1 = 2 from rfl)) ∧
    Function.Exact (ptTLocalDualMap (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) M
        (gsLocalInvRootsQZ S ιs N) (gsRealInvRootsQZ S ιr N) (show 1 + 1 = 2 from rfl))
      (ptTDualToGlobal (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) (gsTrace S ιr ιs N) M
        (show 2 + 1 = 3 from rfl)
        ((gsTatePoitouTateHypotheses S ιr ιs hS).bijective_ptTCompactDualMap M hM _ (by norm_num))) ∧
    Function.Exact (ptTDualToGlobal (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N)
        (gsTrace S ιr ιs N) M (show 2 + 1 = 3 from rfl)
        ((gsTatePoitouTateHypotheses S ιr ιs hS).bijective_ptTCompactDualMap M hM _ (by norm_num)))
      (ptTGlobalToLocal (gsFinFamily S ιs) (gsRealFamily S ιr) M 2).hom ∧
    Function.Exact (ptTGlobalToLocal (gsFinFamily S ιs) (gsRealFamily S ιr) M 2).hom
      (ptTLocalDualMap (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) M
        (gsLocalInvRootsQZ S ιs N) (gsRealInvRootsQZ S ιr N) (show 2 + 0 = 2 from rfl)) ∧
    Function.Surjective (ptTLocalDualMap (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) M
      (gsLocalInvRootsQZ S ιs N) (gsRealInvRootsQZ S ιr N) (show 2 + 0 = 2 from rfl)) :=
  (gsTatePoitouTateHypotheses S ιr ιs hS).nineTerm M hM

include hS hM in

theorem poitouTateReal_sha :
    Finite (ptTSha (gsFinFamily S ιs) (gsRealFamily S ιr) M 1) ∧
      Finite (ptTSha (gsFinFamily S ιs) (gsRealFamily S ιr) (dualRep (gsRoots S N) M) 2) ∧
      Function.Bijective (ptTShaPairing (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) M
        (gsTrace S ιr ιs N)) ∧
      Function.Bijective (ptTShaPairing (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) M
        (gsTrace S ιr ιs N)).flip :=
  (gsTatePoitouTateHypotheses S ιr ιs hS).sha M hM

include ιs hS hM in

theorem injective_gsRealRes_three : Function.Injective (gsRealRes S ιr M 3).hom := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  have h0 : (ptTGlobalToLocal (gsFinFamily S ιs) (gsRealFamily S ιr) M 3).hom x = 0 := by
    refine (ptTGlobalToLocal_apply _ _ M 3 x).trans (Prod.ext (funext fun v => ?_) (funext fun w => ?_))
    · exact (subsingleton_cohomology_gsFinFamily_of_three_le S ιs (NeZero.ne N) M hM v le_rfl).elim _ _
    · exact congrFun hx w
  exact (gsTatePoitouTateHypotheses S ιr ιs hS).injective_ptTGlobalToLocal_three M hM
    (h0.trans (map_zero _).symm)

include ιs hS hM in

theorem bijective_gsRealRes {r : ℕ} (hr : 3 ≤ r) : Function.Bijective (gsRealRes S ιr M r).hom := by
  refine ⟨?_, surjective_gsRealRes_of_three_le S ιr (NeZero.ne N) hS M hM hr⟩
  rcases r with _ | _ | _ | _ | r
  · exact absurd hr (by norm_num)
  · exact absurd hr (by norm_num)
  · exact absurd hr (by norm_num)
  · exact injective_gsRealRes_three S ιr ιs hS M hM
  · exact injective_gsRealRes_of_four_le S ιr (NeZero.ne N) hS M hM (by omega)

end GroundTheory.ProfCoh
end
end
