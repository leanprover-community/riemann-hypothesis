import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLocalFinitenessRegularSemisimpleCentralizStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalTwistContinuousInvolutionIntegralPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalIntegralRestrictedProductEqProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdelicUnitaryPointLocalComponentMemLocalUn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdelicUnitaryPointEqOfSectionComponentsEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicUnitaryPointOfLocalFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyFiniteAdelicUnitaryComponentMemIntegra
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactDefiniteUnitaryRestrictedProduct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalComponentDefiniteUnitaryFinitePartEqLocalPo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyDefiniteUnitaryLocalPointMemMaxCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralConjugateMemCentralizerMulInte
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentraliserCompactPartLeIntegralAlmostAll
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedCentralizerLocalUnitaryCommOfSeparable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteUnitaryLocalPointEqMapRational
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RightStabilizerConjBiinvariantFiniteIndex

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteAdelicUnitaryPoint_localComponent_mem_localUnitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, ∀ (w : Pl E) (x : finU E n), cLoc w (x : UA E n) ∈ UL n w := by
  first | exact @GlobalTheory.BCT.cLoc_mem_UL | exact GlobalTheory.BCT.cLoc_mem_UL | (intros; apply GlobalTheory.BCT.cLoc_mem_UL <;> assumption)
end

section
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT

theorem cLoc_fin_continuous {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (w : Pl E) :
    Continuous (fun x : finU E n => cLoc w (x : UA E n)) := by
  have hf : Continuous ((pLoc E w).comp (pFin E)) := by
    show Continuous (fun x => pLoc E w (pFin E x))
    exact (RestrictedProduct.continuous_eval w).comp continuous_snd
  have hm : Continuous (((pLoc E w).comp (pFin E)).mapMatrix : Matrix (Fin n) (Fin n) (Ad E) →+* _) :=
    continuous_id.matrix_map hf
  exact (Continuous.units_map _ hm).comp (continuous_subtype_val.comp continuous_subtype_val)

theorem continuous_toSub {X G : Type} [TopologicalSpace X] [Group G] [TopologicalSpace G] (H : Subgroup G) {f : X → G}
    (hf : Continuous f) (hH : ∀ x, f x ∈ H) : Continuous (fun x => toSub H (f x)) := by
  have : (fun x => toSub H (f x)) = fun x => (⟨f x, hH x⟩ : H) := by
    funext x; simp [toSub, hH x]
  rw [this]
  exact hf.subtype_mk _

theorem toSub_cLoc_continuous_of_mem {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (w : Pl E)
    (hmem : ∀ x : finU E n, cLoc w (x : UA E n) ∈ UL n w) :
    Continuous (fun x : finU E n => toSub (UL n w) (cLoc w (x : UA E n))) :=
  continuous_toSub _ (cLoc_fin_continuous w) hmem

theorem toSub_cLoc_fin_continuous : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ,
    ∀ w : Pl E, Continuous (fun x : finU E n => toSub (UL n w) (cLoc w (x : UA E n))) := by
  intro E _ _ _ hE n w
  exact toSub_cLoc_continuous_of_mem w (GlobalTheory.T.finiteAdelicUnitaryPoint_localComponent_mem_localUnitary E hE n w)

end GlobalTheory.BCT
end
end

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_unitaryLocalComponent_toLocalUnitaryGroup : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, ∀ w : Pl E, Continuous (fun x : finU E n => toSub (UL n w) (cLoc w (x : UA E n))) := by
  atlas_forward_decl GlobalTheory.BCT.toSub_cLoc_fin_continuous
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteAdelicUnitaryPoint_eq_of_section_components_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, ∀ S : Set (Pl E), IsSection S → ∀ x y : finU E n, (∀ w ∈ S, toSub (UL n w) (cLoc w (x : UA E n)) = toSub (UL n w) (cLoc w (y : UA E n))) → x = y := by
  first | exact @GlobalTheory.BCT.finU_eq_of_loc | exact GlobalTheory.BCT.finU_eq_of_loc | (intros; apply GlobalTheory.BCT.finU_eq_of_loc <;> assumption)
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteAdelicUnitaryPoint_of_local_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, ∀ S : Set (Pl E), IsSection S → ∀ y : ∀ w : Pl E, UL n w, (∀ᶠ w in cofinite, y w ∈ KL n w) → ∃ x : finU E n, ∀ w ∈ S, toSub (UL n w) (cLoc w (x : UA E n)) = y w := by
  first | exact @GlobalTheory.BCT.exists_finU_of_loc | exact GlobalTheory.BCT.exists_finU_of_loc | (intros; apply GlobalTheory.BCT.exists_finU_of_loc <;> assumption)
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_finiteAdelicUnitaryComponent_mem_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, ∀ x : finU E n, ∀ᶠ w in cofinite, toSub (UL n w) (cLoc w (x : UA E n)) ∈ KL n w := by
  first | exact @GlobalTheory.BCT.LocAE.eventually_mem_KL | exact GlobalTheory.BCT.LocAE.eventually_mem_KL | (intros; apply GlobalTheory.BCT.LocAE.eventually_mem_KL <;> assumption)
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCompact_definiteUnitary_restricted_product : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, ∀ S : Set (Pl E), IsSection S → ∀ C : ∀ w : Pl E, Set (UL n w), (∀ w, IsCompact (C w)) → (∀ᶠ w in cofinite, C w = KL n w) → IsCompact {x : finU E n | ∀ w ∈ S, toSub (UL n w) (cLoc w (x : UA E n)) ∈ C w} := by
  first | exact @GlobalTheory.BCT.LocCpt.loc_cpt | exact GlobalTheory.BCT.LocCpt.loc_cpt | (intros; apply GlobalTheory.BCT.LocCpt.loc_cpt <;> assumption)
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localComponent_definiteUnitaryFinitePart_eq_localPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, ∀ (γ : UE E n) (w : Pl E), toSub (UL n w) (cLoc w ((finPt γ : finU E n) : UA E n)) = locPt w γ := by
  first | exact @GlobalTheory.BCT.locPt_finPt | exact GlobalTheory.BCT.locPt_finPt | (intros; apply GlobalTheory.BCT.locPt_finPt <;> assumption)
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_definiteUnitaryLocalPoint_mem_maxCompact : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, ∀ γ : UE E n, γ.1.val.charpoly.Separable → ∀ᶠ w in cofinite, locPt w γ ∈ KL n w := by
  first | exact @GlobalTheory.BCT.GoodInt.locPt_mem_KL | exact GlobalTheory.BCT.GoodInt.locPt_mem_KL | (intros; apply GlobalTheory.BCT.GoodInt.locPt_mem_KL <;> assumption)
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_integralConjugate_mem_centralizer_mul_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ γ : UE E n, γ.1.val.charpoly.Separable → ∀ᶠ w in cofinite, ∀ g : UL n w, g⁻¹ * locPt w γ * g ∈ KL n w → ∃ t ∈ twCent (MonoidHom.id (UL n w)) (locPt w γ), t⁻¹ * g ∈ KL n w := by
  first | exact @GlobalTheory.BCT.GoodConj.main | exact GlobalTheory.BCT.GoodConj.main | (intros; apply GlobalTheory.BCT.GoodConj.main <;> assumption)
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedCentralizer_localUnitary_comm_of_separable : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, ∀ (w : Pl E) (y : UL n w), y.1.val.charpoly.Separable → ∀ a ∈ twCent (MonoidHom.id (UL n w)) y, ∀ b ∈ twCent (MonoidHom.id (UL n w)) y, a * b = b * a := by
  first | exact @GlobalTheory.BCT.centComm | exact GlobalTheory.BCT.centComm | (intros; apply GlobalTheory.BCT.centComm <;> assumption)
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteUnitaryLocalPoint_eq_map_rational : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, ∀ (γ : UE E n) (w : Pl E), ((locPt w γ : UL n w) : GLw n w) = Matrix.GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) (γ : GL (Fin n) E) := by
  first | exact @GlobalTheory.BCT.LocVal.main | exact GlobalTheory.BCT.LocVal.main | (intros; apply GlobalTheory.BCT.LocVal.main <;> assumption)
end

section
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem doubleCoset_finite_of_compactSupport : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (T K : Subgroup G) (y : G) (f : G → ℂ), IsCompact (K : Set G) → HasCompactSupport f → (∀ C : Set G, IsCompact C → {q : DoubleCoset.Quotient (T : Set G) (K : Set G) | (Quotient.out q)⁻¹ * y * Quotient.out q ∈ C}.Finite) → {q : DoubleCoset.Quotient (T : Set G) (K : Set G) | ∃ k ∈ K, f ((Quotient.out q * k)⁻¹ * y * (Quotient.out q * k)) ≠ 0}.Finite := by
  intro G _ _ _ T K y f hK hf hfin
  have hCc : IsCompact ((fun p : G × G => p.1 * p.2 * p.1⁻¹) '' ((K : Set G) ×ˢ tsupport f)) :=
    (hK.prod hf.isCompact).image ((continuous_fst.mul continuous_snd).mul continuous_fst.inv)
  refine (hfin _ hCc).subset ?_
  rintro q ⟨k, hk, hne⟩
  refine ⟨(k, (Quotient.out q * k)⁻¹ * y * (Quotient.out q * k)), ⟨hk, subset_tsupport f hne⟩, ?_⟩
  group

end GlobalTheory
end

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_doubleCosets_meeting_compact_support_conj : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (T K : Subgroup G) (y : G) (f : G → ℂ), IsCompact (K : Set G) → HasCompactSupport f → (∀ C : Set G, IsCompact C → {q : DoubleCoset.Quotient (T : Set G) (K : Set G) | (Quotient.out q)⁻¹ * y * Quotient.out q ∈ C}.Finite) → {q : DoubleCoset.Quotient (T : Set G) (K : Set G) | ∃ k ∈ K, f ((Quotient.out q * k)⁻¹ * y * (Quotient.out q * k)) ≠ 0}.Finite := by
  atlas_forward_decl GlobalTheory.doubleCoset_finite_of_compactSupport
end

section
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT

theorem twOrb_globFn_eq_finprod : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → ∀ γ : UE E n, γ.1.val.charpoly.Separable → twOrb (MonoidHom.id _) (globLev S (KL n)) (finPt γ) (globFn S f) = ∏ᶠ w ∈ S, twOrb (MonoidHom.id _) (KL n w) (locPt w γ) (f w) := by
  intro E _ _ _ hU n hn S hS K' hK' f hf γ hγ
  have hTB := fun w : Pl E => GlobalTheory.T.localTwist_continuous_involution_integral_properties E hU n w
  have hKo : ∀ w : Pl E, IsOpen (KL n w : Set (UL n w)) := fun w => (hTB w).2.2.2.2.2.2.1
  have hKc : ∀ w : Pl E, IsCompact (KL n w : Set (UL n w)) := fun w => (hTB w).2.2.2.2.2.2.2.1
  let p : ∀ i : S, finU E n →* UL n i.1 := fun i =>
    ((cLoc i.1).comp (finU E n).subtype).codRestrict (UL n i.1) (fun x => GlobalTheory.T.finiteAdelicUnitaryPoint_localComponent_mem_localUnitary E hU n i.1 x)
  have hp : ∀ (i : S) (x : finU E n), p i x = toSub (UL n i.1) (cLoc i.1 (x : UA E n)) := by
    intro i x
    unfold toSub
    rw [dif_pos (GlobalTheory.T.finiteAdelicUnitaryPoint_localComponent_mem_localUnitary E hU n i.1 x)]
    rfl
  have hδ : ∀ i : S, p i (finPt γ) = locPt i.1 γ := fun i => (hp i _).trans (GlobalTheory.T.localComponent_definiteUnitaryFinitePart_eq_localPoint E hU n γ i.1)
  have hsep : ∀ w : Pl E, (locPt w γ).1.val.charpoly.Separable := by
    intro w
    rw [GlobalTheory.T.definiteUnitaryLocalPoint_eq_map_rational E hU n γ w]
    show ((γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).map (algebraMap E (w.adicCompletion E)) |>.charpoly.Separable
    rw [Matrix.charpoly_map]
    exact hγ.map
  have hlev : ∀ w : Pl E, IsLevel (MonoidHom.id (UL n w)) (KL n w) (KL n w) :=
    fun w => ⟨hKo w, le_rfl, fun k hk => hk⟩
  have hglob : globFn S f = fun x => ∏ᶠ i : S, f i.1 (p i x) := by
    funext x
    unfold globFn
    exact (finprod_subtype_eq_finprod_cond (f := fun w => f w (toSub (UL n w) (cLoc w (x : UA E n)))) (fun w => w ∈ S)).symm.trans
      (finprod_congr fun i => by rw [hp])
  have hK : ∀ x : finU E n, x ∈ globLev S (KL n) ↔ ∀ i : S, p i x ∈ KL n i.1 := by
    intro x
    unfold globLev
    simp only [Subgroup.mem_iInf, Subgroup.mem_comap, Subgroup.mem_map, MonoidHom.coe_comp, Function.comp_apply,
      Subgroup.coe_subtype]
    constructor
    · intro h i
      obtain ⟨k, hk, hke⟩ := h i.1 i.2
      have : p i x = k := Subtype.ext hke.symm
      rw [this]; exact hk
    · intro h w hw
      exact ⟨p ⟨w, hw⟩ x, h ⟨w, hw⟩, rfl⟩
  rw [hglob]
  have hmain := GlobalTheory.T.orbitalIntegral_restrictedProduct_eq_prod S (finU E n) (fun i : S => UL n i.1) p (globLev S (KL n)) (fun i => KL n i.1) (finPt γ)
    (fun i => f i.1)
    (fun i => by
      have hfun : (p i : finU E n → UL n i.1) = fun x : finU E n => toSub (UL n i.1) (cLoc i.1 (x : UA E n)) := funext (hp i)
      rw [hfun]; exact GlobalTheory.T.continuous_unitaryLocalComponent_toLocalUnitaryGroup E hU n i.1)
    (fun x y h => GlobalTheory.T.finiteAdelicUnitaryPoint_eq_of_section_components_eq E hU n S hS x y (fun w hw => by rw [← hp ⟨w, hw⟩, ← hp ⟨w, hw⟩]; exact h ⟨w, hw⟩))
    (fun y hy => by
      let y' : ∀ w : Pl E, UL n w := fun w => if hw : w ∈ S then y ⟨w, hw⟩ else 1
      have hy' : ∀ᶠ w in cofinite, y' w ∈ KL n w := by
        rw [Filter.eventually_cofinite] at hy ⊢
        refine (hy.image Subtype.val).subset ?_
        intro w hw
        by_cases hwS : w ∈ S
        · exact ⟨⟨w, hwS⟩, by simpa [y', hwS] using hw, rfl⟩
        · exact absurd (by simp only [y', dif_neg hwS]; exact one_mem _) hw
      obtain ⟨x, hx⟩ := GlobalTheory.T.exists_finiteAdelicUnitaryPoint_of_local_family E hU n S hS y' hy'
      exact ⟨x, fun i => by rw [hp, hx i.1 i.2]; simp [y', i.2]⟩)
    (fun x => by
      have h := GlobalTheory.T.eventually_finiteAdelicUnitaryComponent_mem_integral E hU n x
      rw [Filter.eventually_cofinite] at h ⊢
      refine (h.preimage Subtype.val_injective.injOn).subset ?_
      intro i hi
      simp only [Set.mem_preimage, Set.mem_setOf_eq] at hi ⊢
      rwa [← hp])
    hK
    (fun C hC hCK => by
      let C' : ∀ w : Pl E, Set (UL n w) := fun w => if hw : w ∈ S then C ⟨w, hw⟩ else (KL n w : Set (UL n w))
      have hC' : ∀ᶠ w in cofinite, C' w = KL n w := by
        rw [Filter.eventually_cofinite] at hCK ⊢
        refine (hCK.image Subtype.val).subset ?_
        intro w hw
        by_cases hwS : w ∈ S
        · exact ⟨⟨w, hwS⟩, by simpa [C', hwS] using hw, rfl⟩
        · exact absurd (by simp only [C', dif_neg hwS]) hw
      have h := GlobalTheory.T.isCompact_definiteUnitary_restricted_product E hU n S hS C' (fun w => by
        by_cases hw : w ∈ S
        · simp only [C', dif_pos hw]; exact hC _
        · simp only [C', dif_neg hw]; exact hKc w) hC'
      convert h using 1
      ext x
      simp only [Set.mem_setOf_eq]
      constructor
      · intro hx w hw
        have := hx ⟨w, hw⟩
        rw [hp] at this
        simpa [C', hw] using this
      · intro hx i
        have := hx i.1 i.2
        rw [hp]
        simpa [C', i.2] using this)
    (fun i => hKc i.1)
    (fun i => by rw [hδ]; exact GlobalTheory.T.twistedCentralizer_localUnitary_comm_of_separable E hU n i.1 (locPt i.1 γ) (hsep i.1))
    (fun i x => by rw [hδ]; exact (GlobalTheory.T.unitary_local_finiteness_regular_semisimple_centralizer E hU n i.1 (locPt i.1 γ) (hsep i.1) (KL n i.1) (hlev i.1)).1 x)
    (fun i x => GlobalTheory.T.rightStabilizer_conj_biinvariant_finiteIndex (UL n i.1) (KL n i.1) (K' i.1) (f i.1) (p i (finPt γ)) (hKc i.1) (hK'.1 i.1).1
      (hK'.1 i.1).2.1 (hf.1 i.1).2 x)
    (fun i => by
      rw [hδ]
      exact GlobalTheory.T.finite_doubleCosets_meeting_compact_support_conj (UL n i.1) (twCent (MonoidHom.id (UL n i.1)) (locPt i.1 γ)) (KL n i.1) (locPt i.1 γ) (f i.1)
        (hKc i.1) (hf.1 i.1).1 (GlobalTheory.T.unitary_local_finiteness_regular_semisimple_centralizer E hU n i.1 (locPt i.1 γ) (hsep i.1) (KL n i.1) (hlev i.1)).2)
    (by
      have hgood := (GlobalTheory.T.eventually_definiteUnitaryLocalPoint_mem_maxCompact E hU n γ hγ).and (hf.2.and ((GlobalTheory.T.eventually_integralConjugate_mem_centralizer_mul_integral E hU n hn γ hγ).and (GlobalTheory.T.centraliser_compactPart_le_integral_almostAll E hU n γ hγ)))
      rw [Filter.eventually_cofinite] at hgood ⊢
      refine (hgood.preimage Subtype.val_injective.injOn).subset ?_
      intro i hi
      simp only [Set.mem_preimage, Set.mem_setOf_eq] at hi ⊢
      intro h
      apply hi
      rw [hδ]
      exact h)
  rw [hmain]
  simp_rw [hδ]
  exact finprod_subtype_eq_finprod_cond (f := fun w => twOrb (MonoidHom.id _) (KL n w) (locPt w γ) (f w)) (fun w => w ∈ S)

end GlobalTheory.BCT
end
end

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedOrbitalIntegral_product_eq_finprod : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → ∀ γ : UE E n, γ.1.val.charpoly.Separable → twOrb (MonoidHom.id _) (globLev S (KL n)) (finPt γ) (globFn S f) = ∏ᶠ w ∈ S, twOrb (MonoidHom.id _) (KL n w) (locPt w γ) (f w) := by
  atlas_forward_decl GlobalTheory.BCT.twOrb_globFn_eq_finprod
end
