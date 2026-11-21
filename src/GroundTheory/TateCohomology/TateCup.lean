import Mathlib
import GroundTheory.TateCohomology.TateTheorem
import GroundTheory.TateCohomology.CupTate

section
set_option maxSynthPendingDepth 1

open CategoryTheory MonoidalCategory

namespace GroundTheory.GroupCoh

universe u

variable {k G : Type u} [CommRing k] [Group G]

section Unitors

variable (E : ShortComplex (Rep.{u} k G))

noncomputable def leftUnitorSCIso : E.map (tensorLeft (𝟙_ (Rep.{u} k G))) ≅ E :=
  ShortComplex.isoMk (λ_ E.X₁) (λ_ E.X₂) (λ_ E.X₃) (leftUnitor_naturality E.f).symm
    (leftUnitor_naturality E.g).symm

noncomputable def rightUnitorSCIso : E.map (tensorRight (𝟙_ (Rep.{u} k G))) ≅ E :=
  ShortComplex.isoMk (ρ_ E.X₁) (ρ_ E.X₂) (ρ_ E.X₃) (rightUnitor_naturality E.f).symm
    (rightUnitor_naturality E.g).symm

variable {E}

theorem shortExact_tensorLeft_unit (hE : E.ShortExact) :
    (E.map (tensorLeft (𝟙_ (Rep.{u} k G)))).ShortExact :=
  ShortComplex.shortExact_of_iso (leftUnitorSCIso E).symm hE

theorem shortExact_tensorRight_unit (hE : E.ShortExact) :
    (E.map (tensorRight (𝟙_ (Rep.{u} k G)))).ShortExact :=
  ShortComplex.shortExact_of_iso (rightUnitorSCIso E).symm hE

variable [Fintype G]

theorem δ_leftUnitor_apply (hE : E.ShortExact)
    (hE' : (E.map (tensorLeft (𝟙_ (Rep.{u} k G)))).ShortExact) (i : ℤ)
    (x : tateCohomology (𝟙_ (Rep.{u} k G) ⊗ E.X₃) i) :
    (TateCohomology.δ hE i).hom (((tateCohomologyFunctor i).map (λ_ E.X₃).hom).hom x) =
      ((tateCohomologyFunctor (i + 1)).map (λ_ E.X₁).hom).hom ((TateCohomology.δ hE' i).hom x) :=
  congr(($(TateCohomology.δ_naturality hE' hE (leftUnitorSCIso E).hom i)).hom x).symm

theorem δ_rightUnitor_apply (hE : E.ShortExact)
    (hE' : (E.map (tensorRight (𝟙_ (Rep.{u} k G)))).ShortExact) (i : ℤ)
    (x : tateCohomology (E.X₃ ⊗ 𝟙_ (Rep.{u} k G)) i) :
    (TateCohomology.δ hE i).hom (((tateCohomologyFunctor i).map (ρ_ E.X₃).hom).hom x) =
      ((tateCohomologyFunctor (i + 1)).map (ρ_ E.X₁).hom).hom ((TateCohomology.δ hE' i).hom x) :=
  congr(($(TateCohomology.δ_naturality hE' hE (rightUnitorSCIso E).hom i)).hom x).symm

end Unitors

variable [Fintype G]

variable (k G) in

noncomputable def tateOne : tateCohomology (𝟙_ (Rep.{u} k G)) 0 :=
  ((tateCohomologyZeroIso k G).app (𝟙_ (Rep.{u} k G))).inv.hom
    (Submodule.Quotient.mk ⟨(1 : k), fun _ => rfl⟩)

set_option maxHeartbeats 800000 in

theorem leftUnitor_tateCup_tateOne_zero (B : Rep.{u} k G) (b : tateCohomology B 0) :
    ((tateCohomologyFunctor 0).map (λ_ B).hom).hom
      (tateCup 0 0 (𝟙_ (Rep.{u} k G)) B 0 (zero_add 0) (tateOne k G) b) = b := by
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _
    (((tateCohomologyZeroIso k G).app B).hom.hom b)
  have hb : b = ((tateCohomologyZeroIso k G).app B).inv.hom (Submodule.Quotient.mk y) := by
    rw [hy]
    exact (((tateCohomologyZeroIso k G).app B).hom_inv_id_apply b).symm
  subst hb
  have h0 := tateCup_zero_zero (𝟙_ (Rep.{u} k G)) B ⟨(1 : k), fun _ => rfl⟩ y
  refine (congrArg (((tateCohomologyFunctor 0).map (λ_ B).hom).hom) h0).trans ?_
  have hn := congr(($((tateCohomologyZeroIso k G).inv.naturality (λ_ B).hom)).hom
    (Submodule.Quotient.mk (tensorInvariants (⟨(1 : k), fun _ => rfl⟩ :
      (𝟙_ (Rep.{u} k G)).ρ.invariants) y)))
  refine hn.symm.trans ?_
  change ((tateCohomologyZeroIso k G).inv.app B).hom (Submodule.Quotient.mk _) = _
  congr 2
  apply Subtype.ext
  change (λ_ B).hom.hom ((1 : k) ⊗ₜ[k] (y : B)) = y
  rw [leftUnitor_hom_tmul, one_smul]

theorem leftUnitor_tateCup_tateOne_down (q q' : ℤ) (hq : q + 1 = q')
    (h : ∀ (B : Rep.{u} k G) (b : tateCohomology B q'),
      ((tateCohomologyFunctor q').map (λ_ B).hom).hom
        (tateCup 0 q' (𝟙_ (Rep.{u} k G)) B q' (zero_add _) (tateOne k G) b) = b)
    (B : Rep.{u} k G) (b : tateCohomology B q) :
    ((tateCohomologyFunctor q).map (λ_ B).hom).hom
        (tateCup 0 q (𝟙_ (Rep.{u} k G)) B q (zero_add _) (tateOne k G) b) = b := by
  subst hq
  have hE := augSES_shortExact B
  have hAE := augSES_tensorLeft_shortExact (𝟙_ (Rep.{u} k G)) B
  have hiso : IsIso (TateCohomology.δ hE q) :=
    isIso_δ_of_tateAcyclic hE (tateAcyclic_leftRegular_tensor B) q
  apply moduleIso_hom_injective (@asIso _ _ _ _ _ hiso)
  refine (δ_leftUnitor_apply hE hAE q _).trans ?_
  have hr := tateCup_δ_right hE (𝟙_ (Rep.{u} k G)) hAE 0 q q (zero_add q) (tateOne k G) b
  rw [Int.negOnePow_zero, one_smul] at hr
  refine (congrArg (((tateCohomologyFunctor (q + 1)).map (λ_ _).hom).hom) hr).trans ?_
  exact h _ _

theorem leftUnitor_tateCup_tateOne_up (q q' : ℤ) (hq : q + 1 = q')
    (h : ∀ (B : Rep.{u} k G) (b : tateCohomology B q),
      ((tateCohomologyFunctor q).map (λ_ B).hom).hom
        (tateCup 0 q (𝟙_ (Rep.{u} k G)) B q (zero_add _) (tateOne k G) b) = b)
    (B : Rep.{u} k G) (b : tateCohomology B q') :
    ((tateCohomologyFunctor q').map (λ_ B).hom).hom
        (tateCup 0 q' (𝟙_ (Rep.{u} k G)) B q' (zero_add _) (tateOne k G) b) = b := by
  subst hq
  have hE := coindSES_shortExact B
  have hAE := shortExact_tensorLeft_unit hE
  have hiso : IsIso (TateCohomology.δ hE q) := isIso_δ_coindSES B q
  obtain ⟨c, rfl⟩ : ∃ c, (TateCohomology.δ hE q).hom c = b :=
    ⟨(@asIso _ _ _ _ _ hiso).inv.hom b, (@asIso _ _ _ _ _ hiso).inv_hom_id_apply b⟩
  have hr := tateCup_δ_right hE (𝟙_ (Rep.{u} k G)) hAE 0 q q (zero_add q) (tateOne k G) c
  rw [Int.negOnePow_zero, one_smul] at hr
  refine (congrArg (((tateCohomologyFunctor (q + 1)).map (λ_ _).hom).hom) hr.symm).trans ?_
  refine (δ_leftUnitor_apply hE hAE q _).symm.trans ?_
  exact congrArg (TateCohomology.δ hE q).hom (h _ _)

theorem leftUnitor_tateCup_tateOne (q : ℤ) (B : Rep.{u} k G) (b : tateCohomology B q) :
    ((tateCohomologyFunctor q).map (λ_ B).hom).hom
        (tateCup 0 q (𝟙_ (Rep.{u} k G)) B q (zero_add _) (tateOne k G) b) = b := by
  induction q using Int.induction_on generalizing B with
  | zero => exact leftUnitor_tateCup_tateOne_zero B b
  | succ i ih => exact leftUnitor_tateCup_tateOne_up (i : ℤ) _ rfl ih B b
  | pred i ih => exact leftUnitor_tateCup_tateOne_down _ (-(i : ℤ)) (by ring) ih B b

end GroundTheory.GroupCoh
end

section
set_option maxSynthPendingDepth 1

open CategoryTheory MonoidalCategory Limits Rep

namespace GroundTheory.GroupCoh

section Transport

universe u

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

theorem tateCup_eqToHom_left {A B : Rep.{u} k G} {p p' q r r' : ℤ} (hp : p = p') (hr : r = r')
    (h : p + q = r) (h' : p' + q = r') (a : tateCohomology A p) (b : tateCohomology B q) :
    (eqToHom (congrArg (tateCohomology (A ⊗ B)) hr)).hom (tateCup p q A B r h a b) =
      tateCup p' q A B r' h' ((eqToHom (congrArg (tateCohomology A) hp)).hom a) b := by
  subst hp hr
  simp

theorem eqToHom_tateMap_apply {X Y : Rep.{u} k G} (f : X ⟶ Y) {i j : ℤ} (hij : i = j)
    (x : tateCohomology X i) :
    (eqToHom (congrArg (tateCohomology Y) hij)).hom (((tateCohomologyFunctor i).map f).hom x) =
      ((tateCohomologyFunctor j).map f).hom ((eqToHom (congrArg (tateCohomology X) hij)).hom x) := by
  subst hij
  simp

theorem tateIsoH_eqToHom_apply (A : Rep.{u} k G) {p₀ p p' : ℤ} (n : ℕ) [NeZero n] (e : p₀ = p)
    (e' : p₀ = p') (hp : p = n) (hp' : p' = n) (w : tateCohomology A p₀) :
    (tateIsoH A p n hp).hom.hom ((eqToHom (congrArg (tateCohomology A) e)).hom w) =
      (tateIsoH A p' n hp').hom.hom ((eqToHom (congrArg (tateCohomology A) e')).hom w) := by
  subst e e'
  rfl

end Transport

section Tate

variable {G : Type} [Group G] [Fintype G] (M : Rep ℤ G) (u : groupCohomology M 2)
  (S : Subgroup G) [Fintype S]

noncomputable def tateResClass : tateCohomology (res S.subtype M) 2 :=
  (tateIsoH (res S.subtype M) 2 2 (by norm_num)).inv.hom
    (groupCohomology.map S.subtype (𝟙 (res S.subtype M)) 2 u)

variable (h1 : ∀ S : Subgroup G, IsZero (groupCohomology (res S.subtype M) 1))
  (h2 : ∀ S : Subgroup G,
    addOrderOf (groupCohomology.map S.subtype (𝟙 (res S.subtype M)) 2 u) = Nat.card S)
  (h3 : ∀ (S : Subgroup G) (y : groupCohomology (res S.subtype M) 2),
    ∃ m : ℤ, y = m • groupCohomology.map S.subtype (𝟙 (res S.subtype M)) 2 u)

include h1 h2 h3

theorem tateTheorem_δ_δ_tateOne :
    (eqToHom (congrArg (tateCohomology (res S.subtype M)) (show (0 : ℤ) + 1 + 1 = 2 by norm_num))).hom
      ((TateCohomology.δ ((shortExact_res S.subtype).2 (splittingSES_shortExact M u)) (0 + 1)).hom
        ((TateCohomology.δ (augTrivSES_res_shortExact ℤ S.subtype) 0).hom (tateOne ℤ S))) =
      tateResClass M u S := by
  apply moduleIso_hom_injective (tateIsoH (res S.subtype M) 2 2 (by norm_num))
  rw [tateResClass, Iso.inv_hom_id_apply]
  refine (tateIsoH_eqToHom_apply (res S.subtype M) 2 (show (0 : ℤ) + 1 + 1 = 2 by norm_num)
    (show (0 : ℤ) + 1 + 1 = 0 + 2 by norm_num) (by norm_num) (by norm_num) _).trans ?_
  exact tateTheoremIso_zero_apply M u h1 h2 h3 S

set_option maxHeartbeats 1600000 in

theorem tateTheoremIso_hom_apply (n : ℤ) (x : tateCohomology (Rep.trivial ℤ S ℤ) n) :
    (tateTheoremIso M u h1 h2 h3 S n).hom.hom x =
      ((tateCohomologyFunctor (n + 2)).map (ρ_ (res S.subtype M)).hom).hom
        (tateCup 2 n (res S.subtype M) (Rep.trivial ℤ S ℤ) (n + 2) (add_comm 2 n)
          (tateResClass M u S) x) := by
  have hE1 := augTrivSES_res_shortExact ℤ S.subtype
  have hE2 := (shortExact_res S.subtype).2 (splittingSES_shortExact M u)
  have hE1R := shortExact_tensorRight_unit hE1
  have hE2R := shortExact_tensorRight_unit hE2
  have hx : ((tateCohomologyFunctor n).map (ρ_ (𝟙_ (Rep ℤ S))).hom).hom
      (tateCup 0 n (𝟙_ (Rep ℤ S)) (𝟙_ (Rep ℤ S)) n (zero_add n) (tateOne ℤ S) x) = x := by
    rw [← unitors_equal]
    exact leftUnitor_tateCup_tateOne n _ x
  have s1 : (TateCohomology.δ hE1 n).hom x =
      ((tateCohomologyFunctor (n + 1)).map (ρ_ (res S.subtype (augIdeal ℤ G))).hom).hom
        (tateCup (0 + 1) n (res S.subtype (augIdeal ℤ G)) (𝟙_ (Rep ℤ S)) (n + 1) (by omega)
          ((TateCohomology.δ hE1 0).hom (tateOne ℤ S)) x) :=
    (congrArg (TateCohomology.δ hE1 n).hom hx.symm).trans ((δ_rightUnitor_apply hE1 hE1R n _).trans
      (congrArg _ (tateCup_δ_left hE1 (𝟙_ (Rep ℤ S)) hE1R 0 n n (zero_add n) (tateOne ℤ S) x)))
  have s2 : (TateCohomology.δ hE2 (n + 1)).hom
      (((tateCohomologyFunctor (n + 1)).map (ρ_ (res S.subtype (augIdeal ℤ G))).hom).hom
        (tateCup (0 + 1) n (res S.subtype (augIdeal ℤ G)) (𝟙_ (Rep ℤ S)) (n + 1) (by omega)
          ((TateCohomology.δ hE1 0).hom (tateOne ℤ S)) x)) =
      ((tateCohomologyFunctor (n + 1 + 1)).map (ρ_ (res S.subtype M)).hom).hom
        (tateCup (0 + 1 + 1) n (res S.subtype M) (𝟙_ (Rep ℤ S)) (n + 1 + 1) (by omega)
          ((TateCohomology.δ hE2 (0 + 1)).hom ((TateCohomology.δ hE1 0).hom (tateOne ℤ S))) x) :=
    (δ_rightUnitor_apply hE2 hE2R (n + 1) _).trans
      (congrArg _ (tateCup_δ_left hE2 (𝟙_ (Rep ℤ S)) hE2R (0 + 1) n (n + 1) (by omega) _ x))
  have hT : (tateTheoremIso M u h1 h2 h3 S n).hom.hom x =
      (eqToHom (congrArg (tateCohomology (res S.subtype M)) (show n + 1 + 1 = n + 2 by ring))).hom
        ((TateCohomology.δ hE2 (n + 1)).hom ((TateCohomology.δ hE1 n).hom x)) := rfl
  rw [hT, s1, s2]
  refine (eqToHom_tateMap_apply (ρ_ (res S.subtype M)).hom (show n + 1 + 1 = n + 2 by ring) _).trans ?_
  refine congrArg _ ((tateCup_eqToHom_left (show (0 : ℤ) + 1 + 1 = 2 by norm_num)
    (show n + 1 + 1 = n + 2 by ring) _ (add_comm 2 n) _ x).trans ?_)
  exact congrArg (fun t => tateCup 2 n (res S.subtype M) (Rep.trivial ℤ S ℤ) (n + 2) (add_comm 2 n) t x)
    (tateTheorem_δ_δ_tateOne M u S h1 h2 h3)

end Tate

end GroundTheory.GroupCoh
end
