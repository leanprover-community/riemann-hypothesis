import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanLStable
import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocE
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitOfClosure
import BuildAid.ForwardExisting

section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition GlobalTheory.Pass.LocDual GlobalTheory.Pass.LocDual.OneX

noncomputable section

namespace GlobalTheory.Pass.LocDual.OneX.Combine

variable {O V ι Γ Q G C : Type} [CommRing O] [AddCommGroup V] [Module O V] [AddCommGroup Q] [Module O Q]

def blk (act : ι → Γ → V → V) {a : ℕ} (x : Fin a → ι) (γ : Γ) (v : Fin a → V) : Fin a → V :=
  fun b => act (x b) γ (v b)

def appL (a₁ a₂ : ℕ) : ((Fin a₁ → V) × (Fin a₂ → V)) →ₗ[O] (Fin (a₁ + a₂) → V) where
  toFun p := Fin.append p.1 p.2
  map_add' p q := by
    funext j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;> simp
  map_smul' c p := by
    funext j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;> simp

def resL₁ (a₁ a₂ : ℕ) : (Fin (a₁ + a₂) → V) →ₗ[O] (Fin a₁ → V) where
  toFun v := fun j => v (Fin.castAdd a₂ j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def resL₂ (a₁ a₂ : ℕ) : (Fin (a₁ + a₂) → V) →ₗ[O] (Fin a₂ → V) where
  toFun v := fun j => v (Fin.natAdd a₁ j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem resL₁_append {a₁ a₂ : ℕ} (v₁ : Fin a₁ → V) (v₂ : Fin a₂ → V) :
    resL₁ (O := O) a₁ a₂ (Fin.append v₁ v₂) = v₁ := by
  funext j; simp [resL₁]

theorem resL₂_append {a₁ a₂ : ℕ} (v₁ : Fin a₁ → V) (v₂ : Fin a₂ → V) :
    resL₂ (O := O) a₁ a₂ (Fin.append v₁ v₂) = v₂ := by
  funext j; simp [resL₂]

theorem blk_append (act : ι → Γ → V → V) {a₁ a₂ : ℕ} (x₁ : Fin a₁ → ι) (x₂ : Fin a₂ → ι) (γ : Γ)
    (v₁ : Fin a₁ → V) (v₂ : Fin a₂ → V) :
    blk act (Fin.append x₁ x₂) γ (Fin.append v₁ v₂) = Fin.append (blk act x₁ γ v₁) (blk act x₂ γ v₂) := by
  funext j
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;> simp [blk]

theorem append_sub {a₁ a₂ : ℕ} (u₁ v₁ : Fin a₁ → V) (u₂ v₂ : Fin a₂ → V) :
    Fin.append u₁ u₂ - Fin.append v₁ v₂ = Fin.append (u₁ - v₁) (u₂ - v₂) := by
  funext j
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;> simp

def HasPres (act : ι → Γ → V → V) (W : Γ → Q → Q) (gl : G → Γ) (out : Q → C) (S : Set (G → C)) : Prop :=
  ∃ (a : ℕ) (x : Fin a → ι) (E : Fin a → V) (Y : Submodule O (Fin a → V)), Y.FG ∧
    ∃ (hst : ∀ γ : Γ, ∀ y ∈ Y, blk act x γ y ∈ Y) (hE : ∀ γ : Γ, blk act x γ E - E ∈ Y),
      ∀ c ∈ S, ∃ φ : ↥Y →ₗ[O] Q, (∀ (γ : Γ) (y : ↥Y), φ ⟨_, hst γ y.1 y.2⟩ = W γ (φ y)) ∧
        c = fun g => out (φ ⟨_, hE (gl g)⟩)

variable (act : ι → Γ → V → V) (W : Γ → Q → Q) (gl : G → Γ) (out : Q → C)

theorem hasPres_empty : HasPres (O := O) act W gl out ∅ := by
  refine ⟨0, Fin.elim0, 0, ⊥, Submodule.fg_bot, ?_, ?_, ?_⟩
  · intro γ y _
    rw [Subsingleton.elim (blk act Fin.elim0 γ y) 0]; exact Submodule.zero_mem _
  · intro γ
    rw [Subsingleton.elim (blk act Fin.elim0 γ 0 - 0) 0]; exact Submodule.zero_mem _
  · intro c hc; exact absurd hc (Set.notMem_empty c)

theorem hasPres_union {S T : Set (G → C)} (hS : HasPres (O := O) act W gl out S)
    (hT : HasPres (O := O) act W gl out T) : HasPres (O := O) act W gl out (S ∪ T) := by
  obtain ⟨a₁, x₁, E₁, Y₁, hY₁, hst₁, hE₁, hφ₁⟩ := hS
  obtain ⟨a₂, x₂, E₂, Y₂, hY₂, hst₂, hE₂, hφ₂⟩ := hT
  set Y : Submodule O (Fin (a₁ + a₂) → V) := (Y₁.prod Y₂).map (appL a₁ a₂) with hYdef
  have mem_of : ∀ y₁ ∈ Y₁, ∀ y₂ ∈ Y₂, Fin.append y₁ y₂ ∈ Y := fun y₁ h₁ y₂ h₂ =>
    Submodule.mem_map_of_mem (f := appL a₁ a₂) (p := Y₁.prod Y₂) (r := (y₁, y₂)) (Submodule.mem_prod.2 ⟨h₁, h₂⟩)
  have mem_iff : ∀ y ∈ Y, ∃ y₁ ∈ Y₁, ∃ y₂ ∈ Y₂, y = Fin.append y₁ y₂ := by
    intro y hy
    obtain ⟨⟨y₁, y₂⟩, ⟨h₁, h₂⟩, rfl⟩ := Submodule.mem_map.1 hy
    exact ⟨y₁, h₁, y₂, h₂, rfl⟩
  have r₁ : ∀ y ∈ Y, resL₁ (O := O) a₁ a₂ y ∈ Y₁ := by
    intro y hy
    obtain ⟨y₁, h₁, y₂, h₂, rfl⟩ := mem_iff y hy
    rw [resL₁_append]; exact h₁
  have r₂ : ∀ y ∈ Y, resL₂ (O := O) a₁ a₂ y ∈ Y₂ := by
    intro y hy
    obtain ⟨y₁, h₁, y₂, h₂, rfl⟩ := mem_iff y hy
    rw [resL₂_append]; exact h₂
  have hst : ∀ γ : Γ, ∀ y ∈ Y, blk act (Fin.append x₁ x₂) γ y ∈ Y := by
    intro γ y hy
    obtain ⟨y₁, h₁, y₂, h₂, rfl⟩ := mem_iff y hy
    rw [blk_append]
    exact mem_of _ (hst₁ γ y₁ h₁) _ (hst₂ γ y₂ h₂)
  have hEq : ∀ γ : Γ, blk act (Fin.append x₁ x₂) γ (Fin.append E₁ E₂) - Fin.append E₁ E₂ =
      Fin.append (blk act x₁ γ E₁ - E₁) (blk act x₂ γ E₂ - E₂) := by
    intro γ; rw [blk_append, append_sub]
  have hE : ∀ γ : Γ, blk act (Fin.append x₁ x₂) γ (Fin.append E₁ E₂) - Fin.append E₁ E₂ ∈ Y := by
    intro γ; rw [hEq]; exact mem_of _ (hE₁ γ) _ (hE₂ γ)
  refine ⟨a₁ + a₂, Fin.append x₁ x₂, Fin.append E₁ E₂, Y, ?_, hst, hE, ?_⟩
  · exact (hY₁.prod hY₂).map _
  · intro c hc
    rcases hc with hc | hc
    · obtain ⟨φ, hφ, rfl⟩ := hφ₁ c hc
      let ρ : ↥Y →ₗ[O] ↥Y₁ := ((resL₁ (O := O) a₁ a₂).domRestrict Y).codRestrict Y₁ (fun y => r₁ y.1 y.2)
      refine ⟨φ ∘ₗ ρ, ?_, ?_⟩
      · intro γ y
        obtain ⟨y, hy⟩ := y
        obtain ⟨y₁, h₁, y₂, h₂, rfl⟩ := mem_iff y hy
        have e1 : (ρ ⟨_, hst γ _ hy⟩ : ↥Y₁) = ⟨_, hst₁ γ y₁ h₁⟩ := by
          apply Subtype.ext
          show resL₁ (O := O) a₁ a₂ (blk act (Fin.append x₁ x₂) γ (Fin.append y₁ y₂)) = _
          rw [blk_append, resL₁_append]
        have e2 : (ρ ⟨_, hy⟩ : ↥Y₁) = ⟨y₁, h₁⟩ := by
          apply Subtype.ext
          show resL₁ (O := O) a₁ a₂ (Fin.append y₁ y₂) = _
          rw [resL₁_append]
        simp only [LinearMap.comp_apply]
        rw [e1, e2]
        exact hφ γ ⟨y₁, h₁⟩
      · funext g
        simp only [LinearMap.comp_apply]
        congr 2
        apply Subtype.ext
        show _ = resL₁ (O := O) a₁ a₂ (blk act (Fin.append x₁ x₂) (gl g) (Fin.append E₁ E₂) - Fin.append E₁ E₂)
        rw [hEq, resL₁_append]
    · obtain ⟨φ, hφ, rfl⟩ := hφ₂ c hc
      let ρ : ↥Y →ₗ[O] ↥Y₂ := ((resL₂ (O := O) a₁ a₂).domRestrict Y).codRestrict Y₂ (fun y => r₂ y.1 y.2)
      refine ⟨φ ∘ₗ ρ, ?_, ?_⟩
      · intro γ y
        obtain ⟨y, hy⟩ := y
        obtain ⟨y₁, h₁, y₂, h₂, rfl⟩ := mem_iff y hy
        have e1 : (ρ ⟨_, hst γ _ hy⟩ : ↥Y₂) = ⟨_, hst₂ γ y₂ h₂⟩ := by
          apply Subtype.ext
          show resL₂ (O := O) a₁ a₂ (blk act (Fin.append x₁ x₂) γ (Fin.append y₁ y₂)) = _
          rw [blk_append, resL₂_append]
        have e2 : (ρ ⟨_, hy⟩ : ↥Y₂) = ⟨y₂, h₂⟩ := by
          apply Subtype.ext
          show resL₂ (O := O) a₁ a₂ (Fin.append y₁ y₂) = _
          rw [resL₂_append]
        simp only [LinearMap.comp_apply]
        rw [e1, e2]
        exact hφ γ ⟨y₂, h₂⟩
      · funext g
        simp only [LinearMap.comp_apply]
        congr 2
        apply Subtype.ext
        show _ = resL₂ (O := O) a₁ a₂ (blk act (Fin.append x₁ x₂) (gl g) (Fin.append E₁ E₂) - Fin.append E₁ E₂)
        rw [hEq, resL₂_append]

theorem hasPres_finset (F : Finset (G → C)) (h : ∀ c ∈ F, HasPres (O := O) act W gl out {c}) :
    HasPres (O := O) act W gl out (F : Set (G → C)) := by
  classical
  induction F using Finset.induction_on with
  | empty => simpa using hasPres_empty (O := O) act W gl out
  | insert c F hc ih =>
    rw [Finset.coe_insert, Set.insert_eq]
    exact hasPres_union act W gl out (h c (Finset.mem_insert_self c F))
      (ih fun c' hc' => h c' (Finset.mem_insert_of_mem hc'))

end GlobalTheory.Pass.LocDual.OneX.Combine

end

namespace GlobalTheory.Pass.LocDual.OneX

open GlobalTheory.Pass.LocDual.OneX.Combine in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem cutCoc_finset_common : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (Xs : Set (D.nd.X i)) {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))
    (F : Finset (Br.G D.nbr i w hw → (Fin k → Br.LL D.nbr i w hw) ⧸ (Br.locLat D.nbr i w hw M).T)),
    (F : Set (Br.G D.nbr i w hw → (Fin k → Br.LL D.nbr i w hw) ⧸ (Br.locLat D.nbr i w hw M).T)) ⊆
    cutCoc i w hw r Xs M →
    ∃ (a : ℕ) (x : Fin a → ↥Xs) (E : Fin a → Fin D.R.nV → KK D.nd i)
    (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i)), Y.FG ∧
    ∃ (hst : ∀ γ : GE D.nd, ∀ y ∈ Y, actK i r Xs x γ y ∈ Y) (hE : ∀ γ : GE D.nd, actK i r Xs x γ E - E ∈ Y),
    ∀ c ∈ F, ∃ φ : ↥Y →ₗ[D.nd.O i] KOG (D.nd.O i) k,
    (∀ (γ : GE D.nd) (y : ↥Y), φ ⟨_, hst γ y.1 y.2⟩ = WKG M γ (φ y)) ∧
    c = fun g => Br.phi (D.nbr i w hw) k (φ ⟨_, hE (gl i w hw g)⟩) := by
  intro D i w hw r Xs k M F hF
  have h := hasPres_finset (O := D.nd.O i)
    (fun (x : ↥Xs) (γ : GE D.nd) (v : Fin D.R.nV → KK D.nd i) => (mapM (toK D.nd i) (rTwO D.nd i r x) γ).mulVec v)
    (fun γ q => WKG M γ q) (gl i w hw) (Br.phi (D.nbr i w hw) k) F ?_
  · exact h
  · intro c hc
    obtain ⟨a, x, hx, E, Y, hY, hst, hE, φ, hφ, rfl⟩ := hF (Finset.mem_coe.2 hc)
    refine ⟨a, fun j => ⟨x j, hx j⟩, E, Y, hY, hst, hE, ?_⟩
    intro c' hc'
    rw [Set.mem_singleton_iff] at hc'
    subst hc'
    exact ⟨φ, hφ, rfl⟩

end GlobalTheory.Pass.LocDual.OneX
end

section
namespace GlobalTheory.ComplementedSup

theorem complemented_sup :
    (let d1 : {K : Type} → [inst : Field K] → {Γ V : Type} → [inst_1 : AddCommGroup V] → [inst_2 : Module K V] → (Γ → V →ₗ[K] V) → Submodule K V → Prop := @(fun {K : Type} [Field K] {Γ V : Type} [AddCommGroup V] [Module K V] (f : Γ → V →ₗ[K] V) (S : Submodule K V) ↦ ∀ (γ : Γ), ∀ v ∈ S, (f γ : V → V) v ∈ S); let d2 : {K : Type} → [inst : Field K] → {Γ V : Type} → [inst_1 : AddCommGroup V] → [inst_2 : Module K V] → (Γ → V →ₗ[K] V) → Submodule K V → Prop := @(fun {K : Type} [Field K] {Γ V : Type} [AddCommGroup V] [Module K V] (f : Γ → V →ₗ[K] V) (Y : Submodule K V) ↦ ∀ (W : Submodule K V), d1 f W → W ≤ Y → ∃ (C : Submodule K V), d1 f C ∧ C ≤ Y ∧ W ⊓ C = ⊥ ∧ W ⊔ C = Y); ∀ {K : Type} [inst : Field K] {Γ V : Type} [inst_1 : AddCommGroup V] [inst_2 : Module K V] {f : Γ → V →ₗ[K] V} {X U : Submodule K V}, d1 f X → d1 f U → d2 f X → d2 f U → d2 f (X ⊔ U)) := by
  intro d1 d2 K _ Γ V _ _ f X U hX hU hXc hUc

  have hsup : ∀ A B : Submodule K V, d1 f A → d1 f B → d1 f (A ⊔ B) := by
    intro A B hA hB γ v hv
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
    rw [map_add]
    exact Submodule.add_mem_sup (hA γ a ha) (hB γ b hb)
  have hinf : ∀ A B : Submodule K V, d1 f A → d1 f B → d1 f (A ⊓ B) := by
    intro A B hA hB γ v hv
    exact Submodule.mem_inf.mpr ⟨hA γ v (Submodule.mem_inf.mp hv).1, hB γ v (Submodule.mem_inf.mp hv).2⟩
  intro W hW hWle

  obtain ⟨D, hD, hDX, hD1, hD2⟩ := hXc (W ⊓ X) (hinf W X hW hX) inf_le_right
  obtain ⟨B, hB, hBU, hB1, hB2⟩ := hUc ((W ⊔ X) ⊓ U) (hinf _ U (hsup W X hW hX) hU) inf_le_right
  refine ⟨D ⊔ B, hsup D B hD hB, sup_le_sup hDX hBU, ?_, ?_⟩
  ·
    rw [eq_bot_iff]
    intro w hw
    obtain ⟨hwW, hwDB⟩ := Submodule.mem_inf.mp hw
    obtain ⟨d, hd, b, hb, rfl⟩ := Submodule.mem_sup.mp hwDB
    have hbA : b ∈ (W ⊔ X) ⊓ U := by
      refine Submodule.mem_inf.mpr ⟨?_, hBU hb⟩
      have hbd : b = (d + b) - d := by abel
      rw [hbd]
      exact Submodule.sub_mem _ (Submodule.mem_sup_left hwW) (Submodule.mem_sup_right (hDX hd))
    have hb0 : b = 0 := by
      have hb' : b ∈ (W ⊔ X) ⊓ U ⊓ B := Submodule.mem_inf.mpr ⟨hbA, hb⟩
      rw [hB1] at hb'
      exact (Submodule.mem_bot K).mp hb'
    subst hb0
    rw [add_zero] at hwW ⊢
    have hd' : d ∈ W ⊓ X ⊓ D := Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨hwW, hDX hd⟩, hd⟩
    rw [hD1] at hd'
    exact hd'
  · apply le_antisymm
    · exact sup_le hWle (sup_le_sup hDX hBU)
    · have hX' : X ≤ W ⊔ (D ⊔ B) := by
        rw [← hD2]
        exact sup_le (le_trans inf_le_left le_sup_left) (le_trans le_sup_left le_sup_right)
      have hU' : U ≤ W ⊔ (D ⊔ B) := by
        rw [← hB2]
        exact sup_le (le_trans inf_le_left (sup_le le_sup_left hX')) (le_trans le_sup_right le_sup_right)
      exact sup_le hX' hU'

end GlobalTheory.ComplementedSup
end

section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition GlobalTheory.Pass.LocDual GlobalTheory.Pass.LocDual.OneX

namespace GlobalTheory.BlockSum

section General

variable {K : Type} [Field K] {Γ : Type}

def StableUnder {V : Type} [AddCommGroup V] [Module K V] (f : Γ → V →ₗ[K] V)
    (S : Submodule K V) : Prop :=
  ∀ γ, ∀ v ∈ S, f γ v ∈ S

def HasRelCompl {V : Type} [AddCommGroup V] [Module K V] (f : Γ → V →ₗ[K] V)
    (Y : Submodule K V) : Prop :=
  ∀ W : Submodule K V, StableUnder f W → W ≤ Y →
    ∃ C : Submodule K V, StableUnder f C ∧ C ≤ Y ∧ W ⊓ C = ⊥ ∧ W ⊔ C = Y

variable {V : Type} [AddCommGroup V] [Module K V] {f : Γ → V →ₗ[K] V}

theorem hasRelCompl_sup {X U : Submodule K V} (hXs : StableUnder f X) (hUs : StableUnder f U)
    (hX : HasRelCompl f X) (hU : HasRelCompl f U) : HasRelCompl f (X ⊔ U) := by
  first
  | exact @_root_.GlobalTheory.ComplementedSup.complemented_sup
  | exact _root_.GlobalTheory.ComplementedSup.complemented_sup
  | (apply _root_.GlobalTheory.ComplementedSup.complemented_sup <;> assumption)
  | (intros; apply _root_.GlobalTheory.ComplementedSup.complemented_sup <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ComplementedSup.complemented_sup <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ComplementedSup.complemented_sup ..)

end General

section Blocks

variable {K : Type} [Field K] {Γ : Type} {ι : Type} [DecidableEq ι]
  {n : Type} [Fintype n] [DecidableEq n]

def blockAct (ρ : Γ → ι → Matrix n n K) (γ : Γ) : (ι → n → K) →ₗ[K] (ι → n → K) :=
  LinearMap.pi (fun b => (Matrix.mulVecLin (ρ γ b)).comp (LinearMap.proj b))

theorem blockAct_apply (ρ : Γ → ι → Matrix n n K) (γ : Γ) (v : ι → n → K) (b : ι) :
    blockAct ρ γ v b = (ρ γ b).mulVec (v b) := rfl

def blockSub (s : Set ι) : Submodule K (ι → n → K) where
  carrier := {v | ∀ b, b ∉ s → v b = 0}
  add_mem' := by
    intro v w hv hw b hb
    simp [hv b hb, hw b hb]
  zero_mem' := by
    intro b _
    rfl
  smul_mem' := by
    intro c v hv b hb
    simp [hv b hb]

theorem blockSub_stable (ρ : Γ → ι → Matrix n n K) (s : Set ι) :
    StableUnder (blockAct ρ) (blockSub s : Submodule K (ι → n → K)) := by
  intro γ v hv b hb
  rw [blockAct_apply, hv b hb, Matrix.mulVec_zero]

theorem blockSub_mono {s t : Set ι} (h : s ⊆ t) :
    (blockSub s : Submodule K (ι → n → K)) ≤ blockSub t :=
  fun _ hv b hb => hv b (fun hs => hb (h hs))

theorem blockSub_empty : (blockSub (∅ : Set ι) : Submodule K (ι → n → K)) = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  rw [Submodule.mem_bot]
  funext b
  exact hv b (Set.notMem_empty b)

theorem blockSub_univ : (blockSub (Set.univ : Set ι) : Submodule K (ι → n → K)) = ⊤ := by
  rw [eq_top_iff]
  intro v _ b hb
  exact absurd (Set.mem_univ b) hb

theorem blockSub_insert (b : ι) (s : Set ι) :
    (blockSub (insert b s) : Submodule K (ι → n → K)) = blockSub s ⊔ blockSub {b} := by
  apply le_antisymm
  · intro v hv
    refine Submodule.mem_sup.mpr ⟨Function.update v b 0, ?_, Pi.single b (v b), ?_, ?_⟩
    · intro c hc
      by_cases h : c = b
      · subst h; simp
      · rw [Function.update_of_ne h]
        exact hv c (by simp [h, hc])
    · intro c hc
      have h : c ≠ b := by simpa using hc
      simp [h]
    · funext c
      by_cases h : c = b
      · subst h; simp
      · simp [h]
  · exact sup_le (blockSub_mono (Set.subset_insert _ _))
      (blockSub_mono (Set.singleton_subset_iff.mpr (Set.mem_insert _ _)))

def BlockHasCompl (ρ : Γ → ι → Matrix n n K) (b : ι) : Prop :=
  ∀ S : Submodule K (n → K), (∀ γ, ∀ y ∈ S, (ρ γ b).mulVec y ∈ S) →
    ∃ D : Submodule K (n → K), (∀ γ, ∀ y ∈ D, (ρ γ b).mulVec y ∈ D) ∧ IsCompl S D

theorem hasRelCompl_single (ρ : Γ → ι → Matrix n n K) (b : ι) (hb : BlockHasCompl ρ b) :
    HasRelCompl (blockAct ρ) (blockSub ({b} : Set ι) : Submodule K (ι → n → K)) := by
  intro W hW hWY
  obtain ⟨D', hD's, hc⟩ := hb (W.map (LinearMap.proj b)) (by
    rintro γ _ ⟨v, hv, rfl⟩
    exact ⟨blockAct ρ γ v, hW γ v hv, rfl⟩)
  have hDle : D'.map (LinearMap.single K (fun _ : ι => n → K) b) ≤ blockSub {b} := by
    rintro _ ⟨y, _, rfl⟩ c hc
    have h : c ≠ b := by simpa using hc
    simp [h]
  refine ⟨D'.map (LinearMap.single K (fun _ : ι => n → K) b), ?_, hDle, ?_, ?_⟩
  · rintro γ _ ⟨y, hy, rfl⟩
    refine ⟨(ρ γ b).mulVec y, hD's γ y hy, ?_⟩
    funext c
    rw [blockAct_apply]
    by_cases h : c = b
    · subst h; simp
    · simp [h]
  · rw [eq_bot_iff]
    intro v hv
    obtain ⟨hvW, hvD⟩ := Submodule.mem_inf.mp hv
    obtain ⟨y, hy, rfl⟩ := hvD
    have hy0 : y = 0 := by
      have hm : y ∈ W.map (LinearMap.proj b) ⊓ D' :=
        Submodule.mem_inf.mpr ⟨⟨_, hvW, by simp⟩, hy⟩
      rw [hc.inf_eq_bot] at hm
      exact (Submodule.mem_bot K).mp hm
    subst hy0
    simp
  · apply le_antisymm (sup_le hWY hDle)
    intro u hu
    have hub : u b ∈ W.map (LinearMap.proj b) ⊔ D' := by
      rw [hc.sup_eq_top]; trivial
    obtain ⟨s', ⟨v, hv, rfl⟩, d', hd', hsum⟩ := Submodule.mem_sup.mp hub
    refine Submodule.mem_sup.mpr ⟨v, hv, Pi.single b d', ⟨d', hd', by simp⟩, ?_⟩
    funext c
    by_cases h : c = b
    · subst h
      simpa using hsum
    · have h1 : u c = 0 := hu c (by simpa using h)
      have h2 : v c = 0 := hWY hv c (by simpa using h)
      simp [h, h1, h2]

theorem hasRelCompl_finset (ρ : Γ → ι → Matrix n n K) (hblk : ∀ b, BlockHasCompl ρ b)
    (s : Finset ι) :
    HasRelCompl (blockAct ρ) (blockSub (s : Set ι) : Submodule K (ι → n → K)) := by
  refine Finset.induction_on s ?_ ?_
  · intro W _ hWY
    rw [Finset.coe_empty, blockSub_empty] at hWY ⊢
    refine ⟨⊥, fun γ v hv => ?_, le_rfl, inf_bot_eq _, ?_⟩
    · rw [(Submodule.mem_bot K).mp hv, map_zero]; exact Submodule.zero_mem _
    · rw [sup_bot_eq]; exact le_antisymm hWY bot_le
  · intro b s _ ih
    rw [Finset.coe_insert, blockSub_insert]
    exact hasRelCompl_sup (blockSub_stable ρ _) (blockSub_stable ρ _) ih
      (hasRelCompl_single ρ b (hblk b))

theorem exists_stable_compl [Fintype ι] (ρ : Γ → ι → Matrix n n K)
    (hblk : ∀ b, BlockHasCompl ρ b) (W : Submodule K (ι → n → K))
    (hW : StableUnder (blockAct ρ) W) :
    ∃ C : Submodule K (ι → n → K), StableUnder (blockAct ρ) C ∧ IsCompl W C := by
  have h := hasRelCompl_finset ρ hblk Finset.univ W hW
    (by rw [Finset.coe_univ, blockSub_univ]; exact le_top)
  rw [Finset.coe_univ, blockSub_univ] at h
  obtain ⟨C, hCs, _, h1, h2⟩ := h
  exact ⟨C, hCs, ⟨disjoint_iff.mpr h1, codisjoint_iff.mpr h2⟩⟩

end Blocks

end GlobalTheory.BlockSum

namespace GlobalTheory.BlockSum

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem exists_stable_compl_actK : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (Xs : Set (D.nd.X i)), GoodR D.nd i r → ∀ {a : ℕ} (x : Fin a → ↥Xs)
    (W : Submodule (KK D.nd i) (Fin a → Fin D.R.nV → KK D.nd i)),
    (∀ γ : GE D.nd, ∀ v ∈ W, actK i r Xs x γ v ∈ W) →
    ∃ C : Submodule (KK D.nd i) (Fin a → Fin D.R.nV → KK D.nd i),
    (∀ γ : GE D.nd, ∀ v ∈ C, actK i r Xs x γ v ∈ C) ∧ IsCompl W C := by
  intro D i r Xs hG a x W hW
  let ρ : GE D.nd → Fin a → Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i) :=
    fun γ b => (mapM (toK D.nd i) (rTwO D.nd i r ↑(x b))) γ
  have hact : ∀ γ v, actK i r Xs x γ v = blockAct ρ γ v := fun γ v => rfl
  have hblk : ∀ b, BlockHasCompl ρ b := by
    intro b
    have hss := (hG ↑(x b)).2.1
    set c : GE D.nd → KK D.nd i :=
      fun γ => toK D.nd i ((((chiU D.nd i 1)⁻¹ γ : (D.nd.O i)ˣ)) : D.nd.O i) with hcdef
    have hrel : ∀ γ, ρ γ b = c γ • (↑(mapRep (algebraMap (D.nd.O i) (Kf D.nd i)) (r ↑(x b)) γ) :
        Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) := by
      intro γ
      ext j k
      simp [ρ, c, mapM, rTwO, twistM, mapRep, rO]
    have hc0 : ∀ γ, c γ ≠ 0 := fun γ =>
      ((((chiU D.nd i 1)⁻¹ γ : (D.nd.O i)ˣ)).isUnit.map (toK D.nd i)).ne_zero
    intro S hS
    obtain ⟨D', hD', hcompl⟩ := hss S (by
      intro g y hy
      have h := hS g y hy
      rw [hrel, Matrix.smul_mulVec] at h
      have h2 := S.smul_mem (c g)⁻¹ h
      rwa [smul_smul, inv_mul_cancel₀ (hc0 g), one_smul] at h2)
    refine ⟨D', fun g y hy => ?_, hcompl⟩
    rw [hrel, Matrix.smul_mulVec]
    exact D'.smul_mem _ (hD' g y hy)
  obtain ⟨C, hCs, hc⟩ := exists_stable_compl ρ hblk W (fun γ v hv => by
    rw [← hact]; exact hW γ v hv)
  exact ⟨C, fun γ v hv => by rw [hact]; exact hCs γ v hv, hc⟩

end GlobalTheory.BlockSum
end

section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition GlobalTheory.Pass.LocDual GlobalTheory.Pass.LocDual.OneX

noncomputable section

namespace GlobalTheory.Pass.LocDual.OneX

section VecGen
variable {K L : Type} [Field K] [Field L] (φ : K →+* L) (a n : ℕ)

def vecS : (Fin a → Fin n → K) →ₛₗ[φ] (Fin a → Fin n → L) where
  toFun v := fun b j => φ (v b j)
  map_add' u v := by funext b j; simp
  map_smul' c v := by funext b j; simp

variable {φ a n}

theorem vecS_apply (v : Fin a → Fin n → K) (b : Fin a) (j : Fin n) : vecS φ a n v b j = φ (v b j) := rfl

theorem span_vecS_span (S : Set (Fin a → Fin n → K)) :
    Submodule.span L (vecS φ a n '' (Submodule.span K S : Set (Fin a → Fin n → K))) =
      Submodule.span L (vecS φ a n '' S) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨v, hv, rfl⟩
    induction hv using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul c x _ hx => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hx
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

theorem finrank_span_vecS_le (W : Submodule K (Fin a → Fin n → K)) :
    finrank L (Submodule.span L (vecS φ a n '' (W : Set (Fin a → Fin n → K)))) ≤ finrank K W := by
  let b := Module.finBasis K W
  let g : Fin (Module.finrank K W) → (Fin a → Fin n → L) := fun i => vecS φ a n (b i)
  have hle : Submodule.span L (vecS φ a n '' (W : Set (Fin a → Fin n → K))) ≤ Submodule.span L (Set.range g) := by
    rw [Submodule.span_le]
    rintro _ ⟨w, hw, rfl⟩
    have h : w = ∑ i, b.repr ⟨w, hw⟩ i • (b i : Fin a → Fin n → K) := by
      have := congrArg W.subtype (b.sum_repr ⟨w, hw⟩)
      rw [map_sum] at this
      exact this.symm
    rw [h, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have h1 := Submodule.finrank_mono hle
  have h2 : Module.finrank L (Submodule.span L (Set.range g)) ≤ Module.finrank K W := by
    have := finrank_range_le_card (R := L) g
    simpa [Set.finrank] using this
  exact h1.trans h2

theorem span_vecS_top : Submodule.span L (Set.range (vecS φ a n)) = ⊤ := by
  rw [eq_top_iff]
  intro u _
  have e : u = ∑ b, ∑ j, u b j • vecS φ a n (fun b'' j'' => if b'' = b ∧ j'' = j then 1 else 0) := by
    funext b' j'
    simp only [Finset.sum_apply, Pi.smul_apply, vecS_apply, smul_eq_mul, apply_ite φ, map_one, map_zero, mul_ite,
      mul_one, mul_zero, ite_and]
    simp [Finset.sum_ite_eq, Finset.sum_ite_eq']
  rw [e]
  exact Submodule.sum_mem _ fun b _ => Submodule.sum_mem _ fun j _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

theorem isCompl_span_vecS {W W' : Submodule K (Fin a → Fin n → K)} (h : IsCompl W W') :
    IsCompl (Submodule.span L (vecS φ a n '' (W : Set (Fin a → Fin n → K))))
      (Submodule.span L (vecS φ a n '' (W' : Set (Fin a → Fin n → K)))) := by
  set A := Submodule.span L (vecS φ a n '' (W : Set (Fin a → Fin n → K)))
  set B := Submodule.span L (vecS φ a n '' (W' : Set (Fin a → Fin n → K)))
  have hsup : A ⊔ B = ⊤ := by
    rw [eq_top_iff, ← span_vecS_top (φ := φ), Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    have hv : v ∈ W ⊔ W' := by rw [h.sup_eq_top]; trivial
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hv
    rw [map_add]
    exact add_mem (Submodule.mem_sup_left (Submodule.subset_span ⟨y, hy, rfl⟩))
      (Submodule.mem_sup_right (Submodule.subset_span ⟨z, hz, rfl⟩))
  have h1 : finrank L A ≤ finrank K W := finrank_span_vecS_le W
  have h2 : finrank L B ≤ finrank K W' := finrank_span_vecS_le W'
  have h3 := Submodule.finrank_add_eq_of_isCompl h
  have h4 := Submodule.finrank_sup_add_finrank_inf_eq A B
  rw [hsup, finrank_top] at h4
  have hK : finrank K (Fin a → Fin n → K) = a * n := by
    rw [Module.finrank_pi_fintype]; simp [Module.finrank_fin_fun]
  have hL : finrank L (Fin a → Fin n → L) = a * n := by
    rw [Module.finrank_pi_fintype]; simp [Module.finrank_fin_fun]
  have hinf : A ⊓ B = ⊥ := by
    rw [← Submodule.finrank_eq_zero]; omega
  exact ⟨disjoint_iff.2 hinf, codisjoint_iff.2 hsup⟩

end VecGen

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem isSummandTw_XG : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (Xs : Set (D.nd.X i)) (hr : GoodR D.nd i r) {a : ℕ} (x : Fin a → ↥Xs)
    (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i))
    (hst : ∀ γ : GE D.nd, ∀ y ∈ Y, actK i r Xs x γ y ∈ Y),
    (∃ C : Submodule (KK D.nd i) (Fin a → Fin D.R.nV → KK D.nd i),
    (∀ γ : GE D.nd, ∀ v ∈ C, actK i r Xs x γ v ∈ C) ∧
    IsCompl (Submodule.span (KK D.nd i) (Y : Set (Fin a → Fin D.R.nV → KK D.nd i))) C) →
    IsSummandTw i w hw r Xs (XG i w hw r Xs hr x Y hst) := by
  intro D i w hw r Xs hr a x Y hst ⟨C, hC, hYC⟩
  have hspan : spanL i w hw Y = Submodule.span _ (vecS (Br.toLLK (D.nbr i w hw)) a D.R.nV ''
      (Submodule.span (KK D.nd i) (Y : Set (Fin a → Fin D.R.nV → KK D.nd i)) : Set (Fin a → Fin D.R.nV → KK D.nd i))) := by
    rw [span_vecS_span]; rfl
  refine ⟨a, x, (spanL i w hw Y).subtype, Subtype.val_injective, fun g v => rfl,
    Submodule.span _ (vecL i w hw '' (C : Set (Fin a → Fin D.R.nV → KK D.nd i))), ?_, ?_⟩
  · intro g u hu
    have hle : Submodule.span (Br.LL D.nbr i w hw) (vecL i w hw '' (C : Set (Fin a → Fin D.R.nV → KK D.nd i))) ≤
        (Submodule.span (Br.LL D.nbr i w hw) (vecL i w hw '' (C : Set (Fin a → Fin D.R.nV → KK D.nd i)))).comap
          ((sumG i w hw r Xs hr x).ρ g) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨v, hv, rfl⟩
      show (sumG i w hw r Xs hr x).ρ g (vecL i w hw v) ∈
        Submodule.span (Br.LL D.nbr i w hw) (vecL i w hw '' (C : Set (Fin a → Fin D.R.nV → KK D.nd i)))
      rw [sumG_vecL]
      exact Submodule.subset_span ⟨_, hC _ v hv, rfl⟩
    exact hle hu
  · have key : IsCompl (spanL i w hw Y)
        (Submodule.span (Br.LL D.nbr i w hw) (vecL i w hw '' (C : Set (Fin a → Fin D.R.nV → KK D.nd i)))) := by
      rw [hspan]
      exact isCompl_span_vecS hYC
    convert key using 1
    exact Submodule.range_subtype _

end GlobalTheory.Pass.LocDual.OneX

end
end

section
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition GlobalTheory.Pass.LocDual GlobalTheory.Pass.LocDual.OneX
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.Pass.LocDual.OneX

variable {D : D7} (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))

def vecLS (a : ℕ) :
    (Fin a → Fin D.R.nV → KK D.nd i) →ₛₗ[(D.nbr i w hw).eO.toRingHom]
      (Fin a → Fin D.R.nV → Br.LL D.nbr i w hw) where
  toFun := vecL i w hw
  map_add' u v := by
    funext b j
    simp [vecL]
  map_smul' c v := by
    funext b j
    simp only [vecL, Pi.smul_apply, Algebra.smul_def, map_mul, Br.toLLK_alg]
    rfl

theorem eO_surj : RingHomSurjective (D.nbr i w hw).eO.toRingHom :=
  ⟨(D.nbr i w hw).eO.surjective⟩

theorem latY_map {a : ℕ} (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i)) :
    (latY i w hw Y).map ((spanL i w hw Y).subtype.restrictScalars (Br.OLL D.nbr i w hw)) =
      Submodule.span (Br.OLL D.nbr i w hw) (vecL i w hw '' (Y : Set _)) := by
  rw [latY, Submodule.map_span]
  congr 1
  ext v
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact hu
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨vecL i w hw y, Submodule.subset_span ⟨y, hy, rfl⟩⟩, ⟨y, hy, rfl⟩, rfl⟩

theorem latY_fg {a : ℕ} (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i)) (hY : Y.FG) :
    (latY i w hw Y).FG := by
  have hinj : Function.Injective ((spanL i w hw Y).subtype.restrictScalars (Br.OLL D.nbr i w hw)) :=
    Subtype.val_injective
  apply Submodule.fg_of_fg_map_injective _ hinj
  rw [latY_map]
  haveI := eO_surj i w hw
  obtain ⟨S, rfl⟩ := hY
  have h : ∀ T : Set (Fin a → Fin D.R.nV → KK D.nd i), vecL i w hw '' T = (vecLS i w hw a) '' T :=
    fun _ => rfl
  rw [h, ← Submodule.map_coe, Submodule.span_eq, Submodule.map_span]
  classical
  exact ⟨(S.image (vecLS i w hw a)), by rw [Finset.coe_image]⟩

theorem span_stable_of_gen {R K M : Type} [CommRing R] [Field K] [Algebra R K] [AddCommGroup M] [Module K M]
    [Module R M] (hT : IsScalarTower R K M) (f : M →ₗ[K] M) (s : Set M) (h : ∀ v ∈ s, f v ∈ s) :
    ∀ v ∈ Submodule.span R s, f v ∈ Submodule.span R s := by
  intro v hv
  haveI := hT
  have key : Submodule.span R s ≤ (Submodule.span R s).comap (f.restrictScalars R) :=
    Submodule.span_le.2 fun u hu => Submodule.subset_span (h u hu)
  exact key hv

theorem latY_stable (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (Xs : Set (D.nd.X i)) (hr : GoodR D.nd i r) {a : ℕ} (x : Fin a → ↥Xs)
    (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i))
    (hst : ∀ γ : GE D.nd, ∀ y ∈ Y, actK i r Xs x γ y ∈ Y) :
    ∀ g, ∀ u ∈ latY i w hw Y,
      subRho (sumG i w hw r Xs hr x) (spanL i w hw Y) (spanL_stable i w hw r Xs hr x Y hst) g u ∈ latY i w hw Y := by
  intro g
  apply span_stable_of_gen (K := Br.LL D.nbr i w hw)
  · exact ⟨fun c k u => Subtype.ext (smul_assoc c k (u.1 : Fin a → Fin D.R.nV → Br.LL D.nbr i w hw))⟩
  rintro v ⟨y, hy, hv⟩
  refine ⟨actK i r Xs x (gl i w hw g) y, hst _ y hy, ?_⟩
  show _ = (sumG i w hw r Xs hr x).ρ g (v : Fin a → Fin D.R.nV → Br.LL D.nbr i w hw)
  rw [← hv, sumG_vecL]

theorem latY_span {a : ℕ} (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i)) :
    Submodule.span (Br.LL D.nbr i w hw) ((latY i w hw Y : Set ↥(spanL i w hw Y))) = ⊤ := by
  apply Submodule.map_injective_of_injective (spanL i w hw Y).injective_subtype
  rw [Submodule.map_span, Submodule.map_subtype_top]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨u, -, rfl⟩
    exact u.2
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨y, hy, rfl⟩
    apply Submodule.subset_span
    exact ⟨⟨vecL i w hw y, Submodule.subset_span ⟨y, hy, rfl⟩⟩,
      Submodule.subset_span ⟨y, hy, rfl⟩, rfl⟩

theorem latY_free {a : ℕ} (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i)) (hY : Y.FG) :
    Module.Free (Br.OLL D.nbr i w hw) ↥(latY i w hw Y) := by
  haveI : Module.Finite (Br.OLL D.nbr i w hw) ↥(latY i w hw Y) :=
    Module.Finite.iff_fg.2 (latY_fg i w hw Y hY)
  haveI : NoZeroSMulDivisors (Br.OLL D.nbr i w hw) ↥(latY i w hw Y) := by
    constructor
    intro c u h
    by_cases hc : c = 0
    · exact Or.inl hc
    right
    have h1 : ((c • u : ↥(latY i w hw Y)) : ↥(spanL i w hw Y)) = 0 := by rw [h]; rfl
    have h2 : ((algebraMap (Br.OLL D.nbr i w hw) (Br.LL D.nbr i w hw) c) • (u : ↥(spanL i w hw Y))) = 0 := by
      rw [algebraMap_smul]; exact h1
    have hc' : algebraMap (Br.OLL D.nbr i w hw) (Br.LL D.nbr i w hw) c ≠ 0 := by
      intro h0; apply hc; exact Subtype.val_injective h0
    have := (smul_eq_zero.1 h2).resolve_left hc'
    exact Subtype.ext this
  exact Module.free_of_finite_type_torsion_free'

theorem latY_lattice : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (Xs : Set (D.nd.X i)) (hr : GoodR D.nd i r) {a : ℕ} (x : Fin a → ↥Xs)
    (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i))
    (hst : ∀ γ : GE D.nd, ∀ y ∈ Y, actK i r Xs x γ y ∈ Y), Y.FG →
    ∃ LY : Lattice (O := Br.OLL D.nbr i w hw) (XG i w hw r Xs hr x Y hst).ρ, LY.T = latY i w hw Y := by
  intro D i w hw r Xs hr a x Y hst hY
  exact ⟨{ T := latY i w hw Y
           stable := latY_stable i w hw r Xs hr x Y hst
           fg := latY_fg i w hw Y hY
           free := latY_free i w hw Y hY
           span := latY_span i w hw Y }, rfl⟩

end GlobalTheory.Pass.LocDual.OneX

end
end

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition GlobalTheory.Pass.LocDual GlobalTheory.Pass.LocDual.OneX
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localIntegerSpanOfImage_is_stable_lattice : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (Xs : Set (D.nd.X i)) (hr : GoodR D.nd i r) {a : ℕ} (x : Fin a → ↥Xs)
    (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i))
    (hst : ∀ γ : GE D.nd, ∀ y ∈ Y, actK i r Xs x γ y ∈ Y), Y.FG →
    ∃ LY : Lattice (O := Br.OLL D.nbr i w hw) (XG i w hw r Xs hr x Y hst).ρ, LY.T = latY i w hw Y := by
  atlas_forward_decl GlobalTheory.Pass.LocDual.OneX.latY_lattice
end

section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition GlobalTheory.Pass.LocDual GlobalTheory.Pass.LocDual.OneX

noncomputable section

namespace GlobalTheory.Pass.LocDual.OneX

variable {D : D7} (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))

theorem isTopRingLL : IsTopologicalRing (Br.LL D.nbr i w hw) :=
  (goodO_ringOfIntegers (D.nd.l i) (D.nbr i w hw).LL).2.2.2.1

theorem vecL_sub {a : ℕ} (u v : Fin a → Fin D.R.nV → KK D.nd i) :
    vecL i w hw (u - v) = vecL i w hw u - vecL i w hw v := by
  funext b j
  simp [vecL]

variable (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (Xs : Set (D.nd.X i))

theorem sumG_crys (hr : GoodR D.nd i r) (hAdm : FontaineAtPlacesOverL (D := D)) {a : ℕ} (x : Fin a → ↥Xs)
    (K' : FinExt (D.nd.l i)) (h : (D.nbr i w hw).Kw.1 ≤ K'.1)
    (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex)
    (hS : ∀ (g : ↥(GK (D.nbr i w hw).Kw)) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'),
      ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw).actB g (algebraMap ↥(K0 K') (D.loc (D.nd.l i)).R.B c) =
        algebraMap ↥(K0 K') (D.loc (D.nd.l i)).R.B c')
    (hpot : ∀ y : ↥Xs, (pc (D.loc (D.nd.l i)) h hN hF hS).IsPotCrys
      (matRep (Br.loc D.nbr i w hw (rTwO D.nd i r y)))) :
    IsCrys ((D.loc (D.nd.l i)).PD K')
      ((sumG i w hw r Xs hr x).ρ.comp (Subgroup.inclusion (GK_le h))) := by
  haveI := isTopRingLL i w hw
  have hc' : ∀ (y : ↥Xs) (v : Fin D.R.nV → Br.LL D.nbr i w hw),
      Continuous fun g => ((Br.loc D.nbr i w hw (rTwO D.nd i r y)).comp (Subgroup.inclusion (GK_le h)) g).mulVec v :=
    fun y v => (contTw i w hw r Xs hr y v).comp (continuous_inclusion (GK_le h))
  have hF' := hAdm (D.nd.l i) K' (D.nbr i w hw).LL
  have hcr : ∀ y : ↥Xs, IsCrys ((D.loc (D.nd.l i)).PD K')
      (matRep ((Br.loc D.nbr i w hw (rTwO D.nd i r y)).comp (Subgroup.inclusion (GK_le h)))) := fun y =>
    (GlobalTheory.T.potentiallyCrystalline_module_eq_crystalline_restriction (D.nd.l i) (D.loc (D.nd.l i)) (D.nbr i w hw).Kw K' (D.nbr i w hw).LL h hN hF hS _
      (matRep (Br.loc D.nbr i w hw (rTwO D.nd i r y)))).2.1 (hpot y)
  exact (cj_sum (Qp := ℚ_[D.nd.l i]) (O := ↥(OL (D.nbr i w hw).LL))
    (fun y : ↥Xs => (Br.loc D.nbr i w hw (rTwO D.nd i r y)).comp (Subgroup.inclusion (GK_le h))) hc' hF'
    (S := fun _ => Set.univ) (fun y => ⟨hcr y, fun τ b _ => Set.mem_univ _⟩) a x).1

theorem yfun_val {a : ℕ} (hr : GoodR D.nd i r) (x : Fin a → ↥Xs)
    (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i))
    (E : Fin a → Fin D.R.nV → KK D.nd i) (hE : ∀ γ : GE D.nd, actK i r Xs x γ E - E ∈ Y)
    (g : Br.G D.nbr i w hw) :
    (spanL i w hw Y).subtype (yfun i w hw r Xs x Y E hE g) =
      (sumG i w hw r Xs hr x).ρ g (vecL i w hw E) - (show (sumG i w hw r Xs hr x).V from vecL i w hw E) := by
  rw [sumG_vecL]
  exact vecL_sub i w hw _ _

end GlobalTheory.Pass.LocDual.OneX

end

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem GlobalTheory.Pass.LocDual.OneX.yfun_Z1fT : ∀ (D : D7), FontaineAtPlacesOverL (D := D) → ∀ (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (hr : GoodR D.nd i r)
    (Xs : Set (D.nd.X i)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (n : ℕ), PotFam i w hw (fun x : ↥Xs => rTwO D.nd i r x) n → ∀ {a : ℕ} (x : Fin a → ↥Xs) (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i))
    (hst : ∀ γ : GE D.nd, ∀ y ∈ Y, actK i r Xs x γ y ∈ Y) (E : Fin a → Fin D.R.nV → KK D.nd i)
    (hE : ∀ γ : GE D.nd, actK i r Xs x γ E - E ∈ Y)
    (LY : Lattice (O := Br.OLL D.nbr i w hw) (XG i w hw r Xs hr x Y hst).ρ), LY.T = latY i w hw Y →
    (yfun i w hw r Xs x Y E hE : Br.G D.nbr i w hw → (XG i w hw r Xs hr x Y hst).V) ∈
    latticeFiniteCocycles (Br.PD D.loc D.nbr i w hw) LY := by
  intro D hAdm i r hr Xs w hw n hpf a x Y hst E hE LY hLY
  obtain ⟨K', h, hN, hF, hS, Sig, Fr, -, -, -, -, hall⟩ := hpf
  haveI := isTopRingLL i w hw
  have hF' := hAdm (D.nd.l i) K' (D.nbr i w hw).LL
  have hz : (yfun i w hw r Xs x Y E hE : Br.G D.nbr i w hw → (XG i w hw r Xs hr x Y hst).V) ∈
      finiteCocycles (Br.PD D.loc D.nbr i w hw) (XG i w hw r Xs hr x Y hst).ρ :=
    GlobalTheory.Pass.FinDesc.main (D.nd.l i) (D.loc (D.nd.l i)) (D.nbr i w hw).Kw K' (D.nbr i w hw).LL h hN hF
      (fun A₀ A₁ A₂ ι π h1 h2 h3 h4 h5 hA =>
        ⟨((hF'.1 A₀ A₁ A₂ ι π h1 h2 h3 h4 h5).1 hA).1, ((hF'.1 A₀ A₁ A₂ ι π h1 h2 h3 h4 h5).1 hA).2.1⟩)
      (sumG i w hw r Xs hr x) (XG i w hw r Xs hr x Y hst) (spanL i w hw Y).subtype
      (spanL i w hw Y).injective_subtype (fun g v => rfl)
      (sumG_crys i w hw r Xs hr hAdm x K' h hN hF hS (fun y => (hall y).1)) (vecL i w hw E)
      (yfun i w hw r Xs x Y E hE) (yfun_val i w hw r Xs hr x Y E hE)
  refine ⟨⟨hz.1, fun g _ => ?_⟩, hz⟩
  have hm : (yfun i w hw r Xs x Y E hE g : ↥(spanL i w hw Y)) ∈ latY i w hw Y :=
    Submodule.subset_span ⟨_, hE _, rfl⟩
  show yfun i w hw r Xs x Y E hE g ∈ LY.T
  rw [hLY]
  exact hm
end

section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition GlobalTheory.Pass.LocDual GlobalTheory.Pass.LocDual.OneX

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.Pass.LocDual.OneX.PushEq

variable {D : D7} (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))

instance eOsurjOneX : RingHomSurjective (D.nbr i w hw).eO.toRingHom := ⟨(D.nbr i w hw).eO.surjective⟩

instance eOinvOneX : RingHomInvPair (D.nbr i w hw).eO.toRingHom (D.nbr i w hw).eO.symm.toRingHom :=
  ⟨by ext; simp, by ext; simp⟩

instance eOinvOneX' : RingHomInvPair (D.nbr i w hw).eO.symm.toRingHom (D.nbr i w hw).eO.toRingHom :=
  ⟨by ext; simp, by ext; simp⟩

theorem vecL_add {a : ℕ} (u v : Fin a → Fin D.R.nV → KK D.nd i) :
    vecL i w hw (u + v) = vecL i w hw u + vecL i w hw v := by
  funext j m; simp [vecL]

theorem vecL_smul {a : ℕ} (c : D.nd.O i) (u : Fin a → Fin D.R.nV → KK D.nd i) :
    vecL i w hw (c • u) = (D.nbr i w hw).eO c • vecL i w hw u := by
  funext j m
  simp only [vecL, Pi.smul_apply, Algebra.smul_def, map_mul, Br.toLLK_alg]

theorem vecL_inj {a : ℕ} : Function.Injective (vecL (D := D) i w hw (a := a)) := by
  intro u v h
  funext j m
  exact (Br.toLLK (D.nbr i w hw)).injective (congrFun (congrFun h j) m)

section Y
variable {a : ℕ} (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i))

def toY : ↥Y →ₛₗ[(D.nbr i w hw).eO.toRingHom] ↥(spanL i w hw Y) where
  toFun y := ⟨vecL i w hw y.1, Submodule.subset_span ⟨y.1, y.2, rfl⟩⟩
  map_add' u v := Subtype.ext (vecL_add i w hw u.1 v.1)
  map_smul' c u := Subtype.ext (vecL_smul i w hw c u.1)

theorem toY_inj : Function.Injective (toY i w hw Y) := fun u v h =>
  Subtype.ext (vecL_inj i w hw (congrArg (fun z : ↥(spanL i w hw Y) => (z : Fin a → Fin D.R.nV → Br.LL D.nbr i w hw)) h))

theorem range_toY : LinearMap.range (toY i w hw Y) = latY i w hw Y := by
  apply le_antisymm
  · rintro _ ⟨y, rfl⟩
    exact Submodule.subset_span ⟨y.1, y.2, rfl⟩
  · refine Submodule.span_le.2 ?_
    rintro u ⟨y, hy, hu⟩
    exact ⟨⟨y, hy⟩, Subtype.ext hu⟩

def eY : ↥Y ≃ₛₗ[(D.nbr i w hw).eO.toRingHom] ↥(LinearMap.range (toY i w hw Y)) :=
  LinearEquiv.ofInjective _ (toY_inj i w hw Y)

variable {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))
  (T : Submodule (Br.OLL D.nbr i w hw) ↥(spanL i w hw Y)) (hT : T = latY i w hw Y)

def phiL (φ : ↥Y →ₗ[D.nd.O i] KOG (D.nd.O i) k) :
    ↥T →ₗ[Br.OLL D.nbr i w hw] ((Fin k → Br.LL D.nbr i w hw) ⧸ (Br.locLat D.nbr i w hw M).T) :=
  ((Br.phi (D.nbr i w hw) k).comp φ).comp
    ((eY i w hw Y).symm.toLinearMap.comp
      (LinearEquiv.ofEq _ _ (hT.trans (range_toY i w hw Y).symm)).toLinearMap)

theorem phiL_eq (φ : ↥Y →ₗ[D.nd.O i] KOG (D.nd.O i) k) (v : ↥T) (y : ↥Y)
    (hv : (v : ↥(spanL i w hw Y)) = toY i w hw Y y) :
    phiL i w hw Y M T hT φ v = Br.phi (D.nbr i w hw) k (φ y) := by
  have e : (eY i w hw Y).symm (LinearEquiv.ofEq _ _ (hT.trans (range_toY i w hw Y).symm) v) = y :=
    (eY i w hw Y).symm_apply_eq.2 (Subtype.ext hv)
  change Br.phi (D.nbr i w hw) k (φ ((eY i w hw Y).symm (LinearEquiv.ofEq _ _ (hT.trans (range_toY i w hw Y).symm) v))) = _
  rw [e]

end Y

theorem phi_WKG {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (g : Br.G D.nbr i w hw)
    (z : KOG (D.nd.O i) k) :
    Br.phi (D.nbr i w hw) k (WKG M (gl i w hw g) z) =
      repD (Br.locLat D.nbr i w hw M) g (Br.phi (D.nbr i w hw) k z) := by
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  change Submodule.Quotient.mk (Br.vecS (D.nbr i w hw) k ((matRep (mapM (toK D.nd i) M) _) u)) =
    Submodule.Quotient.mk ((matRep (Br.loc D.nbr i w hw M) g) (Br.vecS (D.nbr i w hw) k u))
  congr 1
  exact (loc_mulVec i w hw M g u).symm

theorem main : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (Xs : Set (D.nd.X i)) (hr : GoodR D.nd i r) {a : ℕ} (x : Fin a → ↥Xs)
    (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i))
    (hst : ∀ γ : GE D.nd, ∀ y ∈ Y, actK i r Xs x γ y ∈ Y) (E : Fin a → Fin D.R.nV → KK D.nd i)
    (hE : ∀ γ : GE D.nd, actK i r Xs x γ E - E ∈ Y) {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))
    (LY : Lattice (O := Br.OLL D.nbr i w hw) (XG i w hw r Xs hr x Y hst).ρ), LY.T = latY i w hw Y →
    ∀ φ : ↥Y →ₗ[D.nd.O i] KOG (D.nd.O i) k, (∀ (γ : GE D.nd) (y : ↥Y), φ ⟨_, hst γ y.1 y.2⟩ = WKG M γ (φ y)) →
    ∃ φ' : ↥LY.T →ₗ[Br.OLL D.nbr i w hw] ((Fin k → Br.LL D.nbr i w hw) ⧸ (Br.locLat D.nbr i w hw M).T),
    BlochKatoDuality.IsGMapD LY (Br.locLat D.nbr i w hw M) φ' ∧
    ∀ y : ↥(latticeCocycles LY), (y : Br.G D.nbr i w hw → (XG i w hw r Xs hr x Y hst).V) = yfun i w hw r Xs x Y E hE →
    BlochKatoDuality.pushD LY (Br.locLat D.nbr i w hw M) φ' y =
    fun g => Br.phi (D.nbr i w hw) k (φ ⟨_, hE (gl i w hw g)⟩) := by
  intro D i w hw r Xs hr a x Y hst E hE k M LY hT φ hφ
  refine ⟨phiL i w hw Y M LY.T hT φ, ?_, ?_⟩
  · intro g v
    obtain ⟨v, hv⟩ := v
    have hm : (show ↥(spanL i w hw Y) from v) ∈ LinearMap.range (toY i w hw Y) := by
      rw [range_toY, ← hT]; exact hv
    obtain ⟨y, rfl⟩ := hm
    have h1 : (show ↥(spanL i w hw Y) from (actT LY g ⟨toY i w hw Y y, hv⟩).1) =
        toY i w hw Y ⟨_, hst (gl i w hw g) y.1 y.2⟩ :=
      Subtype.ext (sumG_vecL i w hw r Xs hr x g y.1)
    refine (phiL_eq i w hw Y M LY.T hT φ _ _ h1).trans ?_
    refine Eq.trans ?_ (congrArg (repD (Br.locLat D.nbr i w hw M) g)
      (phiL_eq i w hw Y M LY.T hT φ ⟨_, hv⟩ y rfl).symm)
    rw [hφ]
    exact phi_WKG i w hw M g (φ y)
  · intro y hy
    funext g
    have h2 : (show ↥(spanL i w hw Y) from (evT LY g y).1) = toY i w hw Y ⟨_, hE (gl i w hw g)⟩ := by
      change (y : Br.G D.nbr i w hw → (XG i w hw r Xs hr x Y hst).V) g = _
      rw [hy]
      rfl
    exact phiL_eq i w hw Y M LY.T hT φ (evT LY g y) _ h2

end GlobalTheory.Pass.LocDual.OneX.PushEq

end
end

section
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition GlobalTheory.Pass.LocDual GlobalTheory.Pass.LocDual.OneX
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.Pass.LocDual.OneX

theorem span_stable (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (Xs : Set (D.nd.X i)) {a : ℕ} (x : Fin a → ↥Xs) (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i))
    (hst : ∀ γ : GE D.nd, ∀ y ∈ Y, actK i r Xs x γ y ∈ Y) (γ : GE D.nd) :
    ∀ v ∈ Submodule.span (KK D.nd i) (Y : Set (Fin a → Fin D.R.nV → KK D.nd i)),
      actK i r Xs x γ v ∈ Submodule.span (KK D.nd i) (Y : Set (Fin a → Fin D.R.nV → KK D.nd i)) := by
  let f : (Fin a → Fin D.R.nV → KK D.nd i) →ₗ[KK D.nd i] (Fin a → Fin D.R.nV → KK D.nd i) :=
    LinearMap.pi fun b => Matrix.toLin' (mapM (toK D.nd i) (rTwO D.nd i r (x b)) γ) ∘ₗ LinearMap.proj b
  have hf : ∀ v, f v = actK i r Xs x γ v := fun v => rfl
  intro v hv
  rw [← hf]
  have h : Submodule.span (KK D.nd i) (Y : Set (Fin a → Fin D.R.nV → KK D.nd i)) ≤
      (Submodule.span (KK D.nd i) (Y : Set (Fin a → Fin D.R.nV → KK D.nd i))).comap f := by
    refine Submodule.span_le.2 fun y hy => ?_
    rw [SetLike.mem_coe, Submodule.mem_comap, hf]
    exact Submodule.subset_span (hst γ y hy)
  exact h hv

end GlobalTheory.Pass.LocDual.OneX

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem GlobalTheory.Pass.LocDual.OneX.main : ∀ (D : D7), FontaineAtPlacesOverL (D := D) → ∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))),
    GoodR D.nd i r → ∀ (Xs : Set (D.nd.X i)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (n : ℕ), PotFam i w hw (fun x : ↥Xs => rTwO D.nd i r x) n →
    ∀ (k : ℕ) (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (hSub : SubTw i r Xs M)
      (F : Finset (Br.G D.nbr i w hw → (Fin k → Br.LL D.nbr i w hw) ⧸ (Br.locLat D.nbr i w hw M).T)),
      (F : Set (Br.G D.nbr i w hw → (Fin k → Br.LL D.nbr i w hw) ⧸ (Br.locLat D.nbr i w hw M).T)) ⊆ cutCoc i w hw r Xs M →
      ∃ X : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw),
        IsSummandTw i w hw r Xs X ∧
        Submodule.span (Br.OLL D.nbr i w hw) (F : Set (Br.G D.nbr i w hw → (Fin k → Br.LL D.nbr i w hw) ⧸ (Br.locLat D.nbr i w hw M).T)) ≤
          BlochKatoDuality.spanPush (Br.PD D.loc D.nbr i w hw) X (locU i w hw M hSub.1) (Br.locLat D.nbr i w hw M) := by
  intro D hF i r hr Xs w hw n hP k M hSub F hFs
  obtain ⟨a, x, E, Y, hYfg, hst, hE, hc⟩ := GlobalTheory.Pass.LocDual.OneX.cutCoc_finset_common D i w hw r Xs M F hFs
  have hC := GlobalTheory.BlockSum.exists_stable_compl_actK D i r Xs hr x (Submodule.span (KK D.nd i) (Y : Set _))
    (fun γ => GlobalTheory.Pass.LocDual.OneX.span_stable D i r Xs x Y hst γ)
  refine ⟨GlobalTheory.Pass.LocDual.OneX.XG i w hw r Xs hr x Y hst,
    GlobalTheory.Pass.LocDual.OneX.isSummandTw_XG D i w hw r Xs hr x Y hst hC, ?_⟩
  obtain ⟨LY, hLY⟩ := GlobalTheory.T.localIntegerSpanOfImage_is_stable_lattice D i w hw r Xs hr x Y hst hYfg
  have hy := GlobalTheory.Pass.LocDual.OneX.yfun_Z1fT D hF i r hr Xs w hw n hP x Y hst E hE LY hLY
  apply Submodule.span_le.2
  intro c hcF
  obtain ⟨φ, hφ, rfl⟩ := hc c hcF
  obtain ⟨φ', hG, hpush⟩ := GlobalTheory.Pass.LocDual.OneX.PushEq.main D i w hw r Xs hr x Y hst E hE M LY hLY φ hφ
  unfold BlochKatoDuality.spanPush
  exact Submodule.subset_span (R := Br.OLL D.nbr i w hw) (M := Br.G D.nbr i w hw → (Fin k → Br.LL D.nbr i w hw) ⧸ (Br.locLat D.nbr i w hw M).T) ⟨LY, φ', hG, ⟨_, hy.1⟩, hy, (hpush ⟨_, hy.1⟩ rfl).symm⟩
end

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition GlobalTheory.Pass.LocDual
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localCocycles_mem_span_pushout_summandLattice : ∀ (D : D7), FontaineAtPlacesOverL (D := D) → ∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))),
    GoodR D.nd i r → ∀ (Xs : Set (D.nd.X i)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (n : ℕ), PotFam i w hw (fun x : ↥Xs => rTwO D.nd i r x) n →
    ∀ (k : ℕ) (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (hSub : SubTw i r Xs M)
      (F : Finset (Br.G D.nbr i w hw → (Fin k → Br.LL D.nbr i w hw) ⧸ (Br.locLat D.nbr i w hw M).T)),
      (F : Set (Br.G D.nbr i w hw → (Fin k → Br.LL D.nbr i w hw) ⧸ (Br.locLat D.nbr i w hw M).T)) ⊆ cutCoc i w hw r Xs M →
      ∃ X : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw),
        IsSummandTw i w hw r Xs X ∧
        Submodule.span (Br.OLL D.nbr i w hw) (F : Set (Br.G D.nbr i w hw → (Fin k → Br.LL D.nbr i w hw) ⧸ (Br.locLat D.nbr i w hw M).T)) ≤
          BlochKatoDuality.spanPush (Br.PD D.loc D.nbr i w hw) X (locU i w hw M hSub.1) (Br.locLat D.nbr i w hw M) := by
  atlas_forward_decl GlobalTheory.Pass.LocDual.OneX.main
end
