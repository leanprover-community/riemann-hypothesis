import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Formalism.SharpRestriction.LevelLetterCocycles.IntegralHeckeForms
import Formalism.LocalToGlobal.IndefiniteReal.Bridge
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteGroupLevelActionEqInvSmulTranslate
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHyperspecialIffGIntOfSuppAtSplit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChangeOfSplittingPair
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualTypePlacesIsSplitNonconjugateOfAdmissible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasInfExpMulOfIsOpenKer
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistingCharacterAdmissibleGaloisTwistGood
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNsmulMemOfSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemLatAtIffHat
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsElemStdLatticeSandwichSplitSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteAdelicPointLatticeIsLattice
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualWeylLatticeExistsNatPowSmulMem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvPlaceNormProductMemCoefficientRing

section
noncomputable section

open Formalism.IndefR.Bridge

namespace GlobalTheory.ClassTrace

variable {O Γ Hf P : Type} [CommRing O] [Group Γ] [Group Hf] [AddCommGroup P] [Module O P]
  (ι : Γ →* Hf) (J : Subgroup Hf) (lam : J →* Oˣ) (ρ : Representation O Γ P)

def intForms (LL : Hf → Submodule O P) : Submodule O (Hf → P) where
  carrier := {f | (∀ (γ : Γ) (h : Hf) (k : J), f (ι γ * h * k) = (lam k : O) • ρ γ (f h)) ∧ ∀ h, f h ∈ LL h}
  add_mem' := fun {f g} hf hg =>
    ⟨fun γ h k => by simp only [Pi.add_apply, hf.1 γ h k, hg.1 γ h k, map_add, smul_add],
      fun h => Submodule.add_mem _ (hf.2 h) (hg.2 h)⟩
  zero_mem' := ⟨fun γ h k => by simp, fun h => Submodule.zero_mem _⟩
  smul_mem' := fun a f hf =>
    ⟨fun γ h k => by simp only [Pi.smul_apply, hf.1 γ h k, map_smul]; rw [smul_comm],
      fun h => Submodule.smul_mem _ _ (hf.2 h)⟩

def LatticeLaw (LL : Hf → Submodule O P) : Prop :=
  (∀ γ h, (LL h).map (ρ γ) = LL (ι γ * h)) ∧ ∀ h (k : J), LL (h * k) = LL h

def tr (h : Hf) (p : P) : P := ∑ᶠ γ : stab ι J h, (lam (stabK ι γ) : O) • ρ (γ : Γ) p

open Classical in

def lamExt (x : Hf) : O := if hx : x ∈ J then (lam ⟨x, hx⟩ : O) else 0

theorem lamExt_coe (k : J) : lamExt J lam (k : Hf) = (lam k : O) := by
  simp [lamExt]

theorem lamExt_of_not_mem {x : Hf} (hx : x ∉ J) : lamExt J lam x = 0 := by
  simp [lamExt, hx]

theorem lamExt_mul (x : Hf) (k : J) : lamExt J lam (x * k) = lamExt J lam x * (lam k : O) := by
  by_cases hx : x ∈ J
  · have hxk : x * (k : Hf) ∈ J := J.mul_mem hx k.2
    unfold lamExt
    rw [dif_pos hxk, dif_pos hx, ← Units.val_mul, ← map_mul]
    rfl
  · have hxk : x * (k : Hf) ∉ J := fun hm => hx (by simpa using J.mul_mem hm (J.inv_mem k.2))
    rw [lamExt_of_not_mem J lam hx, lamExt_of_not_mem J lam hxk, zero_mul]

def traceForm (h : Hf) (p : P) (x : Hf) : P := ∑ᶠ γ : Γ, lamExt J lam (h⁻¹ * (ι γ)⁻¹ * x) • ρ γ p

def link (h x : Hf) : Set Γ := {γ | h⁻¹ * (ι γ)⁻¹ * x ∈ J}

theorem mem_link_iff {h x : Hf} {γ : Γ} : γ ∈ link ι J h x ↔ ∃ k : J, x = ι γ * h * k := by
  constructor
  · intro hγ
    refine ⟨⟨h⁻¹ * (ι γ)⁻¹ * x, hγ⟩, ?_⟩
    show x = ι γ * h * (h⁻¹ * (ι γ)⁻¹ * x)
    group
  · rintro ⟨k, rfl⟩
    show h⁻¹ * (ι γ)⁻¹ * (ι γ * h * k) ∈ J
    rw [show h⁻¹ * (ι γ)⁻¹ * (ι γ * h * k) = (k : Hf) by group]
    exact k.2

def linkEquiv {h x : Hf} {γ₀ : Γ} (h0 : γ₀ ∈ link ι J h x) : stab ι J x ≃ link ι J h x where
  toFun δ := ⟨δ * γ₀, by
    have h1 := J.mul_mem h0 (J.inv_mem ((mem_stab ι).1 δ.2))
    simpa [link, mul_assoc] using h1⟩
  invFun γ := ⟨γ * γ₀⁻¹, by
    have h1 := J.mul_mem (J.inv_mem γ.2) h0
    rw [mem_stab]
    simpa [link, mul_assoc] using h1⟩
  left_inv δ := by simp
  right_inv γ := by simp

theorem link_finite (hfin : ∀ x, Finite (stab ι J x)) (h x : Hf) : (link ι J h x).Finite := by
  rcases (link ι J h x).eq_empty_or_nonempty with he | ⟨γ₀, h0⟩
  · rw [he]
    exact Set.finite_empty
  · have := hfin x
    exact Set.finite_coe_iff.mp (Finite.of_equiv _ (linkEquiv ι J h0))

theorem support_subset (h : Hf) (p : P) (x : Hf) :
    (Function.support fun γ : Γ => lamExt J lam (h⁻¹ * (ι γ)⁻¹ * x) • ρ γ p) ⊆ link ι J h x := by
  intro γ hγ
  rw [Function.mem_support] at hγ
  by_contra hn
  have hn' : h⁻¹ * (ι γ)⁻¹ * x ∉ J := hn
  exact hγ (by rw [lamExt_of_not_mem J lam hn', zero_smul])

theorem traceForm_eq_zero (h : Hf) (p : P) {x : Hf} (hx : ¬ ∃ (γ : Γ) (k : J), x = ι γ * h * k) :
    traceForm ι J lam ρ h p x = 0 := by
  unfold traceForm
  have hz : ∀ γ : Γ, lamExt J lam (h⁻¹ * (ι γ)⁻¹ * x) • ρ γ p = 0 := by
    intro γ
    have hn : h⁻¹ * (ι γ)⁻¹ * x ∉ J := fun hm =>
      hx ⟨γ, (mem_link_iff ι J (h := h) (x := x) (γ := γ)).1 hm⟩
    rw [lamExt_of_not_mem J lam hn, zero_smul]
  simp only [hz, finsum_zero]

theorem traceForm_law (hfin : ∀ x, Finite (stab ι J x)) (h : Hf) (p : P) (γ₀ : Γ) (x : Hf) (k : J) :
    traceForm ι J lam ρ h p (ι γ₀ * x * k) = (lam k : O) • ρ γ₀ (traceForm ι J lam ρ h p x) := by
  have hf : (Function.support fun γ : Γ => lamExt J lam (h⁻¹ * (ι γ)⁻¹ * x) • ρ γ p).Finite :=
    (link_finite ι J hfin h x).subset (support_subset ι J lam ρ h p x)
  unfold traceForm
  conv_rhs => rw [← LinearMap.smul_apply]
  rw [map_finsum _ hf, ← finsum_comp_equiv (Equiv.mulLeft γ₀)]
  refine finsum_congr fun γ => ?_
  simp only [Equiv.coe_mulLeft]
  have e : h⁻¹ * (ι (γ₀ * γ))⁻¹ * (ι γ₀ * x * k) = h⁻¹ * (ι γ)⁻¹ * x * k := by
    rw [map_mul]
    group
  rw [e, lamExt_mul, map_mul, Module.End.mul_apply, LinearMap.smul_apply, map_smul, mul_smul]
  exact smul_comm _ _ _

variable {C W : Type} [Field C] [AddCommGroup W] [Module C W] {e : O →+* C}

def classSum (θ : Hf → P →ₛₗ[e] W) {I : Type} [Fintype I] (y : I → Hf) (f : Hf → P) : W :=
  ∑ i, (Nat.card (stab ι J (y i)) : C)⁻¹ • θ (y i) (f (y i))

def DualLaw (θ : Hf → P →ₛₗ[e] W) : Prop :=
  ∀ (γ : Γ) (h : Hf) (k : J) (p : P), e (lam k) • θ (ι γ * h * k) (ρ γ p) = θ h p

theorem kernel_traceForm (hfin : ∀ x, Finite (stab ι J x)) {θ : Hf → P →ₛₗ[e] W} (hθ : DualLaw ι J lam ρ θ)
    (h : Hf) (p : P) {x : Hf} {γ₀ : Γ} (h0 : γ₀ ∈ link ι J h x) :
    θ x (traceForm ι J lam ρ h p x) = (Nat.card (stab ι J x) : C) • θ h p := by
  classical
  have hL := link_finite ι J hfin h x
  have hf : (Function.support fun γ : Γ => lamExt J lam (h⁻¹ * (ι γ)⁻¹ * x) • ρ γ p).Finite :=
    hL.subset (support_subset ι J lam ρ h p x)
  have hterm : ∀ γ : Γ, θ x (lamExt J lam (h⁻¹ * (ι γ)⁻¹ * x) • ρ γ p) =
      if γ ∈ link ι J h x then θ h p else 0 := by
    intro γ
    split_ifs with hγ
    · obtain ⟨k, hk⟩ := (mem_link_iff ι J).1 hγ
      have hk' : h⁻¹ * (ι γ)⁻¹ * x = (k : Hf) := by
        rw [hk]
        group
      rw [hk', lamExt_coe, map_smulₛₗ, ← hθ γ h k p, ← hk]
    · have hn : h⁻¹ * (ι γ)⁻¹ * x ∉ J := hγ
      rw [lamExt_of_not_mem J lam hn, zero_smul, map_zero]
  have hsub : Function.support (fun γ : Γ => if γ ∈ link ι J h x then θ h p else 0) ⊆
      (hL.toFinset : Set Γ) := by
    intro γ hγ
    rw [Set.Finite.coe_toFinset]
    by_contra hn
    exact hγ (if_neg hn)
  have hc : hL.toFinset.card = Nat.card (stab ι J x) := by
    rw [Nat.card_congr (linkEquiv ι J h0), Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card _ hL]
  unfold traceForm
  rw [map_finsum (θ x) hf]
  simp only [hterm]
  rw [finsum_eq_sum_of_support_subset _ hsub,
    Finset.sum_congr rfl (fun γ hγ => if_pos ((Set.Finite.mem_toFinset hL).1 hγ)),
    Finset.sum_const, hc, Nat.cast_smul_eq_nsmul]

theorem classSum_traceForm [CharZero C] (hfin : ∀ x, Finite (stab ι J x)) {θ : Hf → P →ₛₗ[e] W}
    (hθ : DualLaw ι J lam ρ θ) {I : Type} [Fintype I] {y : I → Hf} (hy : IsReps ι J y) (h : Hf) (p : P) :
    classSum ι J θ y (traceForm ι J lam ρ h p) = θ h p := by
  obtain ⟨i₀, ⟨γ, k, hh⟩, huniq⟩ := hy h
  unfold classSum
  rw [Finset.sum_eq_single i₀]
  · have h0 : γ⁻¹ ∈ link ι J h (y i₀) := by
      rw [mem_link_iff]
      refine ⟨k⁻¹, ?_⟩
      rw [hh]
      simp only [map_inv, Subgroup.coe_inv]
      group
    rw [kernel_traceForm ι J lam ρ hfin hθ h p h0]
    have := hfin (y i₀)
    have hne : (Nat.card (stab ι J (y i₀)) : C) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
    exact inv_smul_smul₀ hne _
  · intro i _ hi
    have hx : ¬ ∃ (γ' : Γ) (k' : J), y i = ι γ' * h * k' := by
      rintro ⟨γ', k', hy'⟩
      apply hi
      apply huniq
      refine ⟨γ'⁻¹, k'⁻¹, ?_⟩
      rw [hy']
      simp only [map_inv, Subgroup.coe_inv]
      group
    rw [traceForm_eq_zero ι J lam ρ h p hx, map_zero, smul_zero]
  · intro hi
    exact absurd (Finset.mem_univ i₀) hi

theorem finite_stab_of_reps {I : Type} {y : I → Hf} (hy : IsReps ι J y) (hfin : ∀ i, Finite (stab ι J (y i)))
    (x : Hf) : Finite (stab ι J x) := by
  obtain ⟨i, ⟨γ, k, hx⟩, -⟩ := hy x
  subst hx
  have := hfin i
  refine Finite.of_injective (β := stab ι J (y i)) (fun δ => ⟨γ⁻¹ * δ * γ, ?_⟩) ?_
  · rw [mem_stab]
    have hδ := (mem_stab ι).1 δ.2
    have e : (y i)⁻¹ * ι (γ⁻¹ * δ * γ) * y i =
        (k : Hf) * ((ι γ * y i * k)⁻¹ * ι δ * (ι γ * y i * k)) * (k : Hf)⁻¹ := by
      simp only [map_mul, map_inv]
      group
    rw [e]
    exact J.mul_mem (J.mul_mem k.2 hδ) (J.inv_mem k.2)
  · intro a b hab
    apply Subtype.ext
    have := congrArg Subtype.val hab
    simpa using this

end GlobalTheory.ClassTrace

end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.HatIntSmul

theorem mem_stdLat_coord {E : Type} [Field E] [NumberField E] {n : ℕ} {s : Fin n → E}
    (hs : s ∈ Formalism.L2.Pj.stdLat E n) (j : Fin n) : ∃ o : 𝓞 E, s j = (o : E) := by
  have := (Submodule.mem_pi.mp hs) j (Set.mem_univ _)
  obtain ⟨o, ho⟩ := Submodule.mem_one.mp this
  exact ⟨o, ho.symm⟩

theorem single_mem_stdLat {E : Type} [Field E] [NumberField E] {n : ℕ} (i : Fin n) (o : 𝓞 E) :
    Pi.single i (o : E) ∈ Formalism.L2.Pj.stdLat E n := by
  refine Submodule.mem_pi.mpr fun j _ => ?_
  rw [Submodule.mem_one]
  by_cases h : j = i
  · subst h; exact ⟨o, by simp⟩
  · exact ⟨0, by simp [Pi.single_apply, h]⟩

theorem nsmul_tmul {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]
    (a : ℕ) (β : Af F) (x : E) : a • (β ⊗ₜ[F] x) = β ⊗ₜ[F] (((a : 𝓞 E) : E) * x) := by
  have h := map_nsmul (TensorProduct.mk F (Af F) E β) a x
  simp only [TensorProduct.mk_apply] at h
  rw [← h, nsmul_eq_mul]
  simp

set_option maxHeartbeats 2000000 in

theorem sq_smul_mulVec_mem_hat : ∀ (D : D7) (n : ℕ) (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (a : ℕ), (∀ x ∈ Formalism.L2.Pj.stdLat D.host.E n, (a : 𝓞 D.host.E) • x ∈ Λ) → (∀ x ∈ Λ, (a : 𝓞 D.host.E) • x ∈ Formalism.L2.Pj.stdLat D.host.E n) → ∀ (M : Matrix (Fin n) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E)), (∀ i j, M i j ∈ intAE D) → ∀ y ∈ GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin n → D.host.E)), (a ^ 2) • (M *ᵥ y) ∈ GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin n → D.host.E)) := by
  intro D n Λ a h1 h2 M hM y hy
  have mulMem : ∀ {x y : Af D.host.F ⊗[D.host.F] D.host.E}, x ∈ intAE D → y ∈ intAE D → x * y ∈ intAE D := by
    intro x y hx hy
    refine AddSubgroup.closure_induction₂ (p := fun x y _ _ => x * y ∈ intAE D) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
    · rintro _ _ ⟨a, ha, u, rfl⟩ ⟨b, hb, v, rfl⟩
      refine AddSubgroup.subset_closure ⟨a * b, fun w => ?_, u * v, ?_⟩
      · rw [map_mul]; exact mul_mem (ha w) (hb w)
      · rw [Algebra.TensorProduct.tmul_mul_tmul]; rfl
    · intro x _; rw [zero_mul]; exact zero_mem _
    · intro x _; rw [mul_zero]; exact zero_mem _
    · intro x y z _ _ _ h1 h2; rw [add_mul]; exact add_mem h1 h2
    · intro x y z _ _ _ h1 h2; rw [mul_add]; exact add_mem h1 h2
    · intro x y _ _ h; rw [neg_mul]; exact neg_mem h
    · intro x y _ _ h; rw [mul_neg]; exact neg_mem h

  have stepA : ∀ w : Fin n → Af D.host.F ⊗[D.host.F] D.host.E, (∀ i, w i ∈ intAE D) →
      a • w ∈ GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin n → D.host.E)) := by
    intro w hw
    have hw' : a • w = ∑ i, a • Pi.single i (w i) := by
      rw [← Finset.smul_sum, Finset.univ_sum_single]
    rw [hw']
    refine sum_mem fun i _ => ?_
    have key : ∀ z ∈ intAE D, a • Pi.single i z ∈ GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin n → D.host.E)) := by
      intro z hz
      induction hz using AddSubgroup.closure_induction with
      | mem z hz =>
        obtain ⟨β, hβ, o, rfl⟩ := hz
        apply AddSubgroup.subset_closure
        refine ⟨β, fun v => hβ v, (a : 𝓞 D.host.E) • Pi.single i (o : D.host.E), h1 _ (single_mem_stdLat i o), ?_⟩
        funext k
        by_cases hk : k = i
        · subst hk
          rw [Pi.smul_apply, Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_same, nsmul_tmul, Algebra.smul_def]
        · simp [Pi.single_apply, hk]
      | zero => simp
      | add x y _ _ hx hy => rw [Pi.single_add, smul_add]; exact add_mem hx hy
      | neg x _ hx => rw [Pi.single_neg, smul_neg]; exact neg_mem hx
    exact key _ (hw i)
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨α, hα, x, hx, rfl⟩ := hz
    obtain ⟨o, ho⟩ := Classical.axiomOfChoice (mem_stdLat_coord (h2 x hx))
    have e : (a ^ 2) • (M *ᵥ fun i => α ⊗ₜ[D.host.F] x i) =
        a • (M *ᵥ fun j => α ⊗ₜ[D.host.F] ((o j : 𝓞 D.host.E) : D.host.E)) := by
      rw [pow_two, mul_smul, ← Matrix.mulVec_smul]
      congr 2
      funext j
      rw [Pi.smul_apply, nsmul_tmul, ← ho j]
      simp [Algebra.smul_def]
    rw [e]
    refine stepA _ fun i => ?_
    simp only [Matrix.mulVec, dotProduct]
    refine sum_mem fun j _ => mulMem (hM i j) (AddSubgroup.subset_closure ⟨α, fun v => hα v, o j, rfl⟩)
  | zero => simp
  | add y z _ _ hy hz => rw [Matrix.mulVec_add, smul_add]; exact add_mem hy hz
  | neg y _ hy => rw [Matrix.mulVec_neg, smul_neg]; exact neg_mem hy

end GlobalTheory.HatIntSmul
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.SuppIntCong

set_option maxHeartbeats 2000000 in

theorem cong_one_of_suppAt : ∀ (D : D7) (V : HSp D) (Q : Finset (Pl D.host.E)) (hQ : GA D V) (a : ℕ), 0 < a → SplitSet Q → SuppAt (idem Q) V hQ → ∃ c : ℕ, ∀ i j, (∃ w ∈ intAE D, ((normProd Q ^ c : ℕ) : Af D.host.F ⊗[D.host.F] D.host.E) * ((finHom V hQ).val i j - (1 : Matrix (Fin V.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) i j) = ((a ^ 2 : ℕ) : Af D.host.F ⊗[D.host.F] D.host.E) * w) ∧ (∃ w ∈ intAE D, ((normProd Q ^ c : ℕ) : Af D.host.F ⊗[D.host.F] D.host.E) * ((finHom V hQ)⁻¹.val i j - (1 : Matrix (Fin V.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) i j) = ((a ^ 2 : ℕ) : Af D.host.F ⊗[D.host.F] D.host.E) * w) := by
  intro D V Q hQ a ha hQs hs
  classical
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  have h4 := GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3
  obtain ⟨hid, hcj⟩ := GlobalTheory.ConjVal.components_and_conj_valuation D ι h1 h2 h4
  obtain ⟨ev, hev⟩ : ∃ ev : ∀ P : HeightOneSpectrum (𝓞 D.host.E), AE D →+* P.adicCompletion D.host.E,
      ∀ P z, ev P z = ι (finPart D z) P :=
    ⟨fun P => ((GlobalTheory.CharLocProd.evalAt P).comp ι.toRingHom).comp (finPart D), fun _ _ => rfl⟩
  obtain ⟨evf, hevf⟩ : ∃ evf : ∀ P : HeightOneSpectrum (𝓞 D.host.E),
      (Af D.host.F ⊗[D.host.F] D.host.E) →+* P.adicCompletion D.host.E, ∀ P y, evf P y = ι y P :=
    ⟨fun P => (GlobalTheory.CharLocProd.evalAt P).comp ι.toRingHom, fun _ _ => rfl⟩
  simp only [← hev] at hid hcj
  obtain ⟨⟨es, hes, hsum⟩, -⟩ := hQs.isIdemSum
  have e2 : ∀ P, P ∉ Q → ev P (idem Q) = 0 := fun P hP => by
    rw [hsum, map_sum]
    exact Finset.sum_eq_zero fun Q' h' => (hid _ _ (hes Q' h')).2.2 P fun hh => hP (hh ▸ h')
  have hA1 : ∀ P, P ∉ Q → GlobalTheory.IdemSupport.cP P ∉ Q → (ev P).mapMatrix (mt V hQ) = 1 := fun P hP hP' => by
    have hc := hcj (idem Q) (GlobalTheory.IdemSupport.cP P)
    rw [e2 _ hP', map_zero, GlobalTheory.ClassScalarValue.cP_cP, map_eq_zero] at hc
    have hu : ev P (idem Q + cA D (idem Q)) = 0 := by rw [map_add, e2 P hP, hc, add_zero]
    have : (ev P).mapMatrix (mt V hQ - 1) = 0 := by
      refine Matrix.ext fun i j => ?_
      change ev P ((mt V hQ - 1) i j) = 0
      rw [← hs i j, map_mul, hu, zero_mul]
    rw [map_sub, map_one, sub_eq_zero] at this
    exact this
  have hinv : ∀ P, (ev P).mapMatrix (mt V hQ) * (ev P).mapMatrix (mt V hQ⁻¹) = 1 := fun P => by
    rw [← map_mul, show mt V hQ * mt V hQ⁻¹ = 1 by unfold Formalism.L2.Theta.mt; rw [map_inv]; exact Units.mul_inv _, map_one]
  have hB1 : ∀ P, P ∉ Q → GlobalTheory.IdemSupport.cP P ∉ Q → (ev P).mapMatrix (mt V hQ⁻¹) = 1 := fun P hP hP' => by
    have := hinv P
    rwa [hA1 P hP hP', one_mul] at this
  set S := Q ∪ Q.image GlobalTheory.IdemSupport.cP with hS
  have hout : ∀ P, P ∉ S → P ∉ Q ∧ GlobalTheory.IdemSupport.cP P ∉ Q := fun P hP =>
    ⟨fun h' => hP (Finset.mem_union_left _ h'), fun h' => hP (Finset.mem_union_right _
      (Finset.mem_image.2 ⟨_, h', GlobalTheory.ClassScalarValue.cP_cP P⟩))⟩

  have hN : ∀ P ∈ S, ((normProd Q : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := by
    have key : ∀ P' ∈ Q, ((normProd Q : ℕ) : 𝓞 D.host.E) ∈ P'.asIdeal := fun P' hP' => by
      show ((∏ v ∈ Q, Ideal.absNorm v.asIdeal : ℕ) : 𝓞 D.host.E) ∈ P'.asIdeal
      obtain ⟨r, hr⟩ := Finset.dvd_prod_of_mem (fun v : HeightOneSpectrum (𝓞 D.host.E) => Ideal.absNorm v.asIdeal) hP'
      rw [hr, Nat.cast_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)
    intro P hP
    rcases Finset.mem_union.1 hP with h | h
    · exact key P h
    · obtain ⟨P', hP', rfl⟩ := Finset.mem_image.1 h
      rw [GlobalTheory.IdemSupport.mem_cP, map_natCast]
      exact key P' hP'
  have hvN : ∀ P ∈ S, ∀ c : ℕ, Valued.v (evf P ((normProd Q ^ c : ℕ) : Af D.host.F ⊗[D.host.F] D.host.E)) ≤
      WithZero.exp (-(c : ℤ)) := by
    intro P hP c
    have he : evf P ((normProd Q ^ c : ℕ) : Af D.host.F ⊗[D.host.F] D.host.E) = algebraMap D.host.E (P.adicCompletion D.host.E)
        (algebraMap (𝓞 D.host.E) D.host.E (((normProd Q : ℕ) : 𝓞 D.host.E) ^ c)) := by
      simp only [map_natCast, map_pow, Nat.cast_pow]
    rw [he, GlobalTheory.CharLocProd.val_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]
    exact (HeightOneSpectrum.intValuation_le_pow_iff_mem _ _ _).2 (Ideal.pow_mem_pow (hN P hP) c)
  have hlog : ∀ x : WithZero (Multiplicative ℤ), ∃ n : ℕ, x ≤ WithZero.exp (n : ℤ) := fun x => by
    by_cases hx : x = 0
    · exact ⟨0, hx ▸ zero_le'⟩
    · exact ⟨(WithZero.log x).toNat, by
        rw [← WithZero.exp_log hx]; exact WithZero.exp_le_exp.2 (by rw [WithZero.log_exp]; exact Int.self_le_toNat _)⟩
  choose fn hfn using hlog
  have ha0 : (a : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 ha.ne'

  have hgen : ∀ y : Af D.host.F ⊗[D.host.F] D.host.E, (∀ P, P ∉ S → evf P y = 0) → ∃ c0 : ℕ, ∀ c, c0 ≤ c →
      ∃ w ∈ intAE D, ((normProd Q ^ c : ℕ) : Af D.host.F ⊗[D.host.F] D.host.E) * y =
        ((a ^ 2 : ℕ) : Af D.host.F ⊗[D.host.F] D.host.E) * w := by
    intro y hy
    set u : Af D.host.F ⊗[D.host.F] D.host.E :=
      Algebra.TensorProduct.includeRight (R := D.host.F) (A := Af D.host.F) (B := D.host.E) ((a : D.host.E)⁻¹ ^ 2) with hu
    have hau : ((a ^ 2 : ℕ) : Af D.host.F ⊗[D.host.F] D.host.E) * u = 1 := by
      rw [hu, ← map_natCast (Algebra.TensorProduct.includeRight (R := D.host.F) (A := Af D.host.F) (B := D.host.E)),
        ← map_mul, Nat.cast_pow, ← mul_pow, mul_inv_cancel₀ ha0, one_pow, map_one]
    let f : HeightOneSpectrum (𝓞 D.host.E) → ℕ := fun P => fn (Valued.v (evf P u)) + fn (Valued.v (evf P y))
    refine ⟨S.sup f, fun c hc => ⟨u * ((normProd Q ^ c : ℕ) : Af D.host.F ⊗[D.host.F] D.host.E) * y, ?_, ?_⟩⟩
    · refine (h2 _).2 fun P => ?_
      rw [← hevf, map_mul, map_mul, map_mul, map_mul]
      by_cases hP : P ∈ S
      · have hle : f P ≤ c := (Finset.le_sup hP).trans hc
        calc _ ≤ WithZero.exp (fn (Valued.v (evf P u)) : ℤ) * WithZero.exp (-(c : ℤ)) *
              WithZero.exp (fn (Valued.v (evf P y)) : ℤ) :=
              mul_le_mul' (mul_le_mul' (hfn _) (hvN P hP c)) (hfn _)
          _ = WithZero.exp ((fn (Valued.v (evf P u)) : ℤ) + -(c : ℤ) + fn (Valued.v (evf P y))) := by
              rw [← WithZero.exp_add, ← WithZero.exp_add]
          _ ≤ 1 := by
              rw [← WithZero.exp_zero]
              exact WithZero.exp_le_exp.2 (by simp only [f] at hle; omega)
      · rw [hy P hP, map_zero, mul_zero]; exact zero_le'
    · rw [← mul_assoc, ← mul_assoc, hau, one_mul]
  have hone : ∀ P i j, evf P ((1 : Matrix (Fin V.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) i j) =
      (1 : Matrix (Fin V.rank) (Fin V.rank) (P.adicCompletion D.host.E)) i j := fun P i j => by
    rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp
  have hy1 : ∀ i j P, P ∉ S → evf P ((finHom V hQ).val i j -
      (1 : Matrix (Fin V.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) i j) = 0 := by
    intro i j P hP
    obtain ⟨o1, o2⟩ := hout P hP
    have h' := congrFun (congrFun (hA1 P o1 o2) i) j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply] at h'
    have hk : (finHom V hQ).val i j = finPart D (mt V hQ i j) := rfl
    rw [map_sub, hone, hk, hevf, ← hev, h', sub_self]
  have hy2 : ∀ i j P, P ∉ S → evf P ((finHom V hQ)⁻¹.val i j -
      (1 : Matrix (Fin V.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) i j) = 0 := by
    intro i j P hP
    obtain ⟨o1, o2⟩ := hout P hP
    have h' := congrFun (congrFun (hB1 P o1 o2) i) j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply] at h'
    have hk : (finHom V hQ)⁻¹.val i j = finPart D (mt V hQ⁻¹ i j) := by rw [← map_inv]; rfl
    rw [map_sub, hone, hk, hevf, ← hev, h', sub_self]
  choose c1 hc1 using fun i j => hgen _ (hy1 i j)
  choose c2 hc2 using fun i j => hgen _ (hy2 i j)
  let g : Fin V.rank × Fin V.rank → ℕ := fun p => c1 p.1 p.2 + c2 p.1 p.2
  refine ⟨Finset.univ.sup g, fun i j => ⟨hc1 i j _ ?_, hc2 i j _ ?_⟩⟩
  · exact le_trans (Nat.le_add_right _ _) (Finset.le_sup (f := g) (Finset.mem_univ (i, j)))
  · exact le_trans (Nat.le_add_left _ _) (Finset.le_sup (f := g) (Finset.mem_univ (i, j)))

end GlobalTheory.SuppIntCong
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.LatCmpQ

theorem nsmul_mulVec_eq {R : Type*} [CommRing R] {n : ℕ} (N m : ℕ) (g w : Matrix (Fin n) (Fin n) R)
    (hwe : ∀ i j, (N : R) * (g i j - (1 : Matrix (Fin n) (Fin n) R) i j) = (m : R) * w i j) (y : Fin n → R) :
    N • (g *ᵥ y) = N • y + m • (w *ᵥ y) := by
  have e1 : (N : R) • (g - 1) = (m : R) • w := by
    ext i j
    simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
    exact hwe i j
  have e2 : ((N : R) • (g - 1)) *ᵥ y = N • (g *ᵥ y) - N • y := by
    rw [Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Nat.cast_smul_eq_nsmul, smul_sub]
  have e3 : ((m : R) • w) *ᵥ y = m • (w *ᵥ y) := by
    rw [Matrix.smul_mulVec, Nat.cast_smul_eq_nsmul]
  rw [← e3, ← e1, e2]
  abel

set_option maxHeartbeats 1000000 in

theorem step {D : D7} {n : ℕ} (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (a N : ℕ)
    (h1 : ∀ x ∈ Formalism.L2.Pj.stdLat D.host.E n, (a : 𝓞 D.host.E) • x ∈ Λ) (h2 : ∀ x ∈ Λ, (a : 𝓞 D.host.E) • x ∈ Formalism.L2.Pj.stdLat D.host.E n)
    (g : Matrix (Fin n) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))
    (hg : ∀ i j, ∃ w ∈ intAE D, ((N : ℕ) : Af D.host.F ⊗[D.host.F] D.host.E) * (g i j - (1 : Matrix (Fin n) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E)) i j) =
        ((a ^ 2 : ℕ) : Af D.host.F ⊗[D.host.F] D.host.E) * w)
    {y : Fin n → Af D.host.F ⊗[D.host.F] D.host.E} (hy : y ∈ GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin n → D.host.E))) :
    N • (g *ᵥ y) ∈ GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin n → D.host.E)) := by
  choose w hw hwe using hg
  have key := nsmul_mulVec_eq N (a ^ 2) g (Matrix.of w) hwe y
  rw [key]
  exact add_mem (AddSubgroup.nsmul_mem _ hy N) (GlobalTheory.HatIntSmul.sq_smul_mulVec_mem_hat D n Λ a h1 h2 _ hw y hy)

set_option maxHeartbeats 1000000 in

theorem latAt_translate_bounded : ∀ (D : D7) (ρ : Setup D.ntw), ρ.Good → ∀ (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (Q : Finset (Pl D.host.E)) (h hQ : GA D (Vc D j)), SplitSet Q → SuppAt (idem Q) (Vc D j) hQ → ∃ c : ℕ, (∀ x ∈ (ρ.B i j b).latAt (finPt (Vc D j) h), ((normProd Q ^ c : ℕ) : 𝓞 D.host.E) • x ∈ (ρ.B i j b).latAt (finPt (Vc D j) (h * hQ))) ∧ ∀ x ∈ (ρ.B i j b).latAt (finPt (Vc D j) (h * hQ)), ((normProd Q ^ c : ℕ) : 𝓞 D.host.E) • x ∈ (ρ.B i j b).latAt (finPt (Vc D j) h) := by
  intro D ρ hρ i j b Q h hQ hS hsupp
  have hΛ : ∀ x, x ∈ (ρ.B i j b).F.ΛS ↔ x ∈ L0c D (Vc D j) := by
    obtain ⟨_, _, _, h1, h2⟩ := hρ.latS i j b
    intro x
    constructor
    · intro hx; simpa using h2 x hx
    · intro hx; simpa using h1 x hx
  obtain ⟨a, ha, hs1, hs2⟩ := GlobalTheory.LatSandwich.sandwich D (Vc D j) (ρ.B i j b).F.ΛS hΛ
  obtain ⟨c, hc⟩ := GlobalTheory.SuppIntCong.cong_one_of_suppAt D (Vc D j) Q hQ a ha hS hsupp
  have ev : ∀ x : Fin (Vc D j).rank → D.host.E, (fun k => (1 : Af D.host.F) ⊗ₜ[D.host.F] ((((normProd Q ^ c : ℕ) : 𝓞 D.host.E) • x) k)) =
      (normProd Q ^ c) • (fun k => (1 : Af D.host.F) ⊗ₜ[D.host.F] x k) := by
    intro x
    funext k
    rw [Pi.smul_apply, Pi.smul_apply, Nat.cast_smul_eq_nsmul]
    exact map_nsmul ((TensorProduct.mk D.host.F (Af D.host.F) D.host.E) 1) _ _
  have hmul : ((finPt (Vc D j) (h * hQ)).1⁻¹).val = (finHom (Vc D j) hQ)⁻¹.val * ((finPt (Vc D j) h).1⁻¹).val := by
    have e : (finPt (Vc D j) (h * hQ)).1 = finHom (Vc D j) h * finHom (Vc D j) hQ := map_mul (finHom (Vc D j)) h hQ
    rw [e, _root_.mul_inv_rev, Units.val_mul]
    rfl
  have hmul' : ((finPt (Vc D j) h).1⁻¹).val = (finHom (Vc D j) hQ).val * ((finPt (Vc D j) (h * hQ)).1⁻¹).val := by
    rw [hmul, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
  refine ⟨c, fun x hx => ?_, fun x hx => ?_⟩
  · rw [GlobalTheory.LatAtHLat.mem_latAt_iff_hat] at hx ⊢
    rw [ev x, Matrix.mulVec_smul, hmul, ← Matrix.mulVec_mulVec]
    exact step _ a _ hs1 hs2 _ (fun i j => (hc i j).2) hx
  · rw [GlobalTheory.LatAtHLat.mem_latAt_iff_hat] at hx ⊢
    have hst := step _ a _ hs1 hs2 _ (fun i j => (hc i j).1) hx
    rw [Matrix.mulVec_mulVec, ← hmul'] at hst
    rw [ev x, Matrix.mulVec_smul]
    exact hst

end GlobalTheory.LatCmpQ
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlaces_translation_lattice_bounded_norm : ∀ (D : D7) (ρ : Setup D.ntw), ρ.Good → ∀ (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (Q : Finset (Pl D.host.E)) (h hQ : GA D (Vc D j)), SplitSet Q → SuppAt (idem Q) (Vc D j) hQ → ∃ c : ℕ, (∀ x ∈ (ρ.B i j b).latAt (finPt (Vc D j) h), ((normProd Q ^ c : ℕ) : 𝓞 D.host.E) • x ∈ (ρ.B i j b).latAt (finPt (Vc D j) (h * hQ))) ∧ ∀ x ∈ (ρ.B i j b).latAt (finPt (Vc D j) (h * hQ)), ((normProd Q ^ c : ℕ) : 𝓞 D.host.E) • x ∈ (ρ.B i j b).latAt (finPt (Vc D j) h) := by
  first | exact @GlobalTheory.LatCmpQ.latAt_translate_bounded | exact GlobalTheory.LatCmpQ.latAt_translate_bounded | (intros; apply GlobalTheory.LatCmpQ.latAt_translate_bounded <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_adelic_point_lattice_isLattice : ∀ (D : D7) (ρ : Setup D.ntw), ρ.Good → ∀ (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (h : GA D (Vc D j)), Submodule.IsLattice D.host.E ((ρ.B i j b).latAt (finPt (Vc D j) h)) := by
  first | exact @GlobalTheory.LatFull.latAt_isLattice | exact GlobalTheory.LatFull.latAt_isLattice | (intros; apply GlobalTheory.LatFull.latAt_isLattice <;> assumption)
end

section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualWeylLattice_exists_natPow_smul_mem : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] (ι : Type) [Fintype ι] (n : ℕ) (emb : ι → E →+* K) (lam : ι → Formalism.BasicNotions.DomWeight n) (M M' : Submodule (𝓞 E) (Fin n → E)) (N : ℕ), N ≠ 0 → Submodule.IsLattice E M → Submodule.IsLattice E M' → (∀ x ∈ M, (N : 𝓞 E) • x ∈ M') → (∀ x ∈ M', (N : 𝓞 E) • x ∈ M) → ∃ a : ℕ, ∀ F ∈ Formalism.L2.DIV.nabAtr emb lam M, ((N : K) ^ a) • F ∈ Formalism.L2.DIV.nabAtr emb lam M' := by
  first | exact @GlobalTheory.NabScale.nabAtr_smul_pow_mem | exact GlobalTheory.NabScale.nabAtr_smul_pow_mem | (intros; apply GlobalTheory.NabScale.nabAtr_smul_pow_mem <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inv_place_norm_product_mem_coefficient_ring : ∀ (D : D7) (ρ : Setup D.ntw) (i : D.ntw.Tw) (b : Bool) (Q : Finset (Pl D.host.E)), Disjoint Q (D.ntw.S0 i) → ((normProd Q : ℕ) : ℂ)⁻¹ ∈ (ρ.eO i b).range := by
  first | exact @GlobalTheory.NormUnit.normProd_inv_mem | exact GlobalTheory.NormUnit.normProd_inv_mem | (intros; apply GlobalTheory.NormUnit.normProd_inv_mem <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LatTranslate

theorem coefFn_natCast_smul {D : D7} {n : ℕ} {K : Type} [Field K] (σ : K →+* ℂ) (lam : D.what₂.Tau → Formalism.BasicNotions.DomWeight n)
    (N : ℕ) (F : Formalism.L2.DIV.Pol K D.what₂.Tau n) (x : GLR D n) :
    coefFn σ lam ((N : K) • F) x = (N : ℂ) * coefFn σ lam F x := by
  simp only [coefFn, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval₂Hom_C, map_natCast]
  ring

theorem coefLatFn_transfer {D : D7} {n : ℕ} {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ)
    (emb : D.what₂.Tau → D.host.E →+* K) (lam : D.what₂.Tau → Formalism.BasicNotions.DomWeight n) {O O' : Subring ℂ} (hOO : O ≤ O')
    {M M' : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (N : ℕ) (hN : N ≠ 0) (hinv : ((N : ℂ))⁻¹ ∈ O')
    (hF : ∀ F ∈ Formalism.L2.DIV.nabAtr emb lam M, (N : K) • F ∈ Formalism.L2.DIV.nabAtr emb lam M')
    {φ : GLR D n → ℂ} (hφ : φ ∈ coefLatFn σ emb O lam M) : φ ∈ coefLatFn σ emb O' lam M' := by
  induction hφ using Submodule.span_induction with
  | mem _ h =>
    obtain ⟨F, hFm, rfl⟩ := h
    have h1 : coefFn σ lam (((N : K) • F : Formalism.L2.DIV.VV K lam) : Formalism.L2.DIV.Pol K D.what₂.Tau n) ∈ coefLatFn σ emb O' lam M' :=
      Submodule.subset_span ⟨_, hF F hFm, rfl⟩
    have h2 := Submodule.smul_mem _ (⟨_, hinv⟩ : O') h1
    convert h2 using 1
    funext x
    have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN
    change _ = (N : ℂ)⁻¹ * _
    rw [Submodule.coe_smul, coefFn_natCast_smul, inv_mul_cancel_left₀ hN']
  | zero => exact zero_mem _
  | add _ _ _ _ h1 h2 => exact add_mem h1 h2
  | smul c _ _ h1 => exact Submodule.smul_mem _ (⟨c, hOO c.2⟩ : O') h1

theorem normProd_ne_zero {D : D7} (Q : Finset (Pl D.host.E)) : normProd Q ≠ 0 := by
  unfold normProd
  refine Finset.prod_ne_zero_iff.2 fun v _ => ?_
  rw [Ne, Ideal.absNorm_eq_zero_iff]
  exact v.ne_bot

set_option maxHeartbeats 800000 in

theorem lat_translate : ∀ (D : D7) (ρ : Setup D.ntw), ρ.Good → ∀ (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool), ∀ k (Q : Finset (Pl D.host.E)) (h hQ : GA D (Vc D j)) P, SplitSet Q → Disjoint Q (D.ntw.S0 i) → h ∈ GfC (Vc D j) → SuppAt (idem Q) (Vc D j) hQ → P ∈ ρ.lat i j b (ρ.eO i b).range h → P ∈ ρ.lat i j b (ρ.eOk i b k).range (h * hQ) := by
  intro D ρ hρ i j b k Q h hQ P hS hD hh hsupp hP
  unfold GlobalTheory.SeriesTie.Setup.lat GlobalTheory.ExportSeries.Base.coefLat at *
  rw [GlobalTheory.ExportSeries.mem_harmLat] at *
  refine ⟨hP.1, ?_⟩
  obtain ⟨c, h1, h2⟩ := GlobalTheory.T.splitPlaces_translation_lattice_bounded_norm D ρ hρ i j b Q h hQ hS hsupp
  have hN0 : normProd Q ^ c ≠ 0 := pow_ne_zero _ (normProd_ne_zero Q)
  obtain ⟨a, ha⟩ := GlobalTheory.T.dualWeylLattice_exists_natPow_smul_mem _ _ _ _ (labLL0 D) (ρ.B i j b).w.lam _ _ (normProd Q ^ c) hN0 (GlobalTheory.T.finite_adelic_point_lattice_isLattice D ρ hρ i j b h)
    (GlobalTheory.T.finite_adelic_point_lattice_isLattice D ρ hρ i j b (h * hQ)) h1 h2
  have hu : ((normProd Q : ℕ) : ℂ)⁻¹ ∈ (ρ.eOk i b k).range := hρ.range_le i b k (GlobalTheory.T.inv_place_norm_product_mem_coefficient_ring D ρ i b Q hD)
  have hinv : (((normProd Q ^ c) ^ a : ℕ) : ℂ)⁻¹ ∈ (ρ.eOk i b k).range := by
    rw [Nat.cast_pow, Nat.cast_pow, ← inv_pow, ← inv_pow]
    exact Subring.pow_mem _ (Subring.pow_mem _ hu _) _
  have hF : ∀ F ∈ Formalism.L2.DIV.nabAtr (labLL0 D) (ρ.B i j b).w.lam ((ρ.B i j b).latAt (finPt (Vc D j) h)),
      (((normProd Q ^ c) ^ a : ℕ) : ↥D.LL0) • F ∈
        Formalism.L2.DIV.nabAtr (labLL0 D) (ρ.B i j b).w.lam ((ρ.B i j b).latAt (finPt (Vc D j) (h * hQ))) := by
    intro F hF
    have := ha F hF
    rwa [Nat.cast_pow (α := ↥D.LL0) (normProd Q ^ c) a]
  exact coefLatFn_transfer (Formalism.L2.Host.embLL0 D) (labLL0 D) (ρ.B i j b).w.lam (hρ.range_le i b k)
    ((normProd Q ^ c) ^ a) (pow_ne_zero _ hN0) hinv hF hP.2

end GlobalTheory.LatTranslate

end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coefLat_le_translate_splitPlaces_prime_to_l : ∀ (D : D7) (ρ : Setup D.ntw), ρ.Good → ∀ (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool), ∀ k (Q : Finset (Pl D.host.E)) (h hQ : GA D (Vc D j)) P, SplitSet Q → Disjoint Q (D.ntw.S0 i) → h ∈ GfC (Vc D j) → SuppAt (idem Q) (Vc D j) hQ → P ∈ ρ.lat i j b (ρ.eO i b).range h → P ∈ ρ.lat i j b (ρ.eOk i b k).range (h * hQ) := by
  first | exact @GlobalTheory.LatTranslate.lat_translate | exact GlobalTheory.LatTranslate.lat_translate | (intros; apply GlobalTheory.LatTranslate.lat_translate <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.TwTraceCx

open GlobalTheory.ClassTrace

variable {D : D7}

noncomputable def lift (V : HSp D) (x : Bridge.Gf V) : GA D V := Classical.choose (GlobalTheory.ThetaCommutation.exists_fin_part V x)

theorem lift_mem (V : HSp D) (x : Bridge.Gf V) : lift V x ∈ GfC V :=
  (Classical.choose_spec (GlobalTheory.ThetaCommutation.exists_fin_part V x)).1

theorem finPt_lift (V : HSp D) (x : Bridge.Gf V) : finPt V (lift V x) = x :=
  (Classical.choose_spec (GlobalTheory.ThetaCommutation.exists_fin_part V x)).2

theorem eq_of_finPt (V : HSp D) {a b : GA D V} (ha : a ∈ GfC V) (hb : b ∈ GfC V) (h : finPt V a = finPt V b) :
    a = b := by
  have h1 : finHom V a = finHom V b := congrArg Subtype.val h
  have h2 : a⁻¹ * b ∈ GinfC V := by
    show finHom V (a⁻¹ * b) = 1
    rw [map_mul, map_inv, h1, inv_mul_cancel]
  have h3 := (GlobalTheory.UnitarySplit.real_finite_split D V).2.2.1 _ h2 ((GfC V).mul_mem ((GfC V).inv_mem ha) hb)
  rw [inv_mul_eq_one] at h3
  exact h3

theorem lift_finPt (V : HSp D) {a : GA D V} (ha : a ∈ GfC V) : lift V (finPt V a) = a :=
  eq_of_finPt V (lift_mem V _) ha (finPt_lift V _)

theorem mem_GfC_of_suppAt {Q : Finset (Pl D.host.E)} (hQ : SplitSet Q) {V : HSp D} {g : GA D V}
    (hg : SuppAt (idem Q) V g) : g ∈ GfC V := by
  refine GlobalTheory.WeilProduct.mem_GfC_of_supp (a := idem Q + cA D (idem Q)) ?_ hg
  rw [RingHom.map_add, idem, map_sum (cA D), map_sum (infPart D), map_sum (infPart D), ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun PP hPP => ?_
  have h1 := (hQ.isIdemAt hPP).1
  rw [GlobalTheory.SplitScalar.infPart_splitIdem h1, GlobalTheory.SplitScalar.infPart_splitIdem (GlobalTheory.SplitScalar.isSplitIdem_conj h1), add_zero]

theorem act_of_mem_GfC {S T : HSp D} (B : Base S T) {g : GA D S} (hg : g ∈ GfC S) : B.act g = 1 := by
  have h1 : infHom S g = 1 := hg
  have h2 : realGL B.F.θ S g = 1 := by
    funext τ
    show Formalism.UG.bc (B.F.θ τ) (infHom S g) = 1
    rw [h1, map_one]
  rw [Base.act, MonoidHom.comp_apply, h2, map_one]

noncomputable def kern {S T : HSp D} (B : Base S T) (ω : PairRep S T) (t : Twist D Circle) (x : Bridge.Gf S) :
    PolF D T.rank S.rank →ₗ[ℂ] (GA D T → ℂ) :=
  series B.F ω (B.vecFlat t) (lift S x)

noncomputable abbrev ratAct {S T : HSp D} (B : Base S T) : Representation ℂ (GQ S) (PolF D T.rank S.rank) :=
  B.act.comp (GQ S).subtype

end GlobalTheory.TwTraceCx

namespace GlobalTheory.TwTraceCx

variable {D : D7}

theorem gen_eq_smul {S T : HSp D} {B : Base S T} (hB : B.Good) {t : Twist D Circle} (ht : t.Good) (hQ : B.admitted t.Q)
    {ω₁ ωt : PairRep S T} (h1 : B.IsWeil 1 ω₁) (h2 : B.IsWeil t.chi ωt) (h : GA D S) (P : PolF D T.rank S.rank) :
    B.gen ω₁ t h P = ((detChar S t.chi h : Circle) : ℂ) • series B.F ωt (B.vecFlat t) h P := by
  have hν := ht.isHeckeChar
  have hF := ht.real
  have hω1 : IsWeilDatumO B.F.ψ S T B.mu (B.mu * B.eta⁻¹) ω₁ := by
    have := h1
    unfold Base.IsWeil at this
    simpa only [mul_one] using this
  have hωt : IsWeilDatumO B.F.ψ S T (B.mu * t.chi) (B.mu * B.eta⁻¹ * t.chi) ωt := by
    have := h2
    unfold Base.IsWeil at this
    rwa [mul_right_comm B.mu t.chi] at this
  have key := ((GlobalTheory.SplitChange.change_of_splitting_pair D B.F.ψ S T B.mu (B.mu * B.eta⁻¹) t.chi ω₁ hω1 hν hF).2.1
    _ _ (muVal_detChar S hF) (muVal_detChar T hF)).2 ωt hωt
  have hth := Base.isThetaFunO_fock_vecAt hB hQ (fun PP => flat (t.resC PP.1)) P
  funext g
  have e := key h g _ hth
  have hc : ((detChar S t.chi h : Circle) : ℂ) ≠ 0 := Circle.coe_ne_zero _
  change ((detChar T t.chi g : Circle) : ℂ) * (ω₁ (h, g) (B.F.fock (B.vecFlat t) P) 0) =
    ((detChar S t.chi h : Circle) : ℂ) * (ωt (h, g) (B.F.fock (B.vecFlat t) P) 0)
  have e' : ωt (h, g) (B.F.fock (B.vecFlat t) P) 0 = (((detChar T t.chi g : Circle) : ℂ) *
      (((detChar S t.chi h : Circle) : ℂ))⁻¹) * ω₁ (h, g) (B.F.fock (B.vecFlat t) P) 0 := by
    have := congrFun e 0
    simp only [Pi.smul_apply, smul_eq_mul] at this
    exact this
  rw [e']
  field_simp

end GlobalTheory.TwTraceCx

namespace GlobalTheory.TwTraceCx

open GlobalTheory.ClassTrace

variable {D : D7}

theorem traceForm_mem_mtLat {S T : HSp D} {B : Base S T} (hB : B.Good) {K : Type} [Field K] [NumberField K]
    {σ : K →+* ℂ} {emb : D.what₂.Tau → D.host.E →+* K} {O : Subring ℂ} (hc : IsCoefRing σ emb O) {t : Twist D Circle}
    (hfin : ∀ x, Finite (Bridge.stab (Bridge.ratF S) (B.levJ t) x))
    (hlam : ∀ x : B.levJ t, ((B.levLam t x : ℂˣ) : ℂ) ∈ O) (h : Bridge.Gf S) {P : PolF D T.rank S.rank}
    (hP : P ∈ B.coefLat σ emb O h) :
    traceForm (Bridge.ratF S) (B.levJ t) (B.levLam t) (ratAct B) h P ∈ B.mtLat σ emb O t := by
  have hV : P ∈ B.valSpace := (Submodule.mem_inf.1 hP).1
  rw [Base.mem_mtLat, Base.mem_formsC]
  refine ⟨⟨fun x => ?_, fun γ x k => ?_⟩, fun x => ?_⟩
  · refine finsum_induction (· ∈ B.valSpace) (zero_mem _) (fun _ _ => add_mem) fun γ => ?_
    exact Submodule.smul_mem _ _ (Base.act_mem_valSpace _ hV)
  · exact traceForm_law _ _ _ _ hfin h P γ x k
  · refine finsum_induction (· ∈ B.coefLat σ emb O x) (zero_mem _) (fun _ _ => add_mem) fun γ => ?_
    by_cases hγ : γ ∈ link (Bridge.ratF S) (B.levJ t) h x
    · obtain ⟨k, rfl⟩ := (mem_link_iff _ _).1 hγ
      have e : h⁻¹ * (Bridge.ratF S γ)⁻¹ * (Bridge.ratF S γ * h * k) = k := by group
      rw [e, lamExt_coe]
      exact (B.coefLat σ emb O _).smul_mem (⟨_, hlam k⟩ : O)
        (Base.act_mem_coefLat hB.frame hc γ h k (Base.mem_St_of_mem_levJ k.2) hP)
    · rw [lamExt_of_not_mem _ _ hγ, zero_smul]
      exact zero_mem _

end GlobalTheory.TwTraceCx

namespace GlobalTheory.TwTraceCx

open GlobalTheory.ClassTrace

variable {D : D7}

set_option maxHeartbeats 3000000 in

theorem dualLaw_kern {S T : HSp D} {B : Base S T} (hB : B.Good) (hS : HSpace.SigOK S) {t : Twist D Circle} (ht : t.Good)
    (hQ : B.admitted t.Q) {ωt : PairRep S T} (h2 : B.IsWeil t.chi ωt) :
    DualLaw (e := RingHom.id ℂ) (Bridge.ratF S) (B.levJ t) (B.levLam t) (ratAct B) (kern B ωt t) := by
  intro γ x k p
  have hW : IsWeilDatumO B.F.ψ S T (B.mu * t.chi) (B.mu * t.chi * B.eta⁻¹) ωt := h2
  obtain ⟨a, ha, γf, hγf, hγ⟩ := (GlobalTheory.UnitarySplit.real_finite_split D S).1 (γ : GA D S)
  have hxl := lift_mem S x
  have hkl := lift_mem S (k : Bridge.Gf S)
  have hfa : finHom S a = 1 := ha
  have e1 : lift S (Bridge.ratF S γ * x * k) = γf * lift S x * lift S (k : Bridge.Gf S) := by
    refine eq_of_finPt S (lift_mem S _) ((GfC S).mul_mem ((GfC S).mul_mem hγf hxl) hkl) ?_
    rw [finPt_lift]
    apply Subtype.ext
    have hx1 : finHom S (lift S x) = x.1 := congrArg Subtype.val (finPt_lift S x)
    have hk1 : finHom S (lift S (k : Bridge.Gf S)) = (k : Bridge.Gf S).1 := congrArg Subtype.val (finPt_lift S _)
    show finHom S (γ : GA D S) * x.1 * (k : Bridge.Gf S).1 = finHom S (γf * lift S x * lift S (k : Bridge.Gf S))
    rw [map_mul, map_mul, hx1, hk1, hγ, map_mul, hfa, one_mul]
  have e2 : ratAct B γ p = B.act a p := by
    show B.act (γ : GA D S) p = _
    rw [hγ, map_mul, act_of_mem_GfC B hγf, mul_one]
  have hcomm : γf * lift S x * lift S (k : Bridge.Gf S) * a = (γ : GA D S) * (lift S x * lift S (k : Bridge.Gf S)) := by
    rw [← (GlobalTheory.UnitarySplit.real_finite_split D S).2.1 a ha _ ((GfC S).mul_mem ((GfC S).mul_mem hγf hxl) hkl), hγ]
    group
  have hJ : finPt S (lift S (k : Bridge.Gf S)) ∈ B.levJ t := by rw [finPt_lift]; exact k.2
  have hT0 : ωt (lift S (k : Bridge.Gf S), 1) (B.F.fock (B.vecFlat t) p) =
      ((B.levLam t k : ℂˣ) : ℂ)⁻¹ • B.F.fock (B.vecFlat t) p := by
    have := ((GlobalTheory.ExportSeries.DualType.thetaSeriesData_have_dualType hB hS ht hQ).1 ωt h2 _ hkl hJ).2 p
    rwa [show (⟨finPt S (lift S (k : Bridge.Gf S)), hJ⟩ : B.levJ t) = k from Subtype.ext (finPt_lift S _)] at this
  have hK2 : ωt (a, 1) (B.F.fock (B.vecFlat t) p) = B.F.fock (B.vecFlat t) (B.act a p) :=
    GlobalTheory.RealFockAction.om_fock_vecAt D S T B t ωt t.Q (fun PP => flat (t.resC PP.1)) hB ht hQ h2 a ha p
  have hth : IsThetaFunO B.F.ψ S T (B.F.fock (B.vecFlat t) p) :=
    Base.isThetaFunO_fock_vecAt hB hQ (fun PP => flat (t.resC PP.1)) p
  funext g
  rw [Pi.smul_apply, RingHom.id_apply, kern, kern, series_apply, series_apply, smul_eq_mul]
  rw [e1, e2, ← hK2]
  have q1 : ((γf * lift S x * lift S (k : Bridge.Gf S), g) : GA D S × GA D T) * (a, 1) =
      (((γ : GA D S), 1) * (lift S x, g)) * (lift S (k : Bridge.Gf S), 1) := by
    simp only [Prod.mk_mul_mk, mul_one, one_mul]
    rw [hcomm, mul_assoc]
  have e5 : ωt (γf * lift S x * lift S (k : Bridge.Gf S), g) (ωt (a, 1) (B.F.fock (B.vecFlat t) p)) =
      ωt ((γ : GA D S), 1) (ωt (lift S x, g) (ωt (lift S (k : Bridge.Gf S), 1) (B.F.fock (B.vecFlat t) p))) := by
    calc ωt (γf * lift S x * lift S (k : Bridge.Gf S), g) (ωt (a, 1) (B.F.fock (B.vecFlat t) p))
        = ωt (((γf * lift S x * lift S (k : Bridge.Gf S), g) : GA D S × GA D T) * (a, 1)) (B.F.fock (B.vecFlat t) p) := by
          rw [map_mul ωt, Module.End.mul_apply]
      _ = ωt ((((γ : GA D S), 1) * (lift S x, g)) * (lift S (k : Bridge.Gf S), 1)) (B.F.fock (B.vecFlat t) p) := by rw [q1]
      _ = _ := by rw [map_mul ωt, map_mul ωt, Module.End.mul_apply, Module.End.mul_apply]
  have hA := hW.om_aut (γ : GA D S) γ.2 1 (one_mem _)
    (ωt (lift S x, g) (ωt (lift S (k : Bridge.Gf S), 1) (B.F.fock (B.vecFlat t) p))) (hW.om_pres _ _ (hW.om_pres _ _ hth))
  simp only [e5, hA]
  simp only [hT0, map_smul, Pi.smul_apply, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (Units.ne_zero ((B.levLam t) k)), one_mul]

theorem classSum_traceForm_eq {S T : HSp D} {B : Base S T} (hB : B.Good) (hS : HSpace.SigOK S) {t : Twist D Circle}
    (ht : t.Good) (hQ : B.admitted t.Q) {ωt : PairRep S T} (h2 : B.IsWeil t.chi ωt) {I : Type} [Fintype I] {rep : I → GA D S}
    (hcl : IsClassSystem S (B.levJ t) rep) {h : GA D S} (hh : h ∈ GfC S) (P : PolF D T.rank S.rank) :
    B.classSum ωt t rep (traceForm (Bridge.ratF S) (B.levJ t) (B.levLam t) (ratAct B) (finPt S h) P) =
      series B.F ωt (B.vecFlat t) h P := by
  have hfin := finite_stab_of_reps _ _ hcl.reps hcl.stab
  have key := classSum_traceForm (e := RingHom.id ℂ) (Bridge.ratF S) (B.levJ t) (B.levLam t) (ratAct B) hfin
    (dualLaw_kern hB hS ht hQ h2) hcl.reps (finPt S h) P
  have e : kern B ωt t (finPt S h) P = series B.F ωt (B.vecFlat t) h P := by rw [kern, lift_finPt S hh]
  rw [← e, ← key, Base.classSum_apply, GlobalTheory.ClassTrace.classSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [kern, lift_finPt S (hcl.fin i)]

end GlobalTheory.TwTraceCx

namespace GlobalTheory.TwTraceCx

open GlobalTheory.ClassTrace

theorem trace_cx : ∀ (D : D7) (ρ : Setup D.ntw), ρ.Good → ∀ (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool), ∀ k Q ψ,
    TwOK i k Q ψ →
    (∀ x : (ρ.B i j b).levJ (ρ.tw i b k Q ψ), (((ρ.B i j b).levLam (ρ.tw i b k Q ψ) x : ℂˣ) : ℂ) ∈ (ρ.eOk i b k).range) →
    ∀ s h P, ρ.IsDatum i j b s h P → ∀ f ∈ ρ.gens i j b k Q ψ h P, ∃ F ∈ ρ.mt i j b k Q ψ, f = ρ.sum i j b k Q ψ F := by
  intro D ρ hρ i j b k Q ψ hok hlam s h P hd f hf
  obtain ⟨ht, hadm, hval⟩ := GlobalTheory.TwistGood.tw_good D _ D.ntw ρ hρ i j b k Q ψ hok
  obtain ⟨hQ, hsupp, rfl⟩ := hf
  have hB := hρ.base i j b
  have hS : (Vc D j).SigOK := D.sp.V_sig _
  have hcl := hρ.classes i j b _ ht hadm
  have hfin := finite_stab_of_reps _ _ hcl.reps hcl.stab
  have hh : h * hQ ∈ GfC (Vc D j) := (GfC _).mul_mem hd.fin (mem_GfC_of_suppAt ht.split hsupp)
  have hdisj : Disjoint (ρ.tw i b k Q ψ).Q (D.ntw.S0 i) := hok.2.1.mono_left fun x hx =>
    (mem_half.1 (show x ∈ half (ρ.ch i) Q from hx)).1
  have hP : P ∈ ρ.lat i j b (ρ.eOk i b k).range (h * hQ) :=
    GlobalTheory.T.coefLat_le_translate_splitPlaces_prime_to_l D ρ hρ i j b k _ h hQ P ht.split hdisj hd.fin hsupp hd.mem
  obtain ⟨u, hu⟩ := hval (detRoot (Vc D j) (h * hQ))
  have hc : ((detChar (Vc D j) (ρ.tw i b k Q ψ).chi (h * hQ) : Circle) : ℂ) ∈ (ρ.eOk i b k).range := ⟨u, hu.symm⟩
  refine ⟨(⟨_, hc⟩ : (ρ.eOk i b k).range) • traceForm (Bridge.ratF _) _ _ (ratAct (ρ.B i j b)) (finPt _ (h * hQ)) P,
    Submodule.smul_mem _ _ (traceForm_mem_mtLat hB (hρ.isCoefRing_k i b k) hfin hlam _ hP), ?_⟩
  rw [gen_eq_smul hB ht hadm (hρ.weil_base i j b) (hρ.weil i j b _ ht)]
  change _ = (ρ.B i j b).classSum _ _ _
    (((detChar (Vc D j) (ρ.tw i b k Q ψ).chi (h * hQ) : Circle) : ℂ) •
      traceForm (Bridge.ratF _) _ _ (ratAct (ρ.B i j b)) (finPt _ (h * hQ)) P)
  rw [map_smul, classSum_traceForm_eq hB hS ht hadm (hρ.weil i j b _ ht) hcl hh]

end GlobalTheory.TwTraceCx

end
end
