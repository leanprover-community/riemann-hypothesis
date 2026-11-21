import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.DzMatchCut
import Development.DiscreteGroups.GlobalIrreducibility.DzGenDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLanglandsClassificationDetCharacter
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIrreducibleSubquotient
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
import Development.DiscreteGroups.GlobalIrreducibility.DzGenMat
import Development.DiscreteGroups.GlobalIrreducibility.DzGenCpt
import Development.DiscreteGroups.GlobalIrreducibility.DzIsoKO

section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL Matrix

namespace DiscreteGroups.sglob.DzType

theorem genA : GenA := by
  intro H k _ _ _ _ m

  obtain ⟨E⟩ := GlobalTheory.LocGL.DetQuot.nonempty_equiv_multiProd (k := k) (eOne m)
    (θ := fun _ : Fin m => (1 : kˣ →* ℂˣ)) (Θ := (1 : Levi k (fun _ : Fin m => Fin 1) →* ℂˣ)) (fun g => by simp)
  have hs1 : IsSmoothChar (detChar (Fin 1) (1 : kˣ →* ℂˣ)) := by
    show IsOpen ((detChar (Fin 1) (1 : kˣ →* ℂˣ)).ker : Set (GL (Fin 1) k))
    convert isOpen_univ
    ext g
    simp
  have hs : ∀ _ : Fin m, IsSmooth (detRep (Fin 1) (1 : kˣ →* ℂˣ)) := fun _ => (isSmooth_ofChar_iff _).2 hs1
  have hi : ∀ _ : Fin m, (detRep (Fin 1) (1 : kˣ →* ℂˣ)).IsIrreducible := fun _ => isIrreducible_ofChar _
  have hu : ∀ _ : Fin m, IsUnitarisable (detRep (Fin 1) (1 : kˣ →* ℂˣ)) := fun _ =>
    (isUnitarisable_ofChar_iff _).2 fun g => by simp
  have hirr := GlobalTheory.SmGL.MultiIrr.isIrreducible_multiProd H (eOne m)
    (σ := fun _ : Fin m => detRep (Fin 1) (1 : kˣ →* ℂˣ)) hs hi hu
  refine ⟨(GlobalTheory.SmGL.MultiIrr.isIrreducible_iff_of_equiv E).2 hirr, ?_, ?_⟩
  ·
    obtain ⟨f, hf, hf1⟩ := GlobalTheory.SatInd.exists_fixed_apply_one (eOne m)
      (ρ := ofChar (1 : Levi k (fun _ : Fin m => Fin 1) →* ℂˣ)) (x := (1 : ℂ)) fun g _ => by simp
    show fixed (parInd (eOne m) (ofChar (1 : Levi k (fun _ : Fin m => Fin 1) →* ℂˣ))) (GlobalTheory.SplitWeil.KO k (Fin m)) ≠ ⊥
    intro hbot
    have h0 : f ∈ (⊥ : Submodule ℂ _) := hbot ▸ hf
    rw [Submodule.mem_bot] at h0
    rw [h0] at hf1
    exact absurd hf1 (by simp)
  ·
    have hc : HasCentralChar (multiProd (eOne m) fun _ : Fin m => detRep (Fin 1) (1 : kˣ →* ℂˣ)) 1 := by
      intro z f
      rw [GlobalTheory.BoundaryMaps.multiProd_scalar (eOne m) _ (fun _ => (1 : kˣ →* ℂˣ))
        (fun _ => by simpa using GlobalTheory.BoundaryMaps.hasCentralChar_detRep (k := k) 1 (1 : kˣ →* ℂˣ)) z f]
      simp
    exact GlobalTheory.LocGL.hasCentralChar_of_equiv E.symm hc

end DiscreteGroups.sglob.DzType
end
end

section
namespace DiscreteGroups.sglob.DzType

open Matrix

theorem valuation_unitri_lt {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) {m : ℕ}
    (L U : Matrix (Fin m) (Fin m) K) (hL : ∀ i j, i < j → L i j = 0) (hU1 : ∀ i, U i i = 1)
    (hU0 : ∀ i j, j < i → U i j = 0) (hX : ∀ i j, v ((L * U) i j) ≤ 1) (hXd : ∀ i, v ((L * U) i i) = 1)
    (hXu : ∀ i j, i < j → v ((L * U) i j) < 1) : ∀ i j, i < j → v (U i j) < 1 := by
  classical
  have mlt : ∀ a b : Γ, a ≤ 1 → b < 1 → a * b < 1 := fun a b ha hb =>
    lt_of_le_of_lt (show a * b ≤ b from (by gcongr : a * b ≤ 1 * b).trans_eq (one_mul b)) hb
  have split : ∀ (i c a : Fin m), (L * U) i c = L i a * U a c + ∑ l ∈ Finset.univ.erase a, L i l * U l c := by
    intro i c a
    rw [Matrix.mul_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ a)]
  have key : ∀ n : ℕ, ∀ i : Fin m, i.val = n → ∀ j, i < j → v (U i j) < 1 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro i hin
      have up : ∀ l : Fin m, l < i → ∀ j, l < j → v (U l j) < 1 := fun l hl j hlj =>
        ih l.val (by rw [← hin]; exact hl) l rfl j hlj
      have hLi : ∀ p : ℕ, ∀ l : Fin m, l.val = p → l < i → v (L i l) ≤ 1 := by
        intro p
        induction p using Nat.strong_induction_on with
        | _ p ihp =>
          intro l hlp hli
          have hR : v (∑ l' ∈ Finset.univ.erase l, L i l' * U l' l) < 1 := by
            refine Valuation.map_sum_lt v one_ne_zero fun l' hl' => ?_
            have hne : l' ≠ l := Finset.ne_of_mem_erase hl'
            rcases lt_or_gt_of_ne hne with h | h
            · rw [map_mul]
              exact mlt _ _ (ihp l'.val (by rw [← hlp]; exact h) l' rfl (h.trans hli))
                (up l' (h.trans hli) l h)
            · rw [hU0 l' l h, mul_zero, map_zero]; exact zero_lt_one
          have hs := split i l l
          rw [hU1, mul_one] at hs
          have e : L i l = (L * U) i l - ∑ l' ∈ Finset.univ.erase l, L i l' * U l' l := by rw [hs]; ring
          rw [e]
          exact (Valuation.map_sub v _ _).trans (max_le (hX i l) hR.le)
      have hR : ∀ c, (∀ l', l' < i → v (U l' c) < 1) →
          v (∑ l' ∈ Finset.univ.erase i, L i l' * U l' c) < 1 := by
        intro c hc
        refine Valuation.map_sum_lt v one_ne_zero fun l' hl' => ?_
        have hne : l' ≠ i := Finset.ne_of_mem_erase hl'
        rcases lt_or_gt_of_ne hne with h | h
        · rw [map_mul]
          exact mlt _ _ (hLi l'.val l' rfl h) (hc l' h)
        · rw [hL i l' h, zero_mul, map_zero]; exact zero_lt_one
      have hLii : v (L i i) = 1 := by
        have hs := split i i i
        rw [hU1, mul_one] at hs
        have hr := hR i (fun l' h => up l' h i h)
        have e : L i i = (L * U) i i - ∑ l' ∈ Finset.univ.erase i, L i l' * U l' i := by rw [hs]; ring
        refine le_antisymm ?_ ?_
        · rw [e]; exact (Valuation.map_sub v _ _).trans (max_le (hX i i) hr.le)
        · by_contra hlt
          push Not at hlt
          have h2 := Valuation.map_add v (L i i) (∑ l' ∈ Finset.univ.erase i, L i l' * U l' i)
          rw [← hs, hXd i] at h2
          exact absurd (h2.trans_lt (max_lt hlt hr)) (lt_irrefl 1)
      intro j hij
      have hs := split i j i
      have hr := hR j (fun l' h => up l' h j (h.trans hij))
      have h1 : v (L i i * U i j) < 1 := by
        have e : L i i * U i j = (L * U) i j - ∑ l' ∈ Finset.univ.erase i, L i l' * U l' j := by rw [hs]; ring
        rw [e]
        exact (Valuation.map_sub v _ _).trans_lt (max_lt (hXu i j hij) hr)
      rwa [map_mul, hLii, one_mul] at h1
  intro i j hij
  exact key i.val i rfl j hij

end DiscreteGroups.sglob.DzType
end

section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.Whittaker GlobalTheory.SplitWeil ValuativeRel Matrix

namespace DiscreteGroups.sglob.DzType

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {m : ℕ}

@[simp] theorem blk_eOne (i : Fin m) : blk (eOne m) i = i := rfl

@[simp] theorem eOne_mk (a : Fin m) (i : Fin 1) : eOne m ⟨a, i⟩ = a := rfl

def dl (p : parab k (eOne m)) : ℂˣ := deltaHalf k (fun _ : Fin m => Fin 1) (leviProj k (eOne m) p)

theorem dl_mul (p q : parab k (eOne m)) : dl (p * q) = dl p * dl q := by
  simp [dl, map_mul]

theorem dl_one : dl (1 : parab k (eOne m)) = 1 := by simp [dl]

theorem dl_eq_one {q : parab k (eOne m)} (hq : ∀ a, valuation k (((q : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) a a) = 1) :
    dl q = 1 := by
  rw [dl, deltaHalf_apply]
  refine Finset.prod_eq_one fun a _ => Units.ext ?_
  rw [val_absPow, Units.val_one]
  have hd : ((GeneralLinearGroup.det (leviProj k (eOne m) q a) : kˣ) : k) =
      ((q : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) a a := by
    simp only [GeneralLinearGroup.val_det_apply, det_unique]
    rfl
  rw [nabs_eq_one k (by rw [hd]; exact hq a)]
  simp

variable (S : Subgroup (GL (Fin m) k))

def InCell (g : GL (Fin m) k) : Prop := ∃ p : parab k (eOne m), ∃ y ∈ S, g = (p : GL (Fin m) k) * wRev k m * y

open Classical in

def cellFun (g : GL (Fin m) k) : ℂ := if h : InCell S g then (dl h.choose : ℂ) else 0

variable {S}

theorem cellFun_eq (hS4 : ∀ y ∈ S, ∀ a, valuation k (((y : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) a a) = 1)
    (p : parab k (eOne m)) {y : GL (Fin m) k} (hy : y ∈ S) :
    cellFun S ((p : GL (Fin m) k) * wRev k m * y) = dl p := by
  have h : InCell S ((p : GL (Fin m) k) * wRev k m * y) := ⟨p, y, hy, rfl⟩
  rw [cellFun, dif_pos h]
  obtain ⟨y', hy', e⟩ := h.choose_spec
  set p' := h.choose
  let q : parab k (eOne m) := p'⁻¹ * p
  have hq : ((q : GL (Fin m) k)) = wRev k m * (y' * y⁻¹) * (wRev k m)⁻¹ := by
    have e2 : (p : GL (Fin m) k) = p' * (wRev k m * (y' * y⁻¹) * (wRev k m)⁻¹) :=
      calc (p : GL (Fin m) k) = p * wRev k m * y * y⁻¹ * (wRev k m)⁻¹ := by group
        _ = p' * wRev k m * y' * y⁻¹ * (wRev k m)⁻¹ := by rw [e]
        _ = p' * (wRev k m * (y' * y⁻¹) * (wRev k m)⁻¹) := by group
    simp only [q, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [e2]
    group
  have hs : y' * y⁻¹ ∈ S := S.mul_mem hy' (S.inv_mem hy)
  have h1 : dl q = 1 := dl_eq_one fun a => by
    rw [hq, wRev_inv, wRev_conj_apply]
    exact hS4 _ hs _
  have : p = p' * q := by simp [q]
  rw [this, dl_mul, h1, mul_one]

end DiscreteGroups.sglob.DzType
end
end

section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.Whittaker GlobalTheory.SplitWeil ValuativeRel Matrix

namespace DiscreteGroups.sglob.DzType

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {m : ℕ}
  {S : Subgroup (GL (Fin m) k)}

theorem inCell_mul_left_iff (p₀ : parab k (eOne m)) (g : GL (Fin m) k) :
    InCell S ((p₀ : GL (Fin m) k) * g) ↔ InCell S g := by
  constructor
  · rintro ⟨p, y, hy, e⟩
    refine ⟨p₀⁻¹ * p, y, hy, ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc g = (p₀ : GL (Fin m) k)⁻¹ * ((p₀ : GL (Fin m) k) * g) := by group
      _ = _ := by rw [e]; group
  · rintro ⟨p, y, hy, e⟩
    exact ⟨p₀ * p, y, hy, by rw [e]; simp only [Subgroup.coe_mul]; group⟩

theorem inCell_mul_right_iff {s : GL (Fin m) k} (hs : s ∈ S) (g : GL (Fin m) k) :
    InCell S (g * s) ↔ InCell S g := by
  constructor
  · rintro ⟨p, y, hy, e⟩
    refine ⟨p, y * s⁻¹, S.mul_mem hy (S.inv_mem hs), ?_⟩
    calc g = g * s * s⁻¹ := by group
      _ = _ := by rw [e]; group
  · rintro ⟨p, y, hy, e⟩
    exact ⟨p, y * s, S.mul_mem hy hs, by rw [e]; group⟩

variable (hS4 : ∀ y ∈ S, ∀ a, valuation k (((y : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) a a) = 1)
include hS4

theorem cellFun_mul_left (p₀ : parab k (eOne m)) (g : GL (Fin m) k) :
    cellFun S ((p₀ : GL (Fin m) k) * g) = dl p₀ * cellFun S g := by
  by_cases h : InCell S g
  · obtain ⟨p, y, hy, rfl⟩ := h
    have e : (p₀ : GL (Fin m) k) * (p * wRev k m * y) = ((p₀ * p : parab k (eOne m)) : GL (Fin m) k) * wRev k m * y := by
      simp only [Subgroup.coe_mul]; group
    rw [e, cellFun_eq hS4 _ hy, cellFun_eq hS4 _ hy, dl_mul, Units.val_mul]
  · have h' : ¬ InCell S ((p₀ : GL (Fin m) k) * g) := fun h' => h ((inCell_mul_left_iff p₀ g).1 h')
    rw [cellFun, dif_neg h', cellFun, dif_neg h, mul_zero]

theorem cellFun_mul_right {s : GL (Fin m) k} (hs : s ∈ S) (g : GL (Fin m) k) :
    cellFun S (g * s) = cellFun S g := by
  by_cases h : InCell S g
  · obtain ⟨p, y, hy, rfl⟩ := h
    have e : (p : GL (Fin m) k) * wRev k m * y * s = p * wRev k m * (y * s) := by group
    rw [e, cellFun_eq hS4 _ (S.mul_mem hy hs), cellFun_eq hS4 _ hy]
  · rw [cellFun, dif_neg (fun h' => h ((inCell_mul_right_iff hs g).1 h')), cellFun, dif_neg h]

end DiscreteGroups.sglob.DzType
end
end

section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.Whittaker GlobalTheory.SplitWeil ValuativeRel Matrix

namespace DiscreteGroups.sglob.DzType

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {m : ℕ}
  {S : Subgroup (GL (Fin m) k)}

def cellVec (hS1 : KOne k (Fin m) ≤ S)
    (hS4 : ∀ y ∈ S, ∀ a, valuation k (((y : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) a a) = 1) :
    IndSp (eOne m) (ofChar (1 : Levi k (fun _ : Fin m => Fin 1) →* ℂˣ)) :=
  ⟨⟨cellFun S, fun p g => by
      rw [cellFun_mul_left hS4]
      simp [dl]⟩,
    mem_smoothPart_of_nhds (Filter.mem_of_superset (GlobalTheory.StepData.isOpen_KOne.mem_nhds (one_mem _)) fun x hx =>
      Subtype.ext (funext fun g => cellFun_mul_right hS4 (hS1 hx) g))⟩

variable (hS1 : KOne k (Fin m) ≤ S)
  (hS4 : ∀ y ∈ S, ∀ a, valuation k (((y : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) a a) = 1)

theorem cellVec_apply (g : GL (Fin m) k) : (cellVec hS1 hS4).1.1 g = cellFun S g := rfl

theorem cellVec_fixed {s : GL (Fin m) k} (hs : s ∈ S) : psOne k m s (cellVec hS1 hS4) = cellVec hS1 hS4 :=
  Subtype.ext (Subtype.ext (funext fun g => cellFun_mul_right hS4 hs g))

open Classical in
include hS1 hS4 in
theorem cellFun_wRev (hS2 : S ≤ KO k (Fin m))
    (hS3 : ∀ y ∈ S, ∀ a b, a < b → valuation k (((y : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) a b) < 1)
    {c : GL (Fin m) k} (hc : c ∈ unipB k (Fin m)) :
    cellFun S (wRev k m * c⁻¹) = if c ∈ KOne k (Fin m) then 1 else 0 := by
  split_ifs with hK
  · have e : wRev k m * c⁻¹ = (((1 : parab k (eOne m)) : GL (Fin m) k)) * wRev k m * c⁻¹ := by simp
    rw [e, cellFun_eq hS4 1 (hS1 (inv_mem hK)), dl_one, Units.val_one]
  · rw [cellFun, dif_neg]
    rintro ⟨p, y, hy, e⟩
    apply hK
    have hy' : y = (wRev k m * (p : GL (Fin m) k)⁻¹ * wRev k m) * c⁻¹ :=
      calc y = ((p : GL (Fin m) k) * wRev k m)⁻¹ * ((p : GL (Fin m) k) * wRev k m * y) := by group
        _ = ((p : GL (Fin m) k) * wRev k m)⁻¹ * (wRev k m * c⁻¹) := by rw [← e]
        _ = (wRev k m)⁻¹ * (p : GL (Fin m) k)⁻¹ * wRev k m * c⁻¹ := by group
        _ = _ := by rw [wRev_inv]
    have hci : c⁻¹ ∈ unipB k (Fin m) := inv_mem hc
    have hX : ∀ i j, ((((wRev k m * (p : GL (Fin m) k)⁻¹ * wRev k m : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) *
        ((c⁻¹ : GL (Fin m) k) : Matrix (Fin m) (Fin m) k)) i j) = ((y : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) i j := by
      intro i j; rw [hy']; simp only [Units.val_mul]
    have hpi : ((p : GL (Fin m) k)⁻¹) ∈ parab k (eOne m) := inv_mem p.2
    have key := valuation_unitri_lt (valuation k)
      (((wRev k m * (p : GL (Fin m) k)⁻¹ * wRev k m : GL (Fin m) k) : Matrix (Fin m) (Fin m) k))
      (((c⁻¹ : GL (Fin m) k) : Matrix (Fin m) (Fin m) k))
      (fun i j hij => by
        rw [wRev_conj_apply]
        exact (mem_parab.1 hpi) (Fin.rev i) (Fin.rev j) (by simpa using Fin.rev_lt_rev.2 hij))
      (fun i => ((mem_unipB _).1 hci).2 i) (fun i j hij => ((mem_unipB _).1 hci).1 i j hij)
      (fun i j => by rw [hX]; exact val_le_of_mem_KO (hS2 hy) i j)
      (fun i => by rw [hX]; exact hS4 y hy i)
      (fun i j hij => by rw [hX]; exact hS3 y hy i j hij)
    have hK' : c⁻¹ ∈ KOne k (Fin m) := mem_KOne_of_unip hci key
    simpa using inv_mem hK'

end DiscreteGroups.sglob.DzType
end
end

section
namespace DiscreteGroups.sglob.DzType

theorem exists_functional_of_finite {G X : Type} [Group G] [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ G X) (N : Set G) (θ : G → ℂ) (v : X)
    (h : ∀ F : Finset G, (↑F ⊆ N) →
      ∃ Λ : Module.Dual ℂ X, (∀ u ∈ F, ∀ x, Λ (ρ u x) = θ u * Λ x) ∧ Λ v ≠ 0) :
    ∃ l : Module.Dual ℂ X, (∀ u ∈ N, ∀ x, l (ρ u x) = θ u * l x) ∧ l v ≠ 0 := by
  classical
  set S : Set X := {y | ∃ u ∈ N, ∃ x, y = ρ u x - θ u • x} with hSdef
  set T : Submodule ℂ X := Submodule.span ℂ S with hTdef
  have hv : v ∉ T := by
    intro hvT
    obtain ⟨A, hA, hvA⟩ := Submodule.mem_span_finite_of_mem_span hvT
    let f : X → G := fun t => if h : ∃ u ∈ N, ∃ x, t = ρ u x - θ u • x then h.choose else 1
    have hf : ∀ t ∈ A, f t ∈ N ∧ ∃ x, t = ρ (f t) x - θ (f t) • x := by
      intro t ht
      have h' : ∃ u ∈ N, ∃ x, t = ρ u x - θ u • x := hA ht
      simp only [f, dif_pos h']
      exact ⟨h'.choose_spec.1, h'.choose_spec.2⟩
    obtain ⟨Λ, hΛ, hΛv⟩ := h (A.image f) (by
      intro u hu
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hu
      exact (hf t ht).1)
    apply hΛv
    have hle : Submodule.span ℂ (↑A : Set X) ≤ LinearMap.ker Λ := by
      rw [Submodule.span_le]
      intro t ht
      obtain ⟨-, x, hx⟩ := hf t ht
      rw [SetLike.mem_coe, LinearMap.mem_ker, hx, map_sub, map_smul,
        hΛ _ (Finset.mem_image_of_mem f ht) x, smul_eq_mul, sub_self]
    exact hle hvA
  have hq : T.mkQ v ≠ 0 := by
    rw [Ne, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hv
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ (X ⧸ T), φ (T.mkQ v) ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hq ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 hc)
  refine ⟨φ ∘ₗ T.mkQ, fun u hu x => ?_, hφ⟩
  have hmem : ρ u x - θ u • x ∈ T := Submodule.subset_span ⟨u, hu, x, rfl⟩
  have h0 : (φ ∘ₗ T.mkQ) (ρ u x - θ u • x) = 0 := by
    rw [LinearMap.comp_apply, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero T).2 hmem, map_zero]
  set l := φ ∘ₗ T.mkQ
  rw [map_sub, map_smul, smul_eq_mul, sub_eq_zero] at h0
  exact h0

end DiscreteGroups.sglob.DzType
end

section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.Whittaker GlobalTheory.SplitWeil ValuativeRel Matrix MeasureTheory

namespace DiscreteGroups.sglob.DzType

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {m : ℕ}

abbrev PS (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m : ℕ) : Type :=
  IndSp (eOne m) (ofChar (1 : Levi k (fun _ : Fin m => Fin 1) →* ℂˣ))

theorem continuous_ps (f : PS k m) : Continuous f.1.1 := by
  rw [continuous_iff_continuousAt]
  intro g₀
  have hU : IsOpen {x : GL (Fin m) k | ind (parab k (eOne m))
      ((twist (ofChar (1 : Levi k (fun _ : Fin m => Fin 1) →* ℂˣ)) (deltaHalf k _)).comp (leviProj k (eOne m))) x f.1 =
        f.1} := f.2
  have h1 : (1 : GL (Fin m) k) ∈ {x : GL (Fin m) k | ind (parab k (eOne m))
      ((twist (ofChar (1 : Levi k (fun _ : Fin m => Fin 1) →* ℂˣ)) (deltaHalf k _)).comp (leviProj k (eOne m))) x f.1 =
        f.1} := by simp
  have hc : Continuous fun x : GL (Fin m) k => g₀⁻¹ * x := continuous_const.mul continuous_id
  have hmem := hc.continuousAt.preimage_mem_nhds (x := g₀) (by rw [inv_mul_cancel]; exact hU.mem_nhds h1)
  have hev : (fun _ => f.1.1 g₀) =ᶠ[nhds g₀] f.1.1 := by
    refine Filter.mem_of_superset hmem fun x hx => ?_
    have h2 : f.1.1 (g₀ * (g₀⁻¹ * x)) = f.1.1 g₀ := congrArg (fun F => F.1 g₀) hx
    rw [mul_inv_cancel_left] at h2
    exact h2.symm
  exact continuousAt_const.congr hev

def thC (ψ : AddChar k Circle) (c : GL (Fin m) k) : ℂ := ((ψ⁻¹) (superDiag c) : ℂ)

theorem thC_mul (ψ : AddChar k Circle) {a b : GL (Fin m) k} (ha : a ∈ unipB k (Fin m)) (hb : b ∈ unipB k (Fin m)) :
    thC ψ (a * b) = thC ψ a * thC ψ b := by
  simp [thC, superDiag_mul ha hb, AddChar.map_add_eq_mul]

theorem continuous_superDiag : Continuous (superDiag : GL (Fin m) k → k) := by
  unfold superDiag
  exact continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
    (Units.continuous_val (M := Matrix (Fin m) (Fin m) k)).matrix_elem i j

theorem continuous_thC (ψ : AddChar k Circle) (hψc : Continuous ψ) : Continuous (thC ψ : GL (Fin m) k → ℂ) := by
  have : (thC ψ : GL (Fin m) k → ℂ) = fun c => ((ψ (-superDiag c) : Circle) : ℂ) := by
    funext c; simp [thC, AddChar.inv_apply]
  rw [this]
  exact continuous_subtype_val.comp (hψc.comp continuous_superDiag.neg)

theorem thC_of_mem_KOne (ψ : AddChar k Circle) (hψ : ∀ x, valuation k x < 1 → ψ x = 1) {c : GL (Fin m) k}
    (hc : c ∈ KOne k (Fin m)) : thC ψ c = 1 := by
  have hv : valuation k (superDiag c) < 1 := by
    unfold superDiag
    refine Valuation.map_sum_lt _ one_ne_zero fun i _ => Valuation.map_sum_lt _ one_ne_zero fun j hj => ?_
    have hij : i ≠ j := by
      intro h; have := (Finset.mem_filter.1 hj).2; rw [h] at this; omega
    exact val_lt_of_mem_KOne hc hij
  have h1 : ψ (-superDiag c) = 1 := hψ _ (by rwa [Valuation.map_neg])
  simp [thC, AddChar.inv_apply, h1]

end DiscreteGroups.sglob.DzType
end
end

section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.Whittaker GlobalTheory.SplitWeil ValuativeRel Matrix MeasureTheory

namespace DiscreteGroups.sglob.DzType

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {m : ℕ}

theorem exists_cell_functional {S : Subgroup (GL (Fin m) k)} (hS1 : KOne k (Fin m) ≤ S)
    (hS2 : S ≤ KO k (Fin m))
    (hS3 : ∀ y ∈ S, ∀ a b, a < b → valuation k (((y : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) a b) < 1)
    (hS4 : ∀ y ∈ S, ∀ a, valuation k (((y : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) a a) = 1)
    (ψ : AddChar k Circle) (hψc : Continuous ψ) (hψ : ∀ x, valuation k x < 1 → ψ x = 1) :
    ∃ l : Module.Dual ℂ (PS k m), IsFunctional ψ⁻¹ (psOne k m) l ∧ l (cellVec hS1 hS4) ≠ 0 := by
  suffices key : ∀ F : Finset (GL (Fin m) k), (↑F ⊆ (unipB k (Fin m) : Set (GL (Fin m) k))) →
      ∃ Λ : Module.Dual ℂ (PS k m), (∀ u ∈ F, ∀ x, Λ (psOne k m u x) = thC ψ u * Λ x) ∧ Λ (cellVec hS1 hS4) ≠ 0 by
    obtain ⟨l, hl, hlv⟩ := exists_functional_of_finite (psOne k m) (unipB k (Fin m) : Set (GL (Fin m) k)) (thC ψ)
      (cellVec hS1 hS4) key
    exact ⟨l, fun u hu x => hl u hu x, hlv⟩
  intro F hF
  obtain ⟨C, hCc, hCN, hFC⟩ := exists_compact_unip F (fun u hu => hF hu)
  letI : MeasurableSpace C := borel C
  haveI : BorelSpace C := ⟨rfl⟩
  haveI : CompactSpace C := isCompact_iff_compactSpace.mp hCc
  let μ : Measure C := Measure.haar
  let Φ : PS k m → C → ℂ := fun f c => f.1.1 (wRev k m * (c : GL (Fin m) k)⁻¹) * thC ψ (c : GL (Fin m) k)
  have hΦc : ∀ f, Continuous (Φ f) := fun f =>
    ((continuous_ps f).comp (continuous_const.mul continuous_subtype_val.inv)).mul
      ((continuous_thC ψ hψc).comp continuous_subtype_val)
  have hΦi : ∀ f, Integrable (Φ f) μ := fun f => (hΦc f).integrable_of_hasCompactSupport
    (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (Set.subset_univ _))
  let Λ : Module.Dual ℂ (PS k m) :=
    { toFun := fun f => ∫ c, Φ f c ∂μ
      map_add' := fun f g => by
        rw [← integral_add (hΦi f) (hΦi g)]
        congr 1
        funext c
        simp [Φ, add_mul]
      map_smul' := fun a f => by
        rw [RingHom.id_apply, smul_eq_mul, ← integral_const_mul]
        congr 1
        funext c
        simp [Φ, mul_assoc] }
  refine ⟨Λ, fun u hu x => ?_, ?_⟩
  · have huC : u ∈ C := hFC u hu
    have huN : u ∈ unipB k (Fin m) := hCN huC
    let uC : C := ⟨u, huC⟩
    show ∫ c, Φ (psOne k m u x) c ∂μ = thC ψ u * ∫ c, Φ x c ∂μ
    rw [← integral_mul_left_eq_self (Φ x) uC⁻¹, ← integral_const_mul]
    congr 1
    funext c
    have hcN : (c : GL (Fin m) k) ∈ unipB k (Fin m) := hCN c.2
    have e1 : ((uC⁻¹ * c : C) : GL (Fin m) k) = u⁻¹ * c := rfl
    have e2 : thC ψ (c : GL (Fin m) k) = thC ψ u * thC ψ (u⁻¹ * (c : GL (Fin m) k)) := by
      rw [← thC_mul ψ huN (mul_mem (inv_mem huN) hcN), mul_inv_cancel_left]
    simp only [Φ, e1]
    rw [e2, _root_.mul_inv_rev, inv_inv]
    show x.1.1 (wRev k m * (c : GL (Fin m) k)⁻¹ * u) * _ = _
    rw [mul_assoc (wRev k m)]
    ring
  · show ∫ c, Φ (cellVec hS1 hS4) c ∂μ ≠ 0
    set s : Set C := {c | (c : GL (Fin m) k) ∈ KOne k (Fin m)} with hsdef
    have hs : IsOpen s := GlobalTheory.StepData.isOpen_KOne.preimage continuous_subtype_val
    have hΦ : Φ (cellVec hS1 hS4) = s.indicator (fun _ => (1 : ℂ)) := by
      funext c
      simp only [Φ, cellVec_apply]
      rw [cellFun_wRev hS1 hS4 hS2 hS3 (hCN c.2)]
      by_cases hcK : (c : GL (Fin m) k) ∈ KOne k (Fin m)
      · rw [if_pos hcK, Set.indicator_of_mem (show c ∈ s from hcK), thC_of_mem_KOne ψ hψ hcK, one_mul]
      · rw [if_neg hcK, Set.indicator_of_notMem (show c ∉ s from hcK), zero_mul]
    rw [hΦ, integral_indicator_const _ hs.measurableSet]
    have hpos : 0 < μ.real s :=
      ENNReal.toReal_pos (hs.measure_ne_zero μ ⟨1, show ((1 : C) : GL (Fin m) k) ∈ KOne k (Fin m) from one_mem _⟩) (measure_ne_top μ s)
    rw [Complex.real_smul, mul_one]
    exact_mod_cast hpos.ne'

end DiscreteGroups.sglob.DzType
end
end

section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
  GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Whittaker ValuativeRel

namespace DiscreteGroups.sglob.DzType

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem fixed_ne_bot_of_equiv' {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {π : Representation ℂ G V} {σ : Representation ℂ G W} (φ : π.Equiv σ) {K : Subgroup G}
    (hπ : fixed π K ≠ ⊥) : fixed σ K ≠ ⊥ := by
  obtain ⟨v, hv, h0⟩ := (Submodule.ne_bot_iff _).1 hπ
  refine (Submodule.ne_bot_iff _).2 ⟨φ v, GlobalTheory.Parabolic.mem_fixed.2 fun u hu => ?_, fun h1 => h0 ?_⟩
  · exact (φ.toIntertwiningMap.isIntertwining _ _ u v).symm.trans
      (congrArg φ (GlobalTheory.Parabolic.mem_fixed.1 hv u hu))
  · exact φ.toLinearEquiv.injective (h1.trans (map_zero _).symm)

theorem isLower_iff {g m : ℕ} [Fact g.Prime] (b : Gn g m) :
    IsLower b ↔ (b : Mt g m).BlockTriangular OrderDual.toDual := Iff.rfl

def lowZ (g m : ℕ) [Fact g.Prime] : Subgroup (GL (Fin m) ℤ_[g]) where
  carrier := {x | IsLower (GlobalTheory.GLp.red g m x)}
  one_mem' := by
    show IsLower (GlobalTheory.GLp.red g m 1)
    rw [map_one, isLower_iff, Units.val_one]
    exact Matrix.blockTriangular_one
  mul_mem' := by
    intro x y hx hy
    show IsLower (GlobalTheory.GLp.red g m (x * y))
    rw [map_mul, isLower_iff, Units.val_mul]
    exact Matrix.BlockTriangular.mul hx hy
  inv_mem' := by
    intro x hx
    show IsLower (GlobalTheory.GLp.red g m x⁻¹)
    have : Invertible ((GlobalTheory.GLp.red g m x : Gn g m) : Mt g m) := (GlobalTheory.GLp.red g m x).invertible
    rw [map_inv, isLower_iff, Matrix.coe_units_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular hx

theorem toZMod_eq_zero_iff {g : ℕ} [Fact g.Prime] (x : ℤ_[g]) : PadicInt.toZMod x = 0 ↔ ‖(x : ℚ_[g])‖ < 1 := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits,
    PadicInt.padic_norm_e_of_padicInt]

section Place

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {g : ℕ} [Fact g.Prime]
  (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i)

def lowS (m : ℕ) : Subgroup (GL (Fin m) (w.adicCompletion E)) :=
  (lowZ g m).map ((Matrix.GeneralLinearGroup.map i.toRingHom).comp (GlobalTheory.GLp.inc g m))

theorem lowS_apply {m : ℕ} (x : GL (Fin m) ℤ_[g]) (a b : Fin m) :
    ((((Matrix.GeneralLinearGroup.map i.toRingHom).comp (GlobalTheory.GLp.inc g m)) x : GL (Fin m) (w.adicCompletion E)) :
      Matrix (Fin m) (Fin m) (w.adicCompletion E)) a b = i ((x : Matrix (Fin m) (Fin m) ℤ_[g]) a b : ℚ_[g]) := rfl

include hi

theorem lowS_one (m : ℕ) : KOne (w.adicCompletion E) (Fin m) ≤ lowS i m := by
  intro y hy
  obtain ⟨x, hx1, hx2⟩ := DiscreteGroups.sglob.DzIso.exists_of_mem_KOne i hi hy
  refine ⟨x, ?_, hx2⟩
  show IsLower (GlobalTheory.GLp.red g m x)
  rw [hx1, isLower_iff, Units.val_one]
  exact Matrix.blockTriangular_one

theorem lowS_KO (m : ℕ) : lowS i m ≤ KO (w.adicCompletion E) (Fin m) := by
  rintro _ ⟨x, -, rfl⟩
  exact DiscreteGroups.sglob.DzIso.map_inc_mem_KO i hi x

theorem lowS_upper (m : ℕ) : ∀ y ∈ lowS i m, ∀ a b, a < b →
    valuation (w.adicCompletion E) (((y : GL (Fin m) (w.adicCompletion E)) : Matrix (Fin m) (Fin m) _) a b) < 1 := by
  rintro _ ⟨x, hx, rfl⟩ a b hab
  rw [lowS_apply, DiscreteGroups.sglob.DzIso.valuation_lt_iff i hi, ← toZMod_eq_zero_iff]
  exact hx a b hab

theorem lowS_diag (m : ℕ) : ∀ y ∈ lowS i m, ∀ a,
    valuation (w.adicCompletion E) (((y : GL (Fin m) (w.adicCompletion E)) : Matrix (Fin m) (Fin m) _) a a) = 1 := by
  rintro _ ⟨x, hx, rfl⟩ a
  rw [lowS_apply]
  have hdet : ((GlobalTheory.GLp.red g m x : Gn g m) : Mt g m).det ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]
    exact Units.ne_zero _
  rw [Matrix.det_of_lowerTriangular _ hx] at hdet
  have hd : PadicInt.toZMod ((x : Matrix (Fin m) (Fin m) ℤ_[g]) a a) ≠ 0 :=
    (Finset.prod_ne_zero_iff.1 hdet) a (Finset.mem_univ a)
  rw [Ne, toZMod_eq_zero_iff] at hd
  refine le_antisymm ((DiscreteGroups.sglob.DzIso.valuation_le_iff i hi _).2 ?_) (not_lt.1 fun h => hd ?_)
  · rw [PadicInt.padic_norm_e_of_padicInt]; exact PadicInt.norm_le_one _
  · exact (DiscreteGroups.sglob.DzIso.valuation_lt_iff i hi _).1 h

theorem psi_of_lifts {ψ₀ : AddChar (ZMod g) Circle} {ψ : AddChar (w.adicCompletion E) Circle} (hL : Lifts1 i ψ₀ ψ) :
    ∀ y, valuation (w.adicCompletion E) y < 1 → ψ y = 1 := by
  intro y hy
  have hx : ‖i.symm y‖ < 1 := (DiscreteGroups.sglob.DzIso.valuation_lt_iff i hi (i.symm y)).1 (by simpa using hy)
  let z : ℤ_[g] := ⟨i.symm y, hx.le⟩
  have hz : PadicInt.toZMod z = 0 := (toZMod_eq_zero_iff z).2 hx
  have h := hL z
  rw [hz, AddChar.map_zero_eq_one] at h
  have e : i (z : ℚ_[g]) = y := by simp [z]
  rwa [e] at h

end Place

theorem lGen : LGen := by
  intro H E _ _ w g _ i hi ψ₀ _ ψ hψc hL m
  obtain ⟨hirr, hsph, hcen⟩ := genA H (w.adicCompletion E) m
  let τ₀ : IrrRep (GL (Fin m) (w.adicCompletion E)) :=
    ⟨PS (w.adicCompletion E) m, psOne (w.adicCompletion E) m, isSmooth_parInd _ _, hirr⟩
  refine ⟨τ₀, 1, ?_, hcen, ?_⟩
  · obtain ⟨φ⟩ := IrrRep.nonempty_equiv_rep τ₀
    exact fixed_ne_bot_of_equiv' φ.symm hsph
  · obtain ⟨l, hl, hlv⟩ := exists_cell_functional (lowS_one i hi m) (lowS_KO i hi m) (lowS_upper i hi m)
      (lowS_diag i hi m) ψ hψc (psi_of_lifts i hi hL)
    exact ⟨l, cellVec (lowS_one i hi m) (lowS_diag i hi m), hl, hlv, fun x hx =>
      cellVec_fixed (lowS_one i hi m) (lowS_diag i hi m) ⟨x, hx, rfl⟩⟩

end DiscreteGroups.sglob.DzType
end
end
