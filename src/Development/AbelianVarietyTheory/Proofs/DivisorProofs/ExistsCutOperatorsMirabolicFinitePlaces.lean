import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerInfMemLocSpan
import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfMemCell
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSupportComp
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWhittakerCutInductionStepOfOpenSubgroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhitMulLocGLDiagPowOfFixed
import Development.AbelianVarietyTheory.Definitions.Divisors.NAInterSupSSubset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerMemSchwartzBruhatFinitePlace
import GroundTheory.GlobalFields.TateThesis.RootNumberLocalPlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCutOperatorTransferAdelicWhittaker

section
section
open Matrix Topology

namespace GlobalTheory.JSW.Cut

theorem cuts_mul_open_subgroup {F : Type} [NormedField F] (ψ : AddChar F ℂ) {n : ℕ}
    (U : Subgroup (GL (Fin n) F)) (hU : IsOpen (U : Set (GL (Fin n) F))) (X A : Set (GL (Fin n) F))
    (hX : ∀ x ∈ X, ∀ u ∈ U, x * u ∈ X) (h : Cuts ψ (U : Set (GL (Fin n) F)) X A) :
    ∃ U₁ : Subgroup (GL (Fin n) F), U₁ ≤ U ∧ IsOpen (U₁ : Set (GL (Fin n) F)) ∧
      Cuts ψ (U : Set (GL (Fin n) F)) X {g | ∃ a ∈ A, ∃ u ∈ U₁, g = a * u} := by
  obtain ⟨T, hT⟩ := h
  let U₁ : Subgroup (GL (Fin n) F) :=
    { carrier := {u | u ∈ U ∧ ∀ k ∈ T.support, k⁻¹ * u * k ∈ U}
      one_mem' := ⟨one_mem _, fun k _ => by simpa using one_mem U⟩
      mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, fun k hk => by
        have := mul_mem (ha.2 k hk) (hb.2 k hk)
        simpa [mul_assoc] using this⟩
      inv_mem' := fun {a} ha => ⟨inv_mem ha.1, fun k hk => by
        have := inv_mem (ha.2 k hk)
        simpa [mul_assoc] using this⟩ }
  refine ⟨U₁, fun u hu => hu.1, ?_, T, ?_⟩
  · have : (U₁ : Set (GL (Fin n) F)) = (U : Set (GL (Fin n) F)) ∩
        ⋂ k ∈ T.support, (fun u : GL (Fin n) F => k⁻¹ * u * k) ⁻¹' (U : Set (GL (Fin n) F)) := by
      ext u
      simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
      rfl
    rw [this]
    exact hU.inter (isOpen_biInter_finset fun k _ =>
      hU.preimage ((continuous_const.mul continuous_id).mul continuous_const))
  · rintro f hf hfU g ⟨a, ha, u, hu, rfl⟩
    have h1 : act T f (a * u) = act T f a := by
      unfold act
      refine Finset.sum_congr rfl fun k hk => ?_
      have e : a * u * k = a * k * (k⁻¹ * u * k) := by group
      simp only
      rw [e, hfU _ (hu.2 k hk)]
    rw [h1, hT f hf hfU a ha]
    by_cases hx : a ∈ X
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hX a hx u hu.1), hfU u hu.1]
    · have hx' : a * u ∉ X := fun h' => hx (by simpa using hX _ h' u⁻¹ (inv_mem hu.1))
      rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx']

end GlobalTheory.JSW.Cut
end

open Matrix Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittakerIndicatorCut_mul_open_subgroup : ∀ {F : Type} [NormedField F] (ψ : AddChar F ℂ) {n : ℕ} (U : Subgroup (GL (Fin n) F)), IsOpen (U : Set (GL (Fin n) F)) → ∀ X A : Set (GL (Fin n) F), (∀ x ∈ X, ∀ u ∈ U, x * u ∈ X) → GlobalTheory.JSW.Cut.Cuts ψ (U : Set (GL (Fin n) F)) X A → ∃ U₁ : Subgroup (GL (Fin n) F), U₁ ≤ U ∧ IsOpen (U₁ : Set (GL (Fin n) F)) ∧ GlobalTheory.JSW.Cut.Cuts ψ (U : Set (GL (Fin n) F)) X {g | ∃ a ∈ A, ∃ u ∈ U₁, g = a * u} := by
  atlas_forward_decl GlobalTheory.JSW.Cut.cuts_mul_open_subgroup
end

section
open Matrix Topology

noncomputable section

namespace GlobalTheory.JSW.Cut.Block

open GlobalTheory.JSW.KirFin GlobalTheory.SmGL

variable {F : Type} [NormedField F] {m : ℕ}

open Matrix Topology in
variable {F : Type} [NormedField F] {m : ℕ} in
theorem _root_.GlobalTheory.JSW.Cut.Block.mir_inv (a : GL (Fin m) F) (y : Fin m → F) :
    (_root_.GlobalTheory.JSW.KirFin.mir a y)⁻¹ =
      _root_.GlobalTheory.JSW.KirFin.mir a⁻¹ (-((a⁻¹).val *ᵥ y)) := by
  apply inv_eq_of_mul_eq_one_right
  rw [_root_.GlobalTheory.JSW.KirFin.mir_mul]
  simp [mulVec_neg, mulVec_mulVec, ← _root_.GlobalTheory.JSW.KirFin.mir_one]

theorem mir_left_inj {g h : GL (Fin m) F} {x y : Fin m → F} (e : mir g x = mir h y) : g = h := by
  ext i j
  have := congrArg (fun p : GL (Fin (m + 1)) F => p.val i.castSucc j.castSucc) e
  simpa using this

def blocks (U : Subgroup (GL (Fin (m + 1)) F)) : Subgroup (GL (Fin m) F) where
  carrier := {a | ∃ y, mir a y ∈ U}
  one_mem' := ⟨0, by rw [mir_one]; exact U.one_mem⟩
  mul_mem' := by
    rintro a b ⟨y, hy⟩ ⟨z, hz⟩
    exact ⟨a.val *ᵥ z + y, by rw [← mir_mul]; exact U.mul_mem hy hz⟩
  inv_mem' := by
    rintro a ⟨y, hy⟩
    exact ⟨_, by rw [← mir_inv]; exact U.inv_mem hy⟩

theorem exists_blocks_cell_cor_iff : ∀ {F : Type} [NormedField F] {m : ℕ} (U : Subgroup (GL (Fin (m + 2)) F)), IsCompact (U : Set (GL (Fin (m + 2)) F)) → IsOpen (U : Set (GL (Fin (m + 2)) F)) → ∃ B : Subgroup (GL (Fin (m + 1)) F), IsCompact (B : Set (GL (Fin (m + 1)) F)) ∧ IsOpen (B : Set (GL (Fin (m + 1)) F)) ∧ (∀ b, GlobalTheory.JSW.KirFin.cor b ∈ U → b ∈ B) ∧ ∀ h₀ h : GL (Fin (m + 1)) F, GlobalTheory.JSW.KirFin.cor h ∈ GlobalTheory.JSW.Cut.cell (GlobalTheory.JSW.KirFin.cor h₀) (U : Set (GL (Fin (m + 2)) F)) ↔ h ∈ GlobalTheory.JSW.Cut.cell h₀ (B : Set (GL (Fin (m + 1)) F)) := by
  intro F _ m U hUc hUo
  refine ⟨blocks U, isCompact_blocks hUc, ?_, fun b hb => ⟨0, hb⟩, fun h₀ h => ?_⟩
  · exact Subgroup.isOpen_mono (H₁ := U.comap cor) (fun b hb => ⟨0, hb⟩) (hUo.preimage continuous_cor)
  constructor
  · rintro ⟨n, hn, u, hu, e⟩
    obtain ⟨n', x, rfl⟩ := exists_mir (lr_of_mem hn)
    have hlu : lr u = lr 1 := by
      have h1 : lr (cor h) = lr (1 * u) := by
        rw [e]
        refine lr_mul_congr ?_ u
        rw [lr_mul_congr (lr_of_mem hn) _, one_mul]
        exact lr_mir h₀ 0
      rw [one_mul] at h1
      rw [← h1]
      exact lr_mir h 0
    obtain ⟨a, y, rfl⟩ := exists_mir hlu
    refine ⟨n', mir_mem_iff.1 hn, a, ⟨y, hu⟩, ?_⟩
    change mir h 0 = mir n' x * mir h₀ 0 * mir a y at e
    rw [mir_mul, mir_mul] at e
    exact mir_left_inj e
  · rintro ⟨n', hn', a, ⟨y, hy⟩, rfl⟩
    refine ⟨mir n' (-((n' * h₀).val *ᵥ y)), mir_mem_iff.2 hn', mir a y, hy, ?_⟩
    change mir (n' * h₀ * a) 0 = mir n' _ * mir h₀ 0 * mir a y
    rw [mir_mul, mir_mul, mulVec_zero, zero_add, add_neg_cancel]

end GlobalTheory.JSW.Cut.Block
end
end

section
open Matrix Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_blockGroup_unipotentDoubleCosetCell_blockDiag_iff : ∀ {F : Type} [NormedField F] {m : ℕ} (U : Subgroup (GL (Fin (m + 2)) F)), IsCompact (U : Set (GL (Fin (m + 2)) F)) → IsOpen (U : Set (GL (Fin (m + 2)) F)) → ∃ B : Subgroup (GL (Fin (m + 1)) F), IsCompact (B : Set (GL (Fin (m + 1)) F)) ∧ IsOpen (B : Set (GL (Fin (m + 1)) F)) ∧ (∀ b, GlobalTheory.JSW.KirFin.cor b ∈ U → b ∈ B) ∧ ∀ h₀ h : GL (Fin (m + 1)) F, GlobalTheory.JSW.KirFin.cor h ∈ GlobalTheory.JSW.Cut.cell (GlobalTheory.JSW.KirFin.cor h₀) (U : Set (GL (Fin (m + 2)) F)) ↔ h ∈ GlobalTheory.JSW.Cut.cell h₀ (B : Set (GL (Fin (m + 1)) F)) := by
  first | (exact @GlobalTheory.JSW.Cut.Block.exists_blocks_cell_cor_iff) | (exact GlobalTheory.JSW.Cut.Block.exists_blocks_cell_cor_iff) | (intros; apply GlobalTheory.JSW.Cut.Block.exists_blocks_cell_cor_iff  <;> assumption)
end

section
open Matrix Topology

namespace GlobalTheory.JSW.Cut

open Pointwise

variable {F : Type} [NormedField F] {n : ℕ}

theorem cell_eq_of_mem (B' : Subgroup (GL (Fin n) F)) {x y g : GL (Fin n) F}
    (hx : g ∈ cell x (B' : Set (GL (Fin n) F))) (hy : g ∈ cell y (B' : Set (GL (Fin n) F))) :
    cell x (B' : Set (GL (Fin n) F)) = cell y (B' : Set (GL (Fin n) F)) := by
  obtain ⟨u, hu, k, hk, rfl⟩ := hx
  obtain ⟨u', hu', k', hk', he⟩ := hy
  have hy' : y = (u'⁻¹ * u) * x * (k * k'⁻¹) := by
    calc y = u'⁻¹ * (u' * y * k') * k'⁻¹ := by group
      _ = (u'⁻¹ * u) * x * (k * k'⁻¹) := by rw [← he]; group
  have hx' : x = (u⁻¹ * u') * y * (k' * k⁻¹) := by
    calc x = u⁻¹ * (u * x * k) * k⁻¹ := by group
      _ = (u⁻¹ * u') * y * (k' * k⁻¹) := by rw [he]; group
  ext g
  constructor
  · rintro ⟨v, hv, l, hl, rfl⟩
    refine ⟨v * (u⁻¹ * u'), mul_mem hv (mul_mem (inv_mem hu) hu'), k' * k⁻¹ * l,
      mul_mem (mul_mem hk' (inv_mem hk)) hl, ?_⟩
    rw [hx']; group
  · rintro ⟨v, hv, l, hl, rfl⟩
    refine ⟨v * (u'⁻¹ * u), mul_mem hv (mul_mem (inv_mem hu') hu), k * k'⁻¹ * l,
      mul_mem (mul_mem hk (inv_mem hk')) hl, ?_⟩
    rw [hy']; group

theorem cell_finite_disjoint_union (B B' : Subgroup (GL (Fin n) F)) (hB : IsCompact (B : Set (GL (Fin n) F)))
    (hB' : IsOpen (B' : Set (GL (Fin n) F))) (hle : B' ≤ B) (h₀ : GL (Fin n) F) :
    ∃ s : Finset (GL (Fin n) F), (∀ x ∈ s, x ∈ cell h₀ (B : Set (GL (Fin n) F))) ∧
      cell h₀ (B : Set (GL (Fin n) F)) = (⋃ x ∈ s, cell x (B' : Set (GL (Fin n) F))) ∧
      (s : Set (GL (Fin n) F)).PairwiseDisjoint fun x => cell x (B' : Set (GL (Fin n) F)) := by
  classical

  obtain ⟨t, ht⟩ := hB.elim_finite_subcover (fun b : B => (b : GL (Fin n) F) • (B' : Set (GL (Fin n) F)))
    (fun b => hB'.smul _) (fun b hb => Set.mem_iUnion.2 ⟨⟨b, hb⟩, ⟨1, one_mem _, by simp⟩⟩)
  set S : Finset (GL (Fin n) F) := t.image fun b : B => h₀ * (b : GL (Fin n) F) with hS
  have hSmem : ∀ x ∈ S, x ∈ cell h₀ (B : Set (GL (Fin n) F)) := by
    intro x hx
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 hx
    exact ⟨1, one_mem _, b, b.2, by simp⟩
  have hunion : cell h₀ (B : Set (GL (Fin n) F)) = ⋃ x ∈ S, cell x (B' : Set (GL (Fin n) F)) := by
    ext g
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨u, hu, k, hk, rfl⟩
      obtain ⟨b, hbt, hkb⟩ := Set.mem_iUnion₂.1 (ht hk)
      obtain ⟨k', hk', hkk⟩ := hkb
      refine ⟨h₀ * b, Finset.mem_image.2 ⟨b, hbt, rfl⟩, u, hu, k', hk', ?_⟩
      rw [← hkk]; simp [smul_eq_mul, mul_assoc]
    · rintro ⟨x, hx, u, hu, k, hk, rfl⟩
      obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 hx
      exact ⟨u, hu, b * k, mul_mem b.2 (hle hk), by simp [mul_assoc]⟩

  set f : GL (Fin n) F → Set (GL (Fin n) F) := fun x => cell x (B' : Set (GL (Fin n) F)) with hf
  set C : Finset (Set (GL (Fin n) F)) := S.image f with hC
  let rep : C → GL (Fin n) F := fun c => Classical.choose (Finset.mem_image.1 c.2)
  have rep_mem : ∀ c : C, rep c ∈ S := fun c => (Classical.choose_spec (Finset.mem_image.1 c.2)).1
  have rep_eq : ∀ c : C, f (rep c) = c := fun c => (Classical.choose_spec (Finset.mem_image.1 c.2)).2
  refine ⟨C.attach.image rep, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hx
    exact hSmem _ (rep_mem c)
  · rw [hunion]
    ext g
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨x, hx, hg⟩
      have hc : f x ∈ C := Finset.mem_image.2 ⟨x, hx, rfl⟩
      refine ⟨rep ⟨f x, hc⟩, Finset.mem_image.2 ⟨⟨f x, hc⟩, Finset.mem_attach _ _, rfl⟩, ?_⟩
      have := rep_eq ⟨f x, hc⟩
      change g ∈ f (rep ⟨f x, hc⟩)
      rw [this]; exact hg
    · rintro ⟨x, hx, hg⟩
      obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hx
      exact ⟨rep c, rep_mem c, hg⟩
  · intro x hx y hy hxy
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
    obtain ⟨d, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hy)
    rw [Function.onFun, Set.disjoint_left]
    intro g hgc hgd
    apply hxy
    have h1 := cell_eq_of_mem B' hgc hgd
    have hcd : c = d := by
      apply Subtype.ext
      rw [← rep_eq c, ← rep_eq d]
      exact h1
    rw [hcd]

theorem cell_finite_disjoint_union' : ∀ {F : Type} [NormedField F] {n : ℕ} (B B' : Subgroup (GL (Fin n) F)), IsCompact (B : Set (GL (Fin n) F)) → IsOpen (B' : Set (GL (Fin n) F)) → B' ≤ B → ∀ h₀ : GL (Fin n) F, ∃ s : Finset (GL (Fin n) F), (∀ x ∈ s, x ∈ GlobalTheory.JSW.Cut.cell h₀ (B : Set (GL (Fin n) F))) ∧ GlobalTheory.JSW.Cut.cell h₀ (B : Set (GL (Fin n) F)) = (⋃ x ∈ s, GlobalTheory.JSW.Cut.cell x (B' : Set (GL (Fin n) F))) ∧ (s : Set (GL (Fin n) F)).PairwiseDisjoint fun x => GlobalTheory.JSW.Cut.cell x (B' : Set (GL (Fin n) F)) :=
  fun B B' hB hB' hle h₀ => cell_finite_disjoint_union B B' hB hB' hle h₀

end GlobalTheory.JSW.Cut
end

section
open Matrix Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotentDoubleCosetCell_finite_disjoint_iUnion : ∀ {F : Type} [NormedField F] {n : ℕ} (B B' : Subgroup (GL (Fin n) F)), IsCompact (B : Set (GL (Fin n) F)) → IsOpen (B' : Set (GL (Fin n) F)) → B' ≤ B → ∀ h₀ : GL (Fin n) F, ∃ s : Finset (GL (Fin n) F), (∀ x ∈ s, x ∈ GlobalTheory.JSW.Cut.cell h₀ (B : Set (GL (Fin n) F))) ∧ GlobalTheory.JSW.Cut.cell h₀ (B : Set (GL (Fin n) F)) = (⋃ x ∈ s, GlobalTheory.JSW.Cut.cell x (B' : Set (GL (Fin n) F))) ∧ (s : Set (GL (Fin n) F)).PairwiseDisjoint fun x => GlobalTheory.JSW.Cut.cell x (B' : Set (GL (Fin n) F)) := by
  first | (exact @GlobalTheory.JSW.Cut.cell_finite_disjoint_union') | (exact GlobalTheory.JSW.Cut.cell_finite_disjoint_union') | (intros; apply GlobalTheory.JSW.Cut.cell_finite_disjoint_union'  <;> assumption)
end

section
section
noncomputable section

open Matrix Topology GlobalTheory.SmGL GlobalTheory.Whittaker

namespace GlobalTheory.JSW.Cut

open GlobalTheory.JSW.KirFin

variable {F : Type} [NormedField F]

namespace Red

theorem mul_mem_cell_iff {n : ℕ} {z : GL (Fin n) F} {U : Set (GL (Fin n) F)} {u : GL (Fin n) F}
    (hu : u ∈ unipB F (Fin n)) (g : GL (Fin n) F) : u * g ∈ cell z U ↔ g ∈ cell z U := by
  constructor
  · rintro ⟨v, hv, k, hk, e⟩
    refine ⟨u⁻¹ * v, mul_mem (inv_mem hu) hv, k, hk, ?_⟩
    have : g = u⁻¹ * (u * g) := by group
    rw [this, e]
    simp only [mul_assoc]
  · rintro ⟨v, hv, k, hk, rfl⟩
    exact ⟨u * v, mul_mem hu hv, k, hk, by simp only [mul_assoc]⟩

theorem cell_eq_of_mem {n : ℕ} {z g : GL (Fin n) F} {U : Subgroup (GL (Fin n) F)}
    (hg : g ∈ cell z (U : Set (GL (Fin n) F))) : cell g (U : Set (GL (Fin n) F)) = cell z U := by
  obtain ⟨v, hv, k, hk, rfl⟩ := hg
  ext x
  constructor
  · rintro ⟨u, hu, k', hk', rfl⟩
    exact ⟨u * v, mul_mem hu hv, k * k', mul_mem hk hk', by simp only [mul_assoc]⟩
  · rintro ⟨u, hu, k', hk', rfl⟩
    refine ⟨u * v⁻¹, mul_mem hu (inv_mem hv), k⁻¹ * k', mul_mem (inv_mem hk) hk', ?_⟩
    group

theorem act_mul_left {ψ : AddChar F ℂ} {n : ℕ} (T : GL (Fin n) F →₀ ℂ) {f : GL (Fin n) F → ℂ} (hf : Eqv ψ f)
    {u : GL (Fin n) F} (hu : u ∈ unipB F (Fin n)) (g : GL (Fin n) F) :
    act T f (u * g) = ψ (superDiag u) * act T f g := by
  unfold act Finsupp.sum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only
  rw [mul_assoc u g k, hf u hu, mul_left_comm]

theorem indicator_cell_mul_left {ψ : AddChar F ℂ} {n : ℕ} {z : GL (Fin n) F} {U : Set (GL (Fin n) F)}
    {f : GL (Fin n) F → ℂ} (hf : Eqv ψ f) {u : GL (Fin n) F} (hu : u ∈ unipB F (Fin n)) (g : GL (Fin n) F) :
    (cell z U).indicator f (u * g) = ψ (superDiag u) * (cell z U).indicator f g := by
  classical
  by_cases hg : g ∈ cell z U
  · rw [Set.indicator_of_mem hg, Set.indicator_of_mem ((mul_mem_cell_iff hu g).2 hg), hf u hu]
  · rw [Set.indicator_apply, Set.indicator_apply, if_neg hg, if_neg (fun h => hg ((mul_mem_cell_iff hu g).1 h)),
      mul_zero]

end Red

open Red

theorem cuts_mir_of_res : ∀ {F : Type} [NormedField F] [ProperSpace F] [IsUltrametricDist F] (ψ : AddChar F ℂ), IsLocallyConstant ψ → ψ ≠ 1 → ∀ m : ℕ, (∀ B : Subgroup (GL (Fin (m + 1)) F), IsCompact (B : Set (GL (Fin (m + 1)) F)) → IsOpen (B : Set (GL (Fin (m + 1)) F)) → ∀ L : Set (Fin (m + 1) → F), L ∈ nhds (0 : Fin (m + 1) → F) → ∀ h₀ : GL (Fin (m + 1)) F, ∃ T : GL (Fin (m + 2)) F →₀ ℂ, ∀ f : GL (Fin (m + 2)) F → ℂ, GlobalTheory.JSW.KirFin.Eqv ψ f → (∀ b ∈ B, ∀ g, f (g * GlobalTheory.JSW.KirFin.cor b) = f g) → (∀ y ∈ L, ∀ g, f (g * GlobalTheory.JSW.KirFin.mir 1 y) = f g) → ∀ h : GL (Fin (m + 1)) F, GlobalTheory.JSW.Cut.act T f (GlobalTheory.JSW.KirFin.cor h) = (GlobalTheory.JSW.Cut.cell h₀ (B : Set (GL (Fin (m + 1)) F))).indicator (fun h => f (GlobalTheory.JSW.KirFin.cor h)) h) → ∀ U : Subgroup (GL (Fin (m + 2)) F), IsCompact (U : Set (GL (Fin (m + 2)) F)) → IsOpen (U : Set (GL (Fin (m + 2)) F)) → ∀ z : GL (Fin (m + 2)) F, GlobalTheory.JSW.Cut.Cuts ψ (U : Set (GL (Fin (m + 2)) F)) (GlobalTheory.JSW.Cut.cell z (U : Set (GL (Fin (m + 2)) F))) {p | GlobalTheory.JSW.KirFin.lr p = GlobalTheory.JSW.KirFin.lr 1} := by
  intro F _ _ _ ψ _ _ m H U hUc hUo z
  classical
  by_cases hz : ∃ h₀ : GL (Fin (m + 1)) F, cor h₀ ∈ cell z (U : Set (GL (Fin (m + 2)) F))
  swap
  · refine ⟨0, fun f _ _ p hp => ?_⟩
    rw [act_zero, Set.indicator_apply, if_neg]
    intro hpc
    obtain ⟨h, x, rfl⟩ := exists_mir hp
    rw [mir_eq, mul_mem_cell_iff (mir_mem_iff.2 (one_mem _))] at hpc
    exact hz ⟨h, hpc⟩
  obtain ⟨h₀, hh₀⟩ := hz
  have hzc : cell z (U : Set (GL (Fin (m + 2)) F)) = cell (cor h₀) U := (Red.cell_eq_of_mem hh₀).symm
  obtain ⟨B, hBc, _, hUB, hcell⟩ := GlobalTheory.T.exists_blockGroup_unipotentDoubleCosetCell_blockDiag_iff U hUc hUo
  let B' : Subgroup (GL (Fin (m + 1)) F) := U.comap cor
  have hB'o : IsOpen (B' : Set (GL (Fin (m + 1)) F)) := hUo.preimage continuous_cor
  have hB'B : B' ≤ B := fun b hb => hUB b hb
  have hB'c : IsCompact (B' : Set (GL (Fin (m + 1)) F)) :=
    hBc.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ hB'o) hB'B
  let L : Set (Fin (m + 1) → F) := {y | mir 1 y ∈ U}
  have hL : L ∈ 𝓝 (0 : Fin (m + 1) → F) := by
    refine (hUo.preimage continuous_col).mem_nhds ?_
    show mir 1 0 ∈ U
    rw [mir_one]
    exact one_mem _
  obtain ⟨s, -, hsU, hsd⟩ := GlobalTheory.T.unipotentDoubleCosetCell_finite_disjoint_iUnion B B' hBc hB'o hB'B h₀
  choose T hT using fun x : GL (Fin (m + 1)) F => H B' hB'c hB'o L hL x
  refine ⟨∑ x ∈ s, T x, fun f hf hfU => ?_⟩
  have hB'f : ∀ b ∈ B', ∀ g, f (g * cor b) = f g := fun b hb g => hfU _ hb g
  have hLf : ∀ y ∈ L, ∀ g, f (g * mir 1 y) = f g := fun y hy g => hfU _ hy g
  have hcor : ∀ h, act (∑ x ∈ s, T x) f (cor h) = (cell z (U : Set (GL (Fin (m + 2)) F))).indicator f (cor h) := by
    intro h
    rw [act_finset_sum]
    rw [Finset.sum_congr rfl fun x _ => hT x f hf hB'f hLf h]
    rw [← Finset.indicator_biUnion_apply s _ hsd, ← hsU, hzc]
    by_cases hh : h ∈ cell h₀ (B : Set (GL (Fin (m + 1)) F))
    · rw [Set.indicator_of_mem hh, Set.indicator_of_mem ((hcell h₀ h).2 hh)]
    · rw [Set.indicator_apply, Set.indicator_apply, if_neg hh, if_neg fun h' => hh ((hcell h₀ h).1 h')]
  intro p hp
  obtain ⟨h, x, rfl⟩ := exists_mir hp
  have hu : mir 1 x ∈ unipB F (Fin (m + 2)) := mir_mem_iff.2 (one_mem _)
  rw [mir_eq]
  show act _ f (mir 1 x * cor h) = (cell z (U : Set (GL (Fin (m + 2)) F))).indicator f (mir 1 x * cor h)
  rw [act_mul_left _ hf hu, indicator_cell_mul_left hf hu, hcor]

end GlobalTheory.JSW.Cut
end
end

open Matrix Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mirabolic_cutoffs_of_restriction_cutoffs : ∀ {F : Type} [NormedField F] [ProperSpace F] [IsUltrametricDist F] (ψ : AddChar F ℂ), IsLocallyConstant ψ → ψ ≠ 1 → ∀ m : ℕ, (∀ B : Subgroup (GL (Fin (m + 1)) F), IsCompact (B : Set (GL (Fin (m + 1)) F)) → IsOpen (B : Set (GL (Fin (m + 1)) F)) → ∀ L : Set (Fin (m + 1) → F), L ∈ nhds (0 : Fin (m + 1) → F) → ∀ h₀ : GL (Fin (m + 1)) F, ∃ T : GL (Fin (m + 2)) F →₀ ℂ, ∀ f : GL (Fin (m + 2)) F → ℂ, GlobalTheory.JSW.KirFin.Eqv ψ f → (∀ b ∈ B, ∀ g, f (g * GlobalTheory.JSW.KirFin.cor b) = f g) → (∀ y ∈ L, ∀ g, f (g * GlobalTheory.JSW.KirFin.mir 1 y) = f g) → ∀ h : GL (Fin (m + 1)) F, GlobalTheory.JSW.Cut.act T f (GlobalTheory.JSW.KirFin.cor h) = (GlobalTheory.JSW.Cut.cell h₀ (B : Set (GL (Fin (m + 1)) F))).indicator (fun h => f (GlobalTheory.JSW.KirFin.cor h)) h) → ∀ U : Subgroup (GL (Fin (m + 2)) F), IsCompact (U : Set (GL (Fin (m + 2)) F)) → IsOpen (U : Set (GL (Fin (m + 2)) F)) → ∀ z : GL (Fin (m + 2)) F, GlobalTheory.JSW.Cut.Cuts ψ (U : Set (GL (Fin (m + 2)) F)) (GlobalTheory.JSW.Cut.cell z (U : Set (GL (Fin (m + 2)) F))) {p | GlobalTheory.JSW.KirFin.lr p = GlobalTheory.JSW.KirFin.lr 1} := by
  atlas_forward_decl GlobalTheory.JSW.Cut.cuts_mir_of_res
end

section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory

namespace GlobalTheory.JSW

theorem psiLoc_addChar_locallyConstant_ne_one :
    ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)), ∃ ψ : AddChar (w.adicCompletion E) ℂ,
      (∀ x, ψ x = GlobalTheory.JSW.psiLoc w x) ∧ IsLocallyConstant ψ ∧ ψ ≠ 1 := by
  intro E _ _ w
  refine ⟨psiLocChar w, fun x => rfl, ?_, ?_⟩
  · have hc : Continuous (psiLocChar w) := by
      have : (psiLocChar w : w.adicCompletion E → ℂ) = fun x => ((GroundTheory.Global.localAdelicChar E w x : Circle) : ℂ) := by
        funext x; exact GlobalTheory.JSW.WhitModel.psiLoc_eq w x
      rw [this]
      exact continuous_subtype_val.comp (GroundTheory.Global.continuous_localAdelicChar w)
    exact GlobalTheory.SchrSBFin.isLocallyConstant_addChar _ hc
  · intro h
    apply GroundTheory.Global.localAdelicChar_ne_one (K := E) (v := w)
    refine AddChar.ext _ _ fun x => ?_
    have h1 : psiLocChar w x = 1 := by rw [h]; rfl
    have h2 : ((GroundTheory.Global.localAdelicChar E w x : Circle) : ℂ) = 1 := by
      rw [← GlobalTheory.JSW.WhitModel.psiLoc_eq]; exact h1
    exact Subtype.ext h2

end GlobalTheory.JSW
end

section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finitePlace_standardChar_locallyConstant_nontrivial : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)), ∃ ψ : AddChar (w.adicCompletion E) ℂ, (∀ x, ψ x = GlobalTheory.JSW.psiLoc w x) ∧ IsLocallyConstant ψ ∧ ψ ≠ 1 := by
  first | exact @GlobalTheory.JSW.psiLoc_addChar_locallyConstant_ne_one | exact GlobalTheory.JSW.psiLoc_addChar_locallyConstant_ne_one | (intros; apply GlobalTheory.JSW.psiLoc_addChar_locallyConstant_ne_one <;> assumption)
end

section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory

noncomputable section

namespace GlobalTheory.JSW.MirPatch.Decomp

open GlobalTheory.JSW GlobalTheory.SmGL Topology

theorem exists_distinct {ι X : Type} [Finite ι] (C : ι → Set X)
    (hC : ∀ i j x, x ∈ C i → x ∈ C j → C i = C j) :
    ∃ (N : ℕ) (f : Fin N → ι), (∀ i j x, x ∈ C (f i) → x ∈ C (f j) → i = j) ∧
      ∀ x, (∃ i, x ∈ C i) ↔ ∃ j, x ∈ C (f j) := by
  obtain ⟨N, ⟨e⟩⟩ := Finite.exists_equiv_fin (Set.range C)
  have hf : ∀ j, C (e.symm j).2.choose = (e.symm j).1 := fun j => (e.symm j).2.choose_spec
  refine ⟨N, fun j => (e.symm j).2.choose, fun i j x hi hj => ?_, fun x => ⟨fun ⟨i, hi⟩ => ?_, fun ⟨j, hj⟩ => ⟨_, hj⟩⟩⟩
  · have h := hC _ _ x hi hj
    rw [hf, hf] at h
    exact e.symm.injective (Subtype.ext h)
  · refine ⟨e ⟨C i, i, rfl⟩, ?_⟩
    simp only
    rw [hf, Equiv.symm_apply_apply]
    exact hi

theorem exists_finite_reps {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {K A : Set G} (hK : IsCompact K) (hA : A ⊆ K) (V : Subgroup G) (hV : IsOpen (V : Set G)) :
    ∃ (ι : Type) (_ : Finite ι) (k : ι → G), (∀ i, k i ∈ A) ∧ ∀ a ∈ A, ∃ i, (k i)⁻¹ * a ∈ V := by
  obtain ⟨t, ht⟩ := compact_covered_by_mul_left_translates hK (V := (V : Set G))
    (by rw [hV.interior_eq]; exact ⟨1, V.one_mem⟩)
  let ι := {g : G // g ∈ t ∧ ∃ a ∈ A, g * a ∈ V}
  haveI : Finite ι := Finite.of_injective (fun x : ι => (⟨x.1, x.2.1⟩ : t))
    (fun x y h => Subtype.ext (congrArg (fun z : t => (z : G)) h))
  refine ⟨ι, inferInstance, fun x => x.2.2.choose, fun x => x.2.2.choose_spec.1, fun a ha => ?_⟩
  obtain ⟨g, hg, hga⟩ := Set.mem_iUnion₂.1 (ht (hA ha))
  have hga' : g * a ∈ V := hga
  refine ⟨⟨g, hg, a, ha, hga'⟩, ?_⟩
  have hb := (⟨g, hg, a, ha, hga'⟩ : ι).2.2.choose_spec.2
  have e : ((⟨g, hg, a, ha, hga'⟩ : ι).2.2.choose)⁻¹ * a =
      (g * (⟨g, hg, a, ha, hga'⟩ : ι).2.2.choose)⁻¹ * (g * a) := by group
  rw [e]
  exact mul_mem (inv_mem hb) hga'

theorem cell_eq_of_mem {F : Type} [NormedField F] {n : ℕ} {z g : GL (Fin n) F} {U : Subgroup (GL (Fin n) F)}
    (h : g ∈ Cut.cell z (U : Set (GL (Fin n) F))) :
    Cut.cell z (U : Set (GL (Fin n) F)) = Cut.cell g (U : Set (GL (Fin n) F)) := by
  obtain ⟨u, hu, k, hk, rfl⟩ := h
  ext x
  constructor
  · rintro ⟨u', hu', k', hk', rfl⟩
    exact ⟨u' * u⁻¹, mul_mem hu' (inv_mem hu), k⁻¹ * k', mul_mem (inv_mem hk) hk', by group⟩
  · rintro ⟨u', hu', k', hk', rfl⟩
    exact ⟨u' * u, mul_mem hu' hu, k * k', mul_mem hk hk', by group⟩

variable {E : Type} [Field E] [NumberField E]

theorem map_comp_eq {a : ℕ} (w : HeightOneSpectrum (𝓞 E)) (g : GA E a) :
    GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) g =
      GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) g) := rfl

theorem af_eq {x y : Af E} (h : ∀ w, pLoc E w x = pLoc E w y) : x = y := FiniteAdeleRing.ext _ h

open Classical in

theorem pLoc_list_prod {n : ℕ} (u : ∀ w : HeightOneSpectrum (𝓞 E), GL (Fin n) (w.adicCompletion E))
    (l : List (HeightOneSpectrum (𝓞 E))) (hl : l.Nodup) (v : HeightOneSpectrum (𝓞 E)) :
    GeneralLinearGroup.map (pLoc E v) (l.map fun w => locGL E n w (u w)).prod = if v ∈ l then u v else 1 := by
  classical
  induction l with
  | nil => simp
  | cons w l ih =>
    rw [List.map_cons, List.prod_cons, map_mul, ih (List.nodup_cons.1 hl).2]
    by_cases h : v = w
    · subst h
      rw [pLoc_locGL, if_neg (List.nodup_cons.1 hl).1, if_pos (by simp), mul_one]
    · rw [pLoc_locGL_of_ne h, one_mul]
      simp only [List.mem_cons, h, false_or]

theorem loc_mem_unipB {a : ℕ} {u : GA E a} (hu : u ∈ NA E a) (w : HeightOneSpectrum (𝓞 E)) :
    GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) u ∈ unipB (w.adicCompletion E) (Fin a) :=
  (GlobalTheory.SmGL.mem_unipB _).2 ⟨fun i j h => by
    show pLoc E w (pFin E _) = 0
    rw [hu.1 i j h, map_zero, map_zero], fun i => by
    show pLoc E w (pFin E _) = 1
    rw [hu.2 i, map_one, map_one]⟩

variable [IsTotallyComplex E]

theorem finGL_mem_NA {a : ℕ} {v : GL (Fin a) (Af E)}
    (hv : ∀ w, GeneralLinearGroup.map (pLoc E w) v ∈ unipB (w.adicCompletion E) (Fin a)) : finGL E a v ∈ NA E a := by
  have e1 : ∀ i j, pInf E ((finGL E a v : Matrix (Fin a) (Fin a) (Ad E)) i j) =
      ((1 : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E)) i j := fun i j =>
    congrArg (fun g : GL (Fin a) (Cinf E) => (g : Matrix (Fin a) (Fin a) (Cinf E)) i j) (pInf_finGL (E := E) v)
  have e2 : ∀ i j, pFin E ((finGL E a v : Matrix (Fin a) (Fin a) (Ad E)) i j) = (v : Matrix (Fin a) (Fin a) (Af E)) i j :=
    fun i j => congrArg (fun g : GL (Fin a) (Af E) => (g : Matrix (Fin a) (Fin a) (Af E)) i j) (pFin_finGL (E := E) v)
  refine ⟨fun i j h => ad_ext ?_ ?_, fun i => ad_ext ?_ ?_⟩
  · rw [e1, Units.val_one, Matrix.one_apply_ne (ne_of_gt h), map_zero]
  · rw [e2, map_zero]
    exact af_eq fun w => by rw [map_zero]; exact ((GlobalTheory.SmGL.mem_unipB _).1 (hv w)).1 i j h
  · rw [e1, Units.val_one, Matrix.one_apply_eq, map_one]
  · rw [e2, map_one]
    exact af_eq fun w => by rw [map_one]; exact ((GlobalTheory.SmGL.mem_unipB _).1 (hv w)).2 i

theorem mem_cell_iff {a : ℕ} (S : Finset (HeightOneSpectrum (𝓞 E))) (K : Subgroup (GL (Fin a) (Af E))) (q : GA E a)
    {p : GA E a} (hp : p ∈ supS E a S) :
    p ∈ cell K q ↔ ∃ k ∈ K,
      (∀ w ∉ S, GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) q * k) ∈
        unipB (w.adicCompletion E) (Fin a)) ∧
      ∀ w ∈ S, ∃ u ∈ unipB (w.adicCompletion E) (Fin a), GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) p =
        u * GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) q * k) := by
  constructor
  · rintro ⟨u, hu, k, hk, y, rfl⟩
    have hf : GeneralLinearGroup.map (pFin E) (u * q * finGL E a k * infGL E a y) =
        GeneralLinearGroup.map (pFin E) u * (GeneralLinearGroup.map (pFin E) q * k) := by
      rw [map_mul, map_mul, map_mul, pFin_finGL, pFin_infGL, mul_one, mul_assoc]
    refine ⟨k, hk, fun w hw => ?_, fun w _ => ⟨_, loc_mem_unipB hu w, ?_⟩⟩
    · have h1 := hp w hw
      rw [map_comp_eq, hf, map_mul] at h1
      rw [eq_inv_of_mul_eq_one_right h1]
      exact inv_mem (loc_mem_unipB hu w)
    · rw [map_comp_eq, hf, map_mul, map_comp_eq]
  · rintro ⟨k, hk, hout, hin⟩
    set v := GeneralLinearGroup.map (pFin E) p * (GeneralLinearGroup.map (pFin E) q * k)⁻¹ with hv
    have hvN : ∀ w, GeneralLinearGroup.map (pLoc E w) v ∈ unipB (w.adicCompletion E) (Fin a) := by
      intro w
      rw [hv, map_mul, map_inv]
      by_cases hw : w ∈ S
      · obtain ⟨u, hu, he⟩ := hin w hw
        rw [← map_comp_eq, he, mul_inv_cancel_right]
        exact hu
      · rw [← map_comp_eq, hp w hw, one_mul]
        exact inv_mem (hout w hw)
    refine ⟨finGL E a v, finGL_mem_NA hvN, k, hk,
      (GeneralLinearGroup.map (pInf E) q)⁻¹ * GeneralLinearGroup.map (pInf E) p, ga_ext ?_ ?_⟩
    · simp only [map_mul, pInf_finGL, pInf_infGL, one_mul, mul_one, mul_inv_cancel_left]
    · simp only [map_mul, pFin_finGL, pFin_infGL, mul_one, hv]
      group

end GlobalTheory.JSW.MirPatch.Decomp

namespace GlobalTheory.JSW.MirPatch

open GlobalTheory.JSW GlobalTheory.SmGL Decomp

theorem cell_decomp : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (K : Subgroup (GL (Fin (m + 1)) (Af E))), IsOpen (K : Set (GL (Fin (m + 1)) (Af E))) → IsCompact (K : Set (GL (Fin (m + 1)) (Af E))) → ∀ q : GA E (m + 1), ∃ (U : ∀ w : HeightOneSpectrum (𝓞 E), Subgroup (GL (Fin (m + 1)) (w.adicCompletion E))) (N : ℕ) (z : Fin N → ∀ w : HeightOneSpectrum (𝓞 E), GL (Fin (m + 1)) (w.adicCompletion E)), (∀ w ∈ S, IsCompact (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E))) ∧ IsOpen (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E))) ∧ ∀ u ∈ U w, locGL E (m + 1) w u ∈ K) ∧ (∀ p ∈ GlobalTheory.JSW.mirS E S m, ∀ i j : Fin N, (∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) p ∈ GlobalTheory.JSW.Cut.cell (z i w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))) → (∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) p ∈ GlobalTheory.JSW.Cut.cell (z j w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))) → i = j) ∧ ∀ p ∈ GlobalTheory.JSW.mirS E S m, (p ∈ GlobalTheory.JSW.MirPatch.cell K q ↔ ∃ i : Fin N, ∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) p ∈ GlobalTheory.JSW.Cut.cell (z i w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))) := by
  intro E _ _ _ m S K hKo hKc q
  classical
  choose U hUo hUc hUK using fun w => LocEx.exists_compact_open (a := m + 1) w K hKo
  set qf := GeneralLinearGroup.map (pFin E) q with hqf
  let A : Set (GL (Fin (m + 1)) (Af E)) := {k | k ∈ K ∧ ∀ w ∉ S,
    GeneralLinearGroup.map (pLoc E w) (qf * k) ∈ unipB (w.adicCompletion E) (Fin (m + 1))}
  let V : Subgroup (GL (Fin (m + 1)) (Af E)) :=
    { carrier := {v | ∀ w ∈ S, GeneralLinearGroup.map (pLoc E w) v ∈ U w}
      mul_mem' := fun ha hb w hw => by rw [map_mul]; exact mul_mem (ha w hw) (hb w hw)
      one_mem' := fun w _ => by rw [map_one]; exact one_mem _
      inv_mem' := fun ha w hw => by rw [map_inv]; exact inv_mem (ha w hw) }
  have hVo : IsOpen (V : Set (GL (Fin (m + 1)) (Af E))) := by
    have e : (V : Set (GL (Fin (m + 1)) (Af E))) =
        ⋂ w ∈ S, GeneralLinearGroup.map (pLoc E w) ⁻¹' (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E))) := by
      ext v; simp [V]
    rw [e]
    exact isOpen_biInter_finset fun w _ => (hUo w).preimage (LocEx.continuous_map_pLoc w)
  obtain ⟨ι, _, k, hkA, hcov⟩ := exists_finite_reps (A := A) hKc (fun x hx => hx.1) V hVo
  let C : ι → Set (∀ w : HeightOneSpectrum (𝓞 E), GL (Fin (m + 1)) (w.adicCompletion E)) := fun i =>
    {x | ∀ w ∈ S, x w ∈ Cut.cell (GeneralLinearGroup.map (pLoc E w) (qf * k i))
      (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))}
  have hC : ∀ i j x, x ∈ C i → x ∈ C j → C i = C j := by
    intro i j x hi hj
    ext y
    exact forall₂_congr fun w hw => by rw [cell_eq_of_mem (hi w hw), cell_eq_of_mem (hj w hw)]
  obtain ⟨N, f, huniq, hiff⟩ := exists_distinct C hC
  refine ⟨U, N, fun j w => GeneralLinearGroup.map (pLoc E w) (qf * k (f j)), fun w _ => ⟨hUc w, hUo w, hUK w⟩,
    fun p _ i j hi hj => huniq i j (fun w => GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) p) hi hj,
    fun p hp => ?_⟩
  rw [mem_cell_iff S K q hp.1]
  refine Iff.trans ?_ (hiff (fun w => GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) p))
  constructor
  · rintro ⟨k', hk', hout, hin⟩
    obtain ⟨i, hi⟩ := hcov k' ⟨hk', hout⟩
    refine ⟨i, fun w hw => ?_⟩
    obtain ⟨u, hu, he⟩ := hin w hw
    refine ⟨u, hu, GeneralLinearGroup.map (pLoc E w) ((k i)⁻¹ * k'), hi w hw, ?_⟩
    show GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) p = _
    rw [he, mul_assoc u, ← map_mul, mul_assoc, mul_inv_cancel_left]
  · rintro ⟨i, hi⟩
    choose! uu huu cc hcc heq using hi
    let g : GL (Fin (m + 1)) (Af E) := (S.toList.map fun w => locGL E (m + 1) w (cc w)).prod
    have hgK : g ∈ K := by
      refine Subgroup.list_prod_mem _ fun x hx => ?_
      obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hx
      exact hUK w _ (hcc w (Finset.mem_toList.1 hw))
    have hg : ∀ v, GeneralLinearGroup.map (pLoc E v) g = if v ∈ S then cc v else 1 := fun v => by
      rw [pLoc_list_prod cc _ S.nodup_toList v]
      simp only [Finset.mem_toList]
    refine ⟨k i * g, mul_mem (hkA i).1 hgK, fun w hw => ?_, fun w hw => ⟨uu w, huu w hw, ?_⟩⟩
    · rw [← mul_assoc, map_mul, hg w, if_neg hw, mul_one]
      exact (hkA i).2 w hw
    · refine (heq w hw).trans ?_
      rw [← mul_assoc qf, map_mul (GeneralLinearGroup.map (pLoc E w)) (qf * k i) g, hg w, if_pos hw, mul_assoc]

end GlobalTheory.JSW.MirPatch
end
end

section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mirabolic_cell_finite_union_local_double_cosets : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (K : Subgroup (GL (Fin (m + 1)) (Af E))), IsOpen (K : Set (GL (Fin (m + 1)) (Af E))) → IsCompact (K : Set (GL (Fin (m + 1)) (Af E))) → ∀ q : GA E (m + 1), ∃ (U : ∀ w : HeightOneSpectrum (𝓞 E), Subgroup (GL (Fin (m + 1)) (w.adicCompletion E))) (N : ℕ) (z : Fin N → ∀ w : HeightOneSpectrum (𝓞 E), GL (Fin (m + 1)) (w.adicCompletion E)), (∀ w ∈ S, IsCompact (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E))) ∧ IsOpen (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E))) ∧ ∀ u ∈ U w, locGL E (m + 1) w u ∈ K) ∧ (∀ p ∈ GlobalTheory.JSW.mirS E S m, ∀ i j : Fin N, (∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) p ∈ GlobalTheory.JSW.Cut.cell (z i w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))) → (∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) p ∈ GlobalTheory.JSW.Cut.cell (z j w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))) → i = j) ∧ ∀ p ∈ GlobalTheory.JSW.mirS E S m, (p ∈ GlobalTheory.JSW.MirPatch.cell K q ↔ ∃ i : Fin N, ∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) p ∈ GlobalTheory.JSW.Cut.cell (z i w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))) := by
  first | (exact @GlobalTheory.JSW.MirPatch.cell_decomp) | (exact GlobalTheory.JSW.MirPatch.cell_decomp) | (intros; apply GlobalTheory.JSW.MirPatch.cell_decomp  <;> assumption)
end

section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localCutOperator_transfer_adelicWhittaker : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (w : HeightOneSpectrum (𝓞 E)) (ψ : AddChar (w.adicCompletion E) ℂ), (∀ x, ψ x = GlobalTheory.JSW.psiLoc w x) → ∀ (K : Subgroup (GL (Fin (m + 1)) (Af E))) (U : Subgroup (GL (Fin (m + 1)) (w.adicCompletion E))), (∀ u ∈ U, locGL E (m + 1) w u ∈ K) → ∀ X A : Set (GL (Fin (m + 1)) (w.adicCompletion E)), GlobalTheory.JSW.Cut.Cuts ψ (U : Set (GL (Fin (m + 1)) (w.adicCompletion E))) X A → ∃ T : GA E (m + 1) →₀ ℂ, (∀ k ∈ T.support, ∃ g, k = finGL E (m + 1) (locGL E (m + 1) w g)) ∧ ∀ W : GA E (m + 1) → ℂ, (∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ g, W (u * g) = GlobalTheory.JSW.psiN u * W g) → (∀ u ∈ K, ∀ g, W (g * finGL E (m + 1) u) = W g) → ∀ y : GA E (m + 1), GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) y ∈ A → GlobalTheory.JSW.Cut.act T W y = {x : GA E (m + 1) | GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) x ∈ X}.indicator W y := by
  first | (exact @GlobalTheory.JSW.CutTransfer.transfer) | (exact GlobalTheory.JSW.CutTransfer.transfer) | (intros; apply GlobalTheory.JSW.CutTransfer.transfer  <;> assumption)
end

section
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory

namespace GlobalTheory.JSW.CutProd

open GlobalTheory.JSW.Cut

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {m : ℕ}

theorem lr_loc_of_mem_mirS {S : Finset (HeightOneSpectrum (𝓞 E))} {p : GA E (m + 1)} (hp : p ∈ GlobalTheory.JSW.mirS E S m)
    (w : HeightOneSpectrum (𝓞 E)) :
    GlobalTheory.JSW.KirFin.lr (GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) p) = GlobalTheory.JSW.KirFin.lr 1 := by
  funext j
  have h := hp.2 j
  simp only [GlobalTheory.JSW.KirFin.lr]
  show ((pLoc E w).comp (pFin E)) ((p : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) j) = _
  rw [h]
  split_ifs with hj <;> simp [hj, Matrix.one_apply, eq_comm]

theorem exists_cut_prod (ψ : ∀ w : HeightOneSpectrum (𝓞 E), AddChar (w.adicCompletion E) ℂ)
    (hψ : ∀ w x, ψ w x = GlobalTheory.JSW.psiLoc w x) (K : Subgroup (GL (Fin (m + 1)) (Af E)))
    (U : ∀ w : HeightOneSpectrum (𝓞 E), Subgroup (GL (Fin (m + 1)) (w.adicCompletion E)))
    (z : ∀ w : HeightOneSpectrum (𝓞 E), GL (Fin (m + 1)) (w.adicCompletion E)) (S : Finset (HeightOneSpectrum (𝓞 E))) :
    (∀ w ∈ S, ∀ u ∈ U w, locGL E (m + 1) w u ∈ K) →
    (∀ w ∈ S, Cuts (ψ w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))
      (cell (z w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))) {p | GlobalTheory.JSW.KirFin.lr p = GlobalTheory.JSW.KirFin.lr 1}) →
    ∃ T : GA E (m + 1) →₀ ℂ, (∀ h ∈ T.support, h ∈ GlobalTheory.JSW.supS E (m + 1) S ∧ GeneralLinearGroup.map (pInf E) h = 1) ∧
      ∀ W : GA E (m + 1) → ℂ, (∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ g, W (u * g) = GlobalTheory.JSW.psiN u * W g) →
        (∀ u ∈ K, ∀ g, W (g * finGL E (m + 1) u) = W g) →
        ∀ y : GA E (m + 1), (∀ w ∈ S, GlobalTheory.JSW.KirFin.lr (GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) y) =
          GlobalTheory.JSW.KirFin.lr 1) →
        GlobalTheory.JSW.Cut.act T W y = {x : GA E (m + 1) | ∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) x ∈
          cell (z w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))}.indicator W y := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro _ _
    refine ⟨Finsupp.single 1 1, fun h hh => ?_, fun W _ _ y _ => ?_⟩
    · have h1 : h = 1 := Finset.mem_singleton.1 (Finsupp.support_single_subset hh)
      subst h1
      exact ⟨fun v _ => map_one _, map_one _⟩
    · simp
  | insert w S hw ih =>
    intro hK hC
    obtain ⟨T₁, hT₁s, hT₁⟩ := ih (fun v hv => hK v (Finset.mem_insert_of_mem hv))
      (fun v hv => hC v (Finset.mem_insert_of_mem hv))
    obtain ⟨T₂, hT₂s, hT₂⟩ := GlobalTheory.T.localCutOperator_transfer_adelicWhittaker E m w (ψ w) (hψ w) K (U w) (hK w (Finset.mem_insert_self _ _))
      (cell (z w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))) {p | GlobalTheory.JSW.KirFin.lr p = GlobalTheory.JSW.KirFin.lr 1}
      (hC w (Finset.mem_insert_self _ _))
    refine ⟨comp T₁ T₂, fun k hk => ?_, fun W hN hKW y hy => ?_⟩
    · obtain ⟨a, ha, b, hb, rfl⟩ := mem_support_comp hk
      obtain ⟨g, rfl⟩ := hT₂s b hb
      have hb' := (GlobalTheory.JSW.WhitModel.loc_mem_supS (insert w S) w g).2 (Or.inl (Finset.mem_insert_self _ _))
      refine ⟨fun v hv => ?_, ?_⟩
      · rw [map_mul, (hT₁s a ha).1 v (fun h => hv (Finset.mem_insert_of_mem h)), hb' v hv, one_mul]
      · rw [map_mul, (hT₁s a ha).2, pInf_finGL, one_mul]
    · have hyh : ∀ h ∈ T₁.support, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) (y * h) =
          GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) y := fun h hh => by
        rw [map_mul, (hT₁s h hh).1 w hw, mul_one]
      have hyS := hT₁ W hN hKW y (fun v hv => hy v (Finset.mem_insert_of_mem hv))
      have hyw := hy w (Finset.mem_insert_self _ _)
      rw [act_comp]
      by_cases hyc : GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) y ∈
          cell (z w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))
      · rw [act_congr T₁ (f' := W) fun k hk => ?_, hyS]
        · simp only [Set.indicator, Set.mem_setOf_eq, Finset.forall_mem_insert, hyc, true_and]
        · rw [hT₂ W hN hKW (y * k) (by rw [hyh k hk]; exact hyw), Set.indicator_of_mem]
          rw [Set.mem_setOf_eq, hyh k hk]; exact hyc
      · rw [act_congr T₁ (f' := 0) fun k hk => ?_]
        · simp only [Set.indicator, Set.mem_setOf_eq, Finset.forall_mem_insert, hyc, false_and, if_false]
          unfold GlobalTheory.JSW.Cut.act; simp
        · rw [hT₂ W hN hKW (y * k) (by rw [hyh k hk]; exact hyw), Set.indicator_of_notMem]
          · rfl
          · rw [Set.mem_setOf_eq, hyh k hk]; exact hyc

end GlobalTheory.JSW.CutProd

theorem _root_.GlobalTheory.JSW.CutProd.cut_prod_mirS : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (ψ : ∀ w : HeightOneSpectrum (𝓞 E), AddChar (w.adicCompletion E) ℂ), (∀ w x, ψ w x = GlobalTheory.JSW.psiLoc w x) → ∀ (K : Subgroup (GL (Fin (m + 1)) (Af E))) (U : ∀ w : HeightOneSpectrum (𝓞 E), Subgroup (GL (Fin (m + 1)) (w.adicCompletion E))) (z : ∀ w : HeightOneSpectrum (𝓞 E), GL (Fin (m + 1)) (w.adicCompletion E)), (∀ w ∈ S, ∀ u ∈ U w, locGL E (m + 1) w u ∈ K) → (∀ w ∈ S, GlobalTheory.JSW.Cut.Cuts (ψ w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E))) (GlobalTheory.JSW.Cut.cell (z w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))) {p | GlobalTheory.JSW.KirFin.lr p = GlobalTheory.JSW.KirFin.lr 1}) → ∃ T : GA E (m + 1) →₀ ℂ, (∀ h ∈ T.support, h ∈ GlobalTheory.JSW.supS E (m + 1) S ∧ GeneralLinearGroup.map (pInf E) h = 1) ∧ ∀ W : GA E (m + 1) → ℂ, (∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ g, W (u * g) = GlobalTheory.JSW.psiN u * W g) → (∀ u ∈ K, ∀ g, W (g * finGL E (m + 1) u) = W g) → ∀ p ∈ GlobalTheory.JSW.mirS E S m, GlobalTheory.JSW.Cut.act T W p = {x : GA E (m + 1) | ∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) x ∈ GlobalTheory.JSW.Cut.cell (z w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))}.indicator W p := by
  intro E _ _ _ m S ψ hψ K U z hK hC
  obtain ⟨T, hTs, hT⟩ := GlobalTheory.JSW.CutProd.exists_cut_prod ψ hψ K U z S hK hC
  exact ⟨T, hTs, fun W hN hKW p hp => hT W hN hKW p fun w _ => GlobalTheory.JSW.CutProd.lr_loc_of_mem_mirS hp w⟩
end

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.composite_cut_operators_product_local_cells_mirabolic : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (ψ : ∀ w : HeightOneSpectrum (𝓞 E), AddChar (w.adicCompletion E) ℂ), (∀ w x, ψ w x = GlobalTheory.JSW.psiLoc w x) → ∀ (K : Subgroup (GL (Fin (m + 1)) (Af E))) (U : ∀ w : HeightOneSpectrum (𝓞 E), Subgroup (GL (Fin (m + 1)) (w.adicCompletion E))) (z : ∀ w : HeightOneSpectrum (𝓞 E), GL (Fin (m + 1)) (w.adicCompletion E)), (∀ w ∈ S, ∀ u ∈ U w, locGL E (m + 1) w u ∈ K) → (∀ w ∈ S, GlobalTheory.JSW.Cut.Cuts (ψ w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E))) (GlobalTheory.JSW.Cut.cell (z w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))) {p | GlobalTheory.JSW.KirFin.lr p = GlobalTheory.JSW.KirFin.lr 1}) → ∃ T : GA E (m + 1) →₀ ℂ, (∀ h ∈ T.support, h ∈ GlobalTheory.JSW.supS E (m + 1) S ∧ GeneralLinearGroup.map (pInf E) h = 1) ∧ ∀ W : GA E (m + 1) → ℂ, (∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ g, W (u * g) = GlobalTheory.JSW.psiN u * W g) → (∀ u ∈ K, ∀ g, W (g * finGL E (m + 1) u) = W g) → ∀ p ∈ GlobalTheory.JSW.mirS E S m, GlobalTheory.JSW.Cut.act T W p = {x : GA E (m + 1) | ∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) x ∈ GlobalTheory.JSW.Cut.cell (z w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))}.indicator W p := by
  atlas_forward_decl GlobalTheory.JSW.CutProd.cut_prod_mirS
end

section
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory

namespace GlobalTheory.JSW.Cut

open GlobalTheory.JSW.KirFin GlobalTheory.SmGL

theorem cuts_mir {F : Type} [NormedField F] [ProperSpace F] [IsUltrametricDist F] (ψ : AddChar F ℂ)
    (hψ : IsLocallyConstant ψ) (hψ1 : ψ ≠ 1) (m : ℕ) (U : Subgroup (GL (Fin (m + 1)) F))
    (hUc : IsCompact (U : Set (GL (Fin (m + 1)) F))) (hUo : IsOpen (U : Set (GL (Fin (m + 1)) F)))
    (z : GL (Fin (m + 1)) F) : Cuts ψ (U : Set (GL (Fin (m + 1)) F)) (cell z (U : Set (GL (Fin (m + 1)) F)))
      {p | lr p = lr 1} := by
  induction m with
  | zero =>
    classical
    have h1 : ∀ q : GL (Fin (0 + 1)) F, lr q = lr 1 → q = 1 := fun q hq => by
      obtain ⟨h, x, rfl⟩ := exists_mir hq
      rw [Subsingleton.elim h 1, Subsingleton.elim x 0, mir_one]
    refine ⟨Finsupp.single 1 (if (1 : GL (Fin (0 + 1)) F) ∈ cell z (U : Set (GL (Fin (0 + 1)) F)) then 1 else 0),
      fun f _ _ g hg => ?_⟩
    rw [h1 g hg, act_single, mul_one]
    by_cases h : (1 : GL (Fin (0 + 1)) F) ∈ cell z (U : Set (GL (Fin (0 + 1)) F))
    · rw [if_pos h, one_mul, Set.indicator_of_mem h]
    · rw [if_neg h, zero_mul, Set.indicator_of_notMem h]
  | succ m ih =>
    refine GlobalTheory.T.mirabolic_cutoffs_of_restriction_cutoffs ψ hψ hψ1 m (GlobalTheory.T.exists_whittakerCut_inductionStep_of_open_subgroup ψ hψ hψ1 m (fun V hVc hVo z' => ?_)) U hUc hUo z
    refine GlobalTheory.T.whittakerIndicatorCut_mul_open_subgroup ψ V hVo _ _ (fun x hx u hu => ?_) (ih V hVc hVo z')
    obtain ⟨n, hn, k, hk, rfl⟩ := hx
    exact ⟨n, hn, k * u, V.mul_mem hk hu, by rw [mul_assoc]⟩

end GlobalTheory.JSW.Cut

open GlobalTheory.JSW.Cut in

theorem GlobalTheory.JSW.MirPatch.cut_operators : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (K : Subgroup (GL (Fin (m + 1)) (Af E))), IsOpen (K : Set (GL (Fin (m + 1)) (Af E))) → IsCompact (K : Set (GL (Fin (m + 1)) (Af E))) → ∀ q : GA E (m + 1), ∃ (n : ℕ) (h : Fin n → GA E (m + 1)) (c : Fin n → ℂ), (∀ i, h i ∈ GlobalTheory.JSW.supS E (m + 1) S) ∧ ∀ W : GA E (m + 1) → ℂ, (∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ g, W (u * g) = GlobalTheory.JSW.psiN u * W g) → (∀ u ∈ K, ∀ g, W (g * finGL E (m + 1) u) = W g) → ∀ p ∈ GlobalTheory.JSW.mirS E S m, ∑ i, c i * W (p * h i) = (GlobalTheory.JSW.MirPatch.cell K q).indicator W p := by
  intro E _ _ _ m S K hKo hKc q
  classical
  obtain ⟨U, N, z, hU, hdisj, hchar⟩ := GlobalTheory.T.mirabolic_cell_finite_union_local_double_cosets E m S K hKo hKc q
  choose ψ hψv hψl hψ1 using GlobalTheory.T.finitePlace_standardChar_locallyConstant_nontrivial E
  have hcut : ∀ i : Fin N, ∃ T : GA E (m + 1) →₀ ℂ, (∀ h ∈ T.support, h ∈ GlobalTheory.JSW.supS E (m + 1) S ∧
      GeneralLinearGroup.map (pInf E) h = 1) ∧ ∀ W : GA E (m + 1) → ℂ,
      (∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ g, W (u * g) = GlobalTheory.JSW.psiN u * W g) →
      (∀ u ∈ K, ∀ g, W (g * finGL E (m + 1) u) = W g) → ∀ p ∈ GlobalTheory.JSW.mirS E S m,
      act T W p = {x : GA E (m + 1) | ∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) x ∈
        GlobalTheory.JSW.Cut.cell (z i w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))}.indicator W p := by
    intro i
    refine GlobalTheory.T.composite_cut_operators_product_local_cells_mirabolic E m S ψ hψv K U (z i) (fun w hw => (hU w hw).2.2) fun w hw => ?_
    haveI := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion E w
    haveI : IsUltrametricDist (w.adicCompletion E) :=
      inferInstanceAs (@IsUltrametricDist (w.adicCompletion E)
        (Valued.toNormedField (w.adicCompletion E) (WithZero (Multiplicative ℤ))).toDist)
    exact cuts_mir (ψ w) (hψl w) (hψ1 w) m (U w) (hU w hw).1 (hU w hw).2.1 (z i w)
  choose T hTs hT using hcut
  obtain ⟨n, h, c, hh, he⟩ := exists_fin (∑ i, T i)
  refine ⟨n, h, c, fun j => ?_, fun W hW hWK p hp => ?_⟩
  · obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 (Finsupp.support_finset_sum (hh j))
    exact (hTs i _ hi).1
  · rw [← he, act_finset_sum]
    simp_rw [fun i => hT i W hW hWK p hp]
    by_cases hc : p ∈ GlobalTheory.JSW.MirPatch.cell K q
    · obtain ⟨i, hi⟩ := (hchar p hp).1 hc
      rw [Set.indicator_of_mem hc, Finset.sum_eq_single i]
      · exact Set.indicator_of_mem (s := {x : GA E (m + 1) | _}) hi _
      · intro j _ hj
        exact Set.indicator_of_notMem (s := {x : GA E (m + 1) | _}) (fun hj' => hj (hdisj p hp j i hj' hi)) _
      · simp
    · rw [Set.indicator_of_notMem hc]
      refine Finset.sum_eq_zero fun i _ => Set.indicator_of_notMem (s := {x : GA E (m + 1) | _}) (fun hi => hc ((hchar p hp).2 ⟨i, hi⟩)) _
end
end

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cutOperators_mirabolic_finitePlaces : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (K : Subgroup (GL (Fin (m + 1)) (Af E))), IsOpen (K : Set (GL (Fin (m + 1)) (Af E))) → IsCompact (K : Set (GL (Fin (m + 1)) (Af E))) → ∀ q : GA E (m + 1), ∃ (n : ℕ) (h : Fin n → GA E (m + 1)) (c : Fin n → ℂ), (∀ i, h i ∈ GlobalTheory.JSW.supS E (m + 1) S) ∧ ∀ W : GA E (m + 1) → ℂ, (∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ g, W (u * g) = GlobalTheory.JSW.psiN u * W g) → (∀ u ∈ K, ∀ g, W (g * finGL E (m + 1) u) = W g) → ∀ p ∈ GlobalTheory.JSW.mirS E S m, ∑ i, c i * W (p * h i) = (GlobalTheory.JSW.MirPatch.cell K q).indicator W p := by
  atlas_forward_decl GlobalTheory.JSW.MirPatch.cut_operators
end
