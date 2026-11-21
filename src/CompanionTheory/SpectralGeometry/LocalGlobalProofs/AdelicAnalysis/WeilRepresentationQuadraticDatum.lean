import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.StandardAdelicCharacter
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicHaarMeasureLinearChange
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicHaarMeasureScaling
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
import BuildAid.ForwardExisting
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensHI

section
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.CofinalDual

theorem card_le_of_pairing {A B : Type} [AddCommGroup A] [AddCommGroup B] [Finite A] [Finite B]
    (b : A → B → ℂ) (hn : ∀ x y, ‖b x y‖ = 1)
    (hl : ∀ x x' y, b (x + x') y = b x y * b x' y)
    (hr : ∀ x y y', b x (y + y') = b x y * b x y')
    (hk : ∀ x, (∀ y, b x y = 1) → x = 0) : Nat.card A ≤ Nat.card B := by
  classical
  haveI := Fintype.ofFinite B
  have hne : ∀ x y, b x y ≠ 0 := fun x y h => by
    have := hn x y
    simp [h] at this
  have h0 : ∀ x, b x 0 = 1 := fun x => by
    have := hr x 0 0
    rw [add_zero] at this
    exact (mul_eq_left₀ (hne x 0)).1 this.symm
  let f : A → AddChar B ℂ := fun x =>
    { toFun := b x, map_zero_eq_one' := h0 x, map_add_eq_mul' := hr x }
  have hf : Function.Injective f := by
    intro x x' h
    have e : ∀ y, b x y = b x' y := fun y => congrArg (fun ψ : AddChar B ℂ => ψ y) h
    have : x - x' = 0 := hk _ fun y => by
      have h1 := hl (x - x') x' y
      rw [sub_add_cancel, e y] at h1
      exact (mul_eq_right₀ (hne x' y)).1 h1.symm
    exact sub_eq_zero.1 this
  have e : Nat.card (AddChar B ℂ) = Nat.card B := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, AddChar.card_eq]
  exact e ▸ Nat.card_le_card_of_injective f hf

theorem index_eq_of_pairing {X Y : Type} [AddCommGroup X] [AddCommGroup Y] (c : X → Y → ℂ)
    (hn : ∀ x y, ‖c x y‖ = 1)
    (hl : ∀ x x' y, c (x + x') y = c x y * c x' y)
    (hr : ∀ x y y', c x (y + y') = c x y * c x y')
    (N : AddSubgroup X) (M : AddSubgroup Y)
    (hN : ∀ x, x ∈ N ↔ ∀ y, c x y = 1) (hM : ∀ y, y ∈ M ↔ ∀ x, c x y = 1)
    [N.FiniteIndex] [M.FiniteIndex] : N.index = M.index := by
  have hx : ∀ (x x' : X) (y : Y), (x : X ⧸ N) = x' → c x y = c x' y := by
    intro x x' y h
    have hm : -x + x' ∈ N := QuotientAddGroup.eq.1 h
    have := hl x (-x + x') y
    rw [add_neg_cancel_left, (hN _).1 hm y, mul_one] at this
    exact this.symm
  have hy : ∀ (x : X) (y y' : Y), (y : Y ⧸ M) = y' → c x y = c x y' := by
    intro x y y' h
    have hm : -y + y' ∈ M := QuotientAddGroup.eq.1 h
    have := hr x y (-y + y')
    rw [add_neg_cancel_left, (hM _).1 hm x, mul_one] at this
    exact this.symm
  let b : X ⧸ N → Y ⧸ M → ℂ := fun p q => c (Quotient.out p) (Quotient.out q)
  have hb : ∀ (x : X) (y : Y), b (x : X ⧸ N) (y : Y ⧸ M) = c x y := fun x y => by
    change c (Quotient.out (x : X ⧸ N)) (Quotient.out (y : Y ⧸ M)) = c x y
    rw [hx _ x _ (QuotientAddGroup.out_eq' _), hy _ _ y (QuotientAddGroup.out_eq' _)]
  have bn : ∀ p q, ‖b p q‖ = 1 := fun p q => hn _ _
  have bl : ∀ p p' q, b (p + p') q = b p q * b p' q := by
    intro p p' q
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective p
    obtain ⟨x', rfl⟩ := QuotientAddGroup.mk_surjective p'
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective q
    rw [← QuotientAddGroup.mk_add, hb, hb, hb, hl]
  have br : ∀ p q q', b p (q + q') = b p q * b p q' := by
    intro p q q'
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective p
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective q
    obtain ⟨y', rfl⟩ := QuotientAddGroup.mk_surjective q'
    rw [← QuotientAddGroup.mk_add, hb, hb, hb, hr]
  have k1 : ∀ p, (∀ q, b p q = 1) → p = 0 := by
    intro p h
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective p
    exact (QuotientAddGroup.eq_zero_iff x).2 ((hN x).2 fun y => by rw [← hb, h])
  have k2 : ∀ q, (∀ p, b p q = 1) → q = 0 := by
    intro q h
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective q
    exact (QuotientAddGroup.eq_zero_iff y).2 ((hM y).2 fun x => by rw [← hb, h])
  exact le_antisymm (card_le_of_pairing b bn bl br k1)
    (card_le_of_pairing (fun q p => b p q) (fun q p => bn p q) (fun q q' p => br p q q')
      (fun q p p' => bl p p' q) k2)

theorem relIndex_ne_zero_of_isOpen {V : Type} [AddCommGroup V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] (S T : AddSubgroup V) (hS : IsOpen (S : Set V))
    (hT : IsCompact (T : Set V)) : S.relIndex T ≠ 0 := by
  haveI : CompactSpace T := isCompact_iff_compactSpace.1 hT
  have ho : IsOpen ((S.addSubgroupOf T : AddSubgroup T) : Set T) :=
    hS.preimage continuous_subtype_val
  haveI := AddSubgroup.quotient_finite_of_isOpen _ ho
  have : (S.addSubgroupOf T).FiniteIndex := AddSubgroup.finiteIndex_of_finite_quotient
  exact this.index_ne_zero

theorem measure_eq_relIndex_mul {V : Type} [AddCommGroup V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V)
    [μ.IsAddLeftInvariant] (S T : AddSubgroup V) (hST : S ≤ T) (hS : IsOpen (S : Set V))
    (hf : S.relIndex T ≠ 0) : μ T = S.relIndex T * μ S := by
  classical
  haveI : (S.addSubgroupOf T).FiniteIndex := ⟨hf⟩
  haveI := Fintype.ofFinite (T ⧸ S.addSubgroupOf T)
  let o : T ⧸ S.addSubgroupOf T → T := fun q => Quotient.out q
  have ho : ∀ q, ((o q : T) : T ⧸ S.addSubgroupOf T) = q := fun q => QuotientAddGroup.out_eq' q
  let C : T ⧸ S.addSubgroupOf T → Set V := fun q => (fun v => (-(o q : V)) + v) ⁻¹' (S : Set V)
  have hU : (T : Set V) = ⋃ q, C q := by
    ext v
    simp only [Set.mem_iUnion, SetLike.mem_coe]
    constructor
    · intro hv
      refine ⟨((⟨v, hv⟩ : T) : T ⧸ S.addSubgroupOf T), ?_⟩
      have h := QuotientAddGroup.eq.1 (ho ((⟨v, hv⟩ : T) : T ⧸ S.addSubgroupOf T))
      exact AddSubgroup.mem_addSubgroupOf.1 h
    · rintro ⟨q, hq⟩
      have h1 : -(o q : V) + v ∈ T := hST hq
      have := T.add_mem (o q).2 h1
      simpa using this
  have hd : Pairwise (Function.onFun Disjoint C) := by
    intro q q' hne
    refine Set.disjoint_left.2 fun v hv hv' => hne ?_
    have h1 : -(o q : V) + v ∈ S := hv
    have h2 : -(o q' : V) + v ∈ S := hv'
    have h3 : -(o q : V) + (o q' : V) ∈ S := by
      have := S.sub_mem h1 h2
      have e : -(o q : V) + v - (-(o q' : V) + v) = -(o q : V) + (o q' : V) := by abel
      rwa [e] at this
    have h4 : ((o q : T) : T ⧸ S.addSubgroupOf T) = (o q' : T) :=
      QuotientAddGroup.eq.2 (AddSubgroup.mem_addSubgroupOf.2 (by simpa using h3))
    rw [ho, ho] at h4
    exact h4
  have hm : ∀ q, MeasurableSet (C q) := fun q =>
    (hS.preimage (continuous_const.add continuous_id)).measurableSet
  have hc : ∀ q, μ (C q) = μ S := fun q => measure_preimage_add μ _ _
  rw [hU, measure_iUnion hd hm, tsum_fintype]
  simp only [hc, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  congr 2
  rw [AddSubgroup.relIndex, AddSubgroup.index, Nat.card_eq_fintype_card]

def perpSub {V : Type} [AddCommGroup V] (χ : V → V → ℂ) (hs : ∀ x y, χ x y = χ y x)
    (hn : ∀ x y, ‖χ x y‖ = 1) (ha : ∀ x x' y, χ (x + x') y = χ x y * χ x' y)
    (L : AddSubgroup V) : AddSubgroup V where
  carrier := perp χ L
  add_mem' := by
    intro y y' hy hy' x hx
    rw [hs, ha, hs y, hs y', hy x hx, hy' x hx, one_mul]
  zero_mem' := by
    intro x _
    have hne : χ 0 x ≠ 0 := fun h => by
      have := hn 0 x
      simp [h] at this
    have := ha 0 0 x
    rw [add_zero] at this
    rw [hs]
    exact (mul_eq_left₀ hne).1 this.symm
  neg_mem' := by
    intro y hy x hx
    have hne : χ 0 x ≠ 0 := fun h => by
      have := hn 0 x
      simp [h] at this
    have h0 : χ 0 x = 1 := by
      have := ha 0 0 x
      rw [add_zero] at this
      exact (mul_eq_left₀ hne).1 this.symm
    have := ha y (-y) x
    rw [add_neg_cancel, h0, hs y x, hy x hx, one_mul] at this
    rw [hs]
    exact this.symm

theorem relIndex_eq_of_pairing {V : Type} [AddCommGroup V] (χ : V → V → ℂ)
    (hs : ∀ x y, χ x y = χ y x) (hn : ∀ x y, ‖χ x y‖ = 1)
    (ha : ∀ x x' y, χ (x + x') y = χ x y * χ x' y) (X₀ X Y₀ Y : AddSubgroup V)
    (hX : ∀ x ∈ X, (x ∈ X₀ ↔ ∀ y ∈ Y, χ x y = 1))
    (hY : ∀ y ∈ Y, (y ∈ Y₀ ↔ ∀ x ∈ X, χ x y = 1))
    (fX : X₀.relIndex X ≠ 0) (fY : Y₀.relIndex Y ≠ 0) : X₀.relIndex X = Y₀.relIndex Y := by
  haveI : (X₀.addSubgroupOf X).FiniteIndex := ⟨fX⟩
  haveI : (Y₀.addSubgroupOf Y).FiniteIndex := ⟨fY⟩
  refine index_eq_of_pairing (fun (x : X) (y : Y) => χ x y) (fun x y => hn _ _)
    (fun x x' y => ha _ _ _)
    (fun x y y' => by
      change χ x ((y : V) + y') = _
      rw [hs, ha, hs y, hs y']) _ _ ?_ ?_
  · intro x
    rw [AddSubgroup.mem_addSubgroupOf, hX x x.2]
    exact ⟨fun h y => h y y.2, fun h y hy => h ⟨y, hy⟩⟩
  · intro y
    rw [AddSubgroup.mem_addSubgroupOf, hY y y.2]
    exact ⟨fun h x => h x x.2, fun h x hx => h ⟨x, hx⟩⟩

theorem selfDual_of_between : ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [MeasurableSpace V] [BorelSpace V] (χ : V → V → ℂ) (μ : Measure V), μ.IsAddHaarMeasure → (∀ x y, χ x y = χ y x) → (∀ x y, ‖χ x y‖ = 1) → (∀ x x' y, χ (x + x') y = χ x y * χ x' y) → ∀ L₁ L L₂ : AddSubgroup V, L₁ ≤ L → L ≤ L₂ → IsOpen (L₁ : Set V) → IsCompact (L₂ : Set V) → IsCompact (perp χ L₁) → IsOpen (perp χ L₂) → perp χ (perp χ L₁) ⊆ L₁ → perp χ (perp χ L₂) ⊆ L₂ → μ L₁ * μ (perp χ L₁) = 1 → μ L₂ * μ (perp χ L₂) = 1 → IsCompact (perp χ L) ∧ IsOpen (perp χ L) ∧ perp χ (perp χ L) ⊆ L ∧ μ L * μ (perp χ L) = 1 := by
  intro V _ _ _ _ _ χ μ hμ hs hn ha L₁ L L₂ h1 h2 oL₁ cL₂ cP₁ oP₂ dd₁ dd₂ _ m₂
  let Q : AddSubgroup V → AddSubgroup V := perpSub χ hs hn ha
  have hQ : ∀ (A : AddSubgroup V) (y : V), y ∈ Q A ↔ ∀ x ∈ A, χ x y = 1 := fun _ _ => Iff.rfl
  have hQc : ∀ A : AddSubgroup V, (Q A : Set V) = perp χ A := fun _ => rfl
  have anti : ∀ A B : AddSubgroup V, A ≤ B → Q B ≤ Q A :=
    fun A B h y hy x hx => hy x (h hx)
  have hself : ∀ A : AddSubgroup V, A ≤ Q (Q A) := fun A x hx y hy => by
    rw [hs]
    exact hy x hx
  have placeRankTwoOne : Q L₂ ≤ Q L₁ := anti _ _ (h1.trans h2)
  have P2 : Q L₂ ≤ Q L := anti _ _ h2
  have P1 : Q L ≤ Q L₁ := anti _ _ h1
  have LM : L ≤ Q (Q L) := hself L
  have ML : Q (Q L) ≤ L₂ := fun z hz => dd₂ (anti _ _ P2 hz)
  have n0 : L₁.relIndex L₂ ≠ 0 := relIndex_ne_zero_of_isOpen _ _ oL₁ cL₂
  have p0 : (Q L₂).relIndex (Q L₁) ≠ 0 := relIndex_ne_zero_of_isOpen _ _ oP₂ cP₁
  have ea := AddSubgroup.relIndex_mul_relIndex L₁ L L₂ h1 h2
  have ep := AddSubgroup.relIndex_mul_relIndex (Q L₂) (Q L) (Q L₁) P2 P1
  have ek := AddSubgroup.relIndex_mul_relIndex L (Q (Q L)) L₂ LM ML
  have a0 : L₁.relIndex L ≠ 0 := fun h => n0 (by rw [← ea, h, zero_mul])
  have a'0 : L.relIndex L₂ ≠ 0 := fun h => n0 (by rw [← ea, h, mul_zero])
  have q0 : (Q L₂).relIndex (Q L) ≠ 0 := fun h => p0 (by rw [← ep, h, zero_mul])
  have q'0 : (Q L).relIndex (Q L₁) ≠ 0 := fun h => p0 (by rw [← ep, h, mul_zero])
  have m0 : (Q (Q L)).relIndex L₂ ≠ 0 := fun h => a'0 (by rw [← ek, h, mul_zero])
  have kerL₁ : ∀ x, x ∈ L₁ ↔ ∀ y ∈ Q L₁, χ x y = 1 := fun x =>
    ⟨fun hx y hy => hy x hx, fun h => dd₁ fun y hy => by
      rw [hs]
      exact h y hy⟩
  have e1 : L₁.relIndex L = (Q L).relIndex (Q L₁) :=
    relIndex_eq_of_pairing χ hs hn ha L₁ L (Q L) (Q L₁) (fun x _ => kerL₁ x)
      (fun y _ => hQ L y) a0 q'0
  have e2 : (Q (Q L)).relIndex L₂ = (Q L₂).relIndex (Q L) :=
    relIndex_eq_of_pairing χ hs hn ha (Q (Q L)) L₂ (Q L₂) (Q L)
      (fun x _ => by
        rw [hQ]
        exact forall₂_congr fun y _ => by rw [hs])
      (fun y _ => hQ L₂ y) m0 q0
  have e3 : L₁.relIndex L₂ = (Q L₂).relIndex (Q L₁) :=
    relIndex_eq_of_pairing χ hs hn ha L₁ L₂ (Q L₂) (Q L₁) (fun x _ => kerL₁ x)
      (fun y _ => hQ L₂ y) n0 p0
  have e4 : L.relIndex L₂ = (Q L₂).relIndex (Q L) := by
    have : L₁.relIndex L * L.relIndex L₂ = L₁.relIndex L * (Q L₂).relIndex (Q L) := by
      rw [ea, e3, ← ep, e1, mul_comm]
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero a0) this
  have hk : L.relIndex (Q (Q L)) = 1 := by
    have : L.relIndex (Q (Q L)) * (Q (Q L)).relIndex L₂ = 1 * (Q (Q L)).relIndex L₂ := by
      rw [ek, one_mul, e2, e4]
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero m0) this
  have MLe : Q (Q L) ≤ L := AddSubgroup.relIndex_eq_one.1 hk
  have oP : IsOpen (Q L : Set V) := AddSubgroup.isOpen_mono P2 oP₂
  refine ⟨?_, oP, MLe, ?_⟩
  · exact cP₁.of_isClosed_subset (AddSubgroup.isClosed_of_isOpen _ oP) P1
  · change μ L * μ (Q L) = 1
    change μ L₂ * μ (Q L₂) = 1 at m₂
    rw [measure_eq_relIndex_mul μ L₁ L h1 oL₁ a0, measure_eq_relIndex_mul μ (Q L₂) (Q L) P2 oP₂ q0,
      ← m₂, measure_eq_relIndex_mul μ L₁ L₂ (h1.trans h2) oL₁ n0, ← ea, e4]
    push_cast
    ring

end GlobalTheory.CompanionTheory.SW.CofinalDual
end
end

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.annihilator_of_annihilator_le : ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [MeasurableSpace V] [BorelSpace V] (χ : V → V → ℂ) (μ : Measure V), μ.IsAddHaarMeasure → (∀ x y, χ x y = χ y x) → (∀ x y, ‖χ x y‖ = 1) → (∀ x x' y, χ (x + x') y = χ x y * χ x' y) → ∀ L₁ L L₂ : AddSubgroup V, L₁ ≤ L → L ≤ L₂ → IsOpen (L₁ : Set V) → IsCompact (L₂ : Set V) → IsCompact (perp χ L₁) → IsOpen (perp χ L₂) → perp χ (perp χ L₁) ⊆ L₁ → perp χ (perp χ L₂) ⊆ L₂ → μ L₁ * μ (perp χ L₁) = 1 → μ L₂ * μ (perp χ L₂) = 1 → IsCompact (perp χ L) ∧ IsOpen (perp χ L) ∧ perp χ (perp χ L) ⊆ L ∧ μ L * μ (perp χ L) = 1 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SW.CofinalDual.selfDual_of_between
end

section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups nonZeroDivisors Pointwise

noncomputable section
namespace GlobalTheory.CompanionTheory.SW.Core.SelfDual

section Arith

variable (F : Type) [Field F] [NumberField F]

def dinv : AddSubgroup F := (Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 F) F)).toAddSubgroup

def oG : AddSubgroup F := (1 : Submodule (𝓞 F) F).toAddSubgroup

variable {F}

theorem mem_oG {b : F} : b ∈ oG F ↔ ∃ r : 𝓞 F, (r : F) = b := by
  unfold oG
  rw [Submodule.mem_toAddSubgroup, Submodule.mem_one]

theorem mem_dinv {b : F} :
    b ∈ dinv F ↔ ∀ r : 𝓞 F, ∃ n : ℤ, Algebra.trace ℚ F (b * (r : F)) = n := by
  unfold dinv
  rw [Submodule.mem_toAddSubgroup, Submodule.mem_traceDual]
  constructor
  · intro h r
    obtain ⟨n, hn⟩ := h r (Submodule.mem_one.2 ⟨r, rfl⟩)
    exact ⟨n, by simpa [Algebra.traceForm_apply] using hn.symm⟩
  · intro h a ha
    obtain ⟨r, rfl⟩ := Submodule.mem_one.1 ha
    obtain ⟨n, hn⟩ := h r
    exact ⟨n, by simpa [Algebra.traceForm_apply] using hn.symm⟩

theorem oG_le_dinv : oG F ≤ dinv F := fun _ hx => Submodule.one_le_traceDual_one hx

theorem oG_eq_closure : oG F = AddSubgroup.closure (Set.range (integralBasis F)) := by
  ext x
  rw [← Submodule.span_int_eq_addSubgroupClosure, Submodule.mem_toAddSubgroup,
    mem_span_integralBasis, mem_oG]
  rfl

open scoped Classical in
theorem dinv_eq_closure :
    dinv F = AddSubgroup.closure (Set.range (integralBasis F).traceDual) := by
  have h := Submodule.traceDual_span_of_basis ℤ (1 : Submodule (𝓞 F) F) (integralBasis F) (by
    ext x
    rw [Submodule.restrictScalars_mem, mem_span_integralBasis, Submodule.mem_one]
    rfl)
  rw [← Submodule.span_int_eq_addSubgroupClosure, ← h]
  rfl

theorem relIndex_oG_dinv : (oG F).relIndex (dinv F) = (discr F).natAbs := by
  classical
  set e := integralBasis F with he
  have h2 : dinv F = AddSubgroup.closure (Set.range e.traceDual) := dinv_eq_closure
  have key := AddSubgroup.relIndex_eq_abs_det (oG F) (dinv F) oG_le_dinv e e.traceDual
    oG_eq_closure h2
  have hdet : e.traceDual.det e = ((discr F : ℤ) : ℚ) := by
    rw [coe_discr, Algebra.discr_def, Module.Basis.det_apply]
    congr 1
    ext i j
    simp [Module.Basis.toMatrix_apply, Module.Basis.traceDual_repr_apply,
      Algebra.traceMatrix_apply, Algebra.traceForm_apply, he, mul_comm]
  rw [hdet] at key
  have : (((oG F).relIndex (dinv F) : ℕ) : ℚ) = (((discr F).natAbs : ℕ) : ℚ) := by
    rw [key, Nat.cast_natAbs, Int.cast_abs]
  exact_mod_cast this

theorem mem_oG_of_dual {b : F} (h : ∀ d ∈ dinv F, ∃ n : ℤ, Algebra.trace ℚ F (d * b) = n) :
    b ∈ oG F := by
  classical
  set e := integralBasis F with he
  have hmem : ∀ i, e.traceDual i ∈ dinv F := by
    intro i
    rw [dinv_eq_closure]
    exact AddSubgroup.subset_closure (Set.mem_range_self i)
  have hrepr : ∀ i, ∃ n : ℤ, e.repr b i = n := by
    intro i
    obtain ⟨n, hn⟩ := h _ (hmem i)
    refine ⟨n, ?_⟩
    have := Module.Basis.traceDual_repr_apply e.traceDual b i
    rw [Module.Basis.traceDual_traceDual, Algebra.traceForm_apply, mul_comm] at this
    rw [this, hn]
  rw [← e.sum_repr b, oG_eq_closure]
  refine sum_mem fun i _ => ?_
  obtain ⟨n, hn⟩ := hrepr i
  rw [hn, Int.cast_smul_eq_zsmul]
  exact zsmul_mem (AddSubgroup.subset_closure (Set.mem_range_self i)) n

end Arith

section Generic

variable {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]

theorem isCompact_of_relIndex {H K : AddSubgroup G} (hHK : H ≤ K) (hi : H.relIndex K ≠ 0)
    (hH : IsCompact (H : Set G)) : IsCompact (K : Set G) := by
  have : (H.addSubgroupOf K).FiniteIndex := ⟨hi⟩
  have hT : (Set.range fun q : K ⧸ H.addSubgroupOf K => ((Quotient.out q : K) : G)).Finite :=
    Set.finite_range _
  have e : (K : Set G) =
      (Set.range fun q : K ⧸ H.addSubgroupOf K => ((Quotient.out q : K) : G)) + (H : Set G) := by
    ext x
    constructor
    · intro hx
      have h := QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq'
        (QuotientAddGroup.mk (⟨x, hx⟩ : K) : K ⧸ H.addSubgroupOf K))
      refine Set.mem_add.2 ⟨_, ⟨QuotientAddGroup.mk (⟨x, hx⟩ : K), rfl⟩, _, ?_, add_neg_cancel_left _ x⟩
      simpa [AddSubgroup.mem_addSubgroupOf] using h
    · rintro ⟨_, ⟨q, rfl⟩, h, hh, rfl⟩
      exact K.add_mem (Quotient.out q).2 (hHK hh)
  rw [e]
  exact hT.isCompact.add hH

end Generic

section Adelic

variable (F : Type) [Field F] [NumberField F]

def ohG : AddSubgroup (A F) where
  carrier := Oh F
  add_mem' := fun ha hb v => add_mem (ha v) (hb v)
  zero_mem' := fun v => zero_mem (v.adicCompletionIntegers F)
  neg_mem' := fun ha v => neg_mem (ha v)

def fr : F →+ A F := (algebraMap F (A F)).toAddMonoidHom

variable {F}

theorem oh_mul {x y : A F} (hx : x ∈ Oh F) (hy : y ∈ Oh F) : x * y ∈ Oh F :=
  fun v => mul_mem (hx v) (hy v)

def perpG (ψ : AddChar (A F) ℂ) (L : AddSubgroup (A F)) : AddSubgroup (A F) where
  carrier := perp (fun x y => ψ (x * y)) L
  add_mem' := fun {a b} ha hb x hx => by
    have h1 : ψ (x * a) = 1 := ha x hx
    have h2 : ψ (x * b) = 1 := hb x hx
    show ψ (x * (a + b)) = 1
    rw [mul_add, AddChar.map_add_eq_mul, h1, h2, one_mul]
  zero_mem' := fun x _ => by
    show ψ (x * 0) = 1
    rw [mul_zero, AddChar.map_zero_eq_one]
  neg_mem' := fun {a} ha x hx => by
    have h1 : ψ (x * a) = 1 := ha x hx
    show ψ (x * -a) = 1
    rw [mul_neg, AddChar.map_neg_eq_inv, h1, inv_one]

abbrev MG (ψ : AddChar (A F) ℂ) : AddSubgroup (A F) := perpG ψ (ohG F)

variable {ψ : AddChar (A F) ℂ}

theorem ohG_le_MG (hψ : IsStdChar F ψ) : ohG F ≤ MG ψ :=
  fun _ hx z hz => ((GlobalTheory.T.standard_adelic_character F).2 ψ hψ).2.1 _ (oh_mul hz hx)

theorem algebraMap_mem_MG_iff (hψ : IsStdChar F ψ) {b : F} :
    algebraMap F (A F) b ∈ MG ψ ↔ b ∈ dinv F := by
  rw [mem_dinv, ← ((GlobalTheory.T.standard_adelic_character F).2 ψ hψ).2.2 b]
  exact forall₂_congr fun z _ => by
    show ψ (z * _) = 1 ↔ _
    rw [mul_comm]

theorem MG_eq (hψ : IsStdChar F ψ) : MG ψ = (dinv F).map (fr F) ⊔ ohG F := by
  obtain ⟨-, -, -, -, hop, hden, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  apply le_antisymm
  · intro x hx
    have hopen : IsOpen {y : A F | y - x ∈ Oh F} :=
      hop.preimage (continuous_id.sub continuous_const)
    obtain ⟨b, hb⟩ := hden.exists_mem_open hopen ⟨x, by
      show x - x ∈ Oh F
      rw [sub_self]
      exact (ohG F).zero_mem⟩
    have hb' : algebraMap F (A F) b - x ∈ ohG F := hb
    have hbM : algebraMap F (A F) b ∈ MG ψ := by
      have := (MG ψ).add_mem hx (ohG_le_MG hψ hb')
      simpa using this
    have e : x = algebraMap F (A F) b + -(algebraMap F (A F) b - x) := by abel
    rw [e]
    exact add_mem (AddSubgroup.mem_sup_left ⟨b, (algebraMap_mem_MG_iff hψ).1 hbM, rfl⟩)
      (AddSubgroup.mem_sup_right (neg_mem hb'))
  · refine sup_le ?_ (ohG_le_MG hψ)
    rintro _ ⟨b, hb, rfl⟩
    exact (algebraMap_mem_MG_iff hψ).2 hb

theorem comap_ohG : (ohG F).comap (fr F) = oG F := by
  obtain ⟨-, -, -, -, -, -, hint, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  ext b
  rw [mem_oG, ← hint b]
  rfl

theorem relIndex_MG (hψ : IsStdChar F ψ) : (ohG F).relIndex (MG ψ) = (discr F).natAbs := by
  rw [MG_eq hψ, AddSubgroup.relIndex_sup_right, ← AddSubgroup.relIndex_comap, comap_ohG]
  exact relIndex_oG_dinv

theorem perp_MG_subset (hψ : IsStdChar F ψ) :
    perp (fun x y => ψ (x * y)) (MG ψ : Set (A F)) ⊆ Oh F := by
  obtain ⟨-, -, -, -, -, -, hint, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  intro y hy
  have hyM : y ∈ MG ψ := fun z hz => hy z (ohG_le_MG hψ hz)
  rw [MG_eq hψ] at hyM
  obtain ⟨u, hu, o, ho, rfl⟩ := AddSubgroup.mem_sup.1 hyM
  obtain ⟨b, hb, rfl⟩ := hu
  have hbO : b ∈ oG F := by
    refine mem_oG_of_dual fun d hd => ?_
    have hd' : algebraMap F (A F) d ∈ MG ψ := (algebraMap_mem_MG_iff hψ).2 hd
    have h1 : ψ (algebraMap F (A F) d * (fr F b + o)) = 1 := hy _ hd'
    have h2 : ψ (o * algebraMap F (A F) d) = 1 := hd' o ho
    have e : fr F b = algebraMap F (A F) b := rfl
    rw [e, mul_add, AddChar.map_add_eq_mul, mul_comm (algebraMap F (A F) d) o, h2, mul_one,
      ← map_mul, hψ.2] at h1
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h1
    refine ⟨-n, ?_⟩
    have h3 : ((Algebra.trace ℚ F (d * b) : ℚ) : ℂ) = ((-n : ℤ) : ℂ) := by
      refine mul_right_cancel₀ Complex.two_pi_I_ne_zero ?_
      push_cast
      linear_combination -hn
    exact_mod_cast h3
  exact (ohG F).add_mem ((hint b).2 (mem_oG.1 hbO)) ho

def sc (c : F) (hc : c ≠ 0) : A F ≃ₜ A F where
  toFun x := algebraMap F (A F) c * x
  invFun x := algebraMap F (A F) c⁻¹ * x
  left_inv x := by
    show algebraMap F (A F) c⁻¹ * (algebraMap F (A F) c * x) = x
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul]
  right_inv x := by
    show algebraMap F (A F) c * (algebraMap F (A F) c⁻¹ * x) = x
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hc, map_one, one_mul]
  continuous_toFun := continuous_const.mul continuous_id
  continuous_invFun := continuous_const.mul continuous_id

def lat (c : F) : AddSubgroup (A F) := (ohG F).map (AddMonoidHom.mulLeft (algebraMap F (A F) c))

theorem coe_lat (c : F) : (lat c : Set (A F)) = (fun x => algebraMap F (A F) c * x) '' Oh F := rfl

theorem perp_lat {c : F} (hc : c ≠ 0) : perp (fun x y => ψ (x * y)) (lat c : Set (A F)) =
    (fun x => algebraMap F (A F) c⁻¹ * x) '' (MG ψ : Set (A F)) := by
  have hcc : algebraMap F (A F) c * algebraMap F (A F) c⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hc, map_one]
  ext y
  constructor
  · intro hy
    refine ⟨algebraMap F (A F) c * y, fun z hz => ?_, ?_⟩
    · have h : ψ (algebraMap F (A F) c * z * y) = 1 := hy _ ⟨z, hz, rfl⟩
      show ψ (z * (algebraMap F (A F) c * y)) = 1
      rwa [mul_left_comm, ← mul_assoc]
    · show algebraMap F (A F) c⁻¹ * (algebraMap F (A F) c * y) = y
      rw [← mul_assoc, mul_comm (algebraMap F (A F) c⁻¹), hcc, one_mul]
  · rintro ⟨m, hm, rfl⟩ _ ⟨z, hz, rfl⟩
    have h : ψ (z * m) = 1 := hm z hz
    show ψ (AddMonoidHom.mulLeft (algebraMap F (A F) c) z * (algebraMap F (A F) c⁻¹ * m)) = 1
    have e : AddMonoidHom.mulLeft (algebraMap F (A F) c) z * (algebraMap F (A F) c⁻¹ * m) = z * m := by
      show algebraMap F (A F) c * z * (algebraMap F (A F) c⁻¹ * m) = z * m
      calc _ = (algebraMap F (A F) c * algebraMap F (A F) c⁻¹) * (z * m) := by ring
        _ = z * m := by rw [hcc, one_mul]
    rw [e, h]

theorem perp_perp_lat (hψ : IsStdChar F ψ) {c : F} (hc : c ≠ 0) :
    perp (fun x y => ψ (x * y)) (perp (fun x y => ψ (x * y)) (lat c : Set (A F))) ⊆
      (lat c : Set (A F)) := by
  rw [perp_lat hc]
  intro y hy
  have hcc : algebraMap F (A F) c * algebraMap F (A F) c⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hc, map_one]
  have h1 : algebraMap F (A F) c⁻¹ * y ∈ Oh F := by
    refine perp_MG_subset hψ fun m hm => ?_
    have h : ψ (algebraMap F (A F) c⁻¹ * m * y) = 1 := hy _ ⟨m, hm, rfl⟩
    show ψ (m * (algebraMap F (A F) c⁻¹ * y)) = 1
    rwa [mul_left_comm, ← mul_assoc]
  refine ⟨_, h1, ?_⟩
  show algebraMap F (A F) c * (algebraMap F (A F) c⁻¹ * y) = y
  rw [← mul_assoc, hcc, one_mul]


theorem mem_lat_inv {N : ℕ} (hN : 0 < N) {x : A F} (h : (N : A F) * x ∈ Oh F) :
    x ∈ lat ((N : F)⁻¹) :=
  ⟨_, h, by
    show algebraMap F (A F) (N : F)⁻¹ * ((N : A F) * x) = x
    have hN' : (N : F) ≠ 0 := by exact_mod_cast hN.ne'
    rw [← map_natCast (algebraMap F (A F)) N, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hN', map_one,
      one_mul]⟩

theorem kap_sq : kap F ^ 2 * |(discr F : ℝ)| = 1 := by
  have hd : 0 < |(discr F : ℝ)| := abs_pos.2 (by exact_mod_cast discr_ne_zero F)
  unfold kap
  rw [inv_pow, Real.sq_sqrt hd.le, inv_mul_cancel₀ hd.ne']

theorem kap_pos : 0 < kap F := by
  have hd : 0 < |(discr F : ℝ)| := abs_pos.2 (by exact_mod_cast discr_ne_zero F)
  exact inv_pos.2 (Real.sqrt_pos.2 hd)

variable [MeasurableSpace (A F)] [BorelSpace (A F)]

theorem lat_all (hψ : IsStdChar F ψ) (lf : Measure (A F)) (hlf : lf.IsAddHaarMeasure)
    (h1 : lf (Oh F) = 1) {c : F} (hc : c ≠ 0) :
    IsCompact (lat c : Set (A F)) ∧ IsOpen (lat c : Set (A F)) ∧
      IsCompact (perp (fun x y => ψ (x * y)) (lat c : Set (A F))) ∧
      IsOpen (perp (fun x y => ψ (x * y)) (lat c : Set (A F))) ∧
      perp (fun x y => ψ (x * y)) (perp (fun x y => ψ (x * y)) (lat c : Set (A F))) ⊆
        (lat c : Set (A F)) ∧
      (ENNReal.ofReal (kap F) • lf) (lat c : Set (A F)) *
        (ENNReal.ofReal (kap F) • lf) (perp (fun x y => ψ (x * y)) (lat c : Set (A F))) = 1 := by
  obtain ⟨hlc, hsc, ht2, hcpt, hop, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  have hne : (ohG F).relIndex (MG ψ) ≠ 0 := by
    rw [relIndex_MG hψ]
    exact Int.natAbs_ne_zero.2 (discr_ne_zero F)
  have hMc : IsCompact (MG ψ : Set (A F)) := isCompact_of_relIndex (ohG_le_MG hψ) hne hcpt
  have hMo : IsOpen (MG ψ : Set (A F)) := AddSubgroup.isOpen_mono (ohG_le_MG hψ) hop
  have hMm : lf (MG ψ : Set (A F)) = ((discr F).natAbs : ℝ≥0∞) := by
    have h := PI.VolStabS.measure_eq_relIndex_mul lf (ohG F) (MG ψ) (ohG_le_MG hψ)
      hMo.measurableSet hop.measurableSet hne
    rw [h, relIndex_MG hψ]
    have h1' : lf (ohG F : Set (A F)) = 1 := h1
    rw [h1', mul_one]
  have hci : c⁻¹ ≠ 0 := inv_ne_zero hc
  have hs := (GlobalTheory.T.adelic_haar_measure_scaling F lf hlf h1).1
  refine ⟨?_, ?_, ?_, ?_, perp_perp_lat hψ hc, ?_⟩
  · rw [coe_lat]
    exact hcpt.image (sc c hc).continuous
  · rw [coe_lat]
    exact (sc c hc).isOpenMap _ hop
  · rw [perp_lat hc]
    exact hMc.image (sc c⁻¹ hci).continuous
  · rw [perp_lat hc]
    exact (sc c⁻¹ hci).isOpenMap _ hMo
  · rw [perp_lat hc, coe_lat, Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul,
      hs c hc _ hop.measurableSet, hs c⁻¹ hci _ hMo.measurableSet, h1, hMm, mul_one]
    have hr : 0 < |((Algebra.norm ℚ c : ℚ) : ℝ)| :=
      abs_pos.2 (by exact_mod_cast Algebra.norm_ne_zero_iff.2 hc)
    have hinv : |((Algebra.norm ℚ c⁻¹ : ℚ) : ℝ)|⁻¹ = |((Algebra.norm ℚ c : ℚ) : ℝ)| := by
      have hn : Algebra.norm ℚ c⁻¹ * Algebra.norm ℚ c = 1 := by
        rw [← map_mul, inv_mul_cancel₀ hc, map_one]
      rw [eq_inv_of_mul_eq_one_left hn, Rat.cast_inv, abs_inv, inv_inv]
    have hD : ((discr F).natAbs : ℝ≥0∞) = ENNReal.ofReal |(discr F : ℝ)| := by
      rw [← ENNReal.ofReal_natCast, Nat.cast_natAbs, Int.cast_abs]
    rw [hinv, hD]
    generalize |((Algebra.norm ℚ c : ℚ) : ℝ)| = r at hr
    have hk : 0 ≤ kap F := kap_pos.le
    have e : kap F * r⁻¹ * (kap F * (r * |(discr F : ℝ)|)) = 1 := by
      calc _ = (kap F ^ 2 * |(discr F : ℝ)|) * (r⁻¹ * r) := by ring
        _ = 1 := by rw [kap_sq, inv_mul_cancel₀ hr.ne', one_mul]
    calc _ = ENNReal.ofReal (kap F * r⁻¹ * (kap F * (r * |(discr F : ℝ)|))) := by
          rw [ENNReal.ofReal_mul (mul_nonneg hk (inv_nonneg.2 hr.le)), ENNReal.ofReal_mul hk,
            ENNReal.ofReal_mul hk, ENNReal.ofReal_mul hr.le]
      _ = 1 := by rw [e, ENNReal.ofReal_one]

end Adelic

theorem finiteAdeles_selfDual : ∀ (F : Type) [Field F] [NumberField F] [MeasurableSpace (A F)]
    [BorelSpace (A F)] (lf : Measure (A F)), lf.IsAddHaarMeasure → lf (Oh F) = 1 →
    ∀ ψ : AddChar (A F) ℂ, IsStdChar F ψ →
      NADual (A F) (fun x y => ψ (x * y)) (ENNReal.ofReal (kap F) • lf) := by
  intro F _ _ _ _ lf hlf h1 ψ hψ
  obtain ⟨hlc, hsc, ht2, hcpt, hop, -, -, hsm, hbd, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  have hnorm := ((GlobalTheory.T.standard_adelic_character F).2 ψ hψ).1
  have hμ : (ENNReal.ofReal (kap F) • lf).IsAddHaarMeasure :=
    Measure.IsAddHaarMeasure.smul lf (by simpa using kap_pos) ENNReal.ofReal_ne_top
  have hsymm : ∀ x y : A F, (fun x y => ψ (x * y)) x y = (fun x y => ψ (x * y)) y x :=
    fun x y => by simp only [mul_comm]
  have hadd : ∀ x x' y : A F, (fun x y => ψ (x * y)) (x + x') y =
      (fun x y => ψ (x * y)) x y * (fun x y => ψ (x * y)) x' y :=
    fun x x' y => by simp only [add_mul, AddChar.map_add_eq_mul]
  have hl := fun {c : F} (hc : c ≠ 0) => lat_all hψ lf hlf h1 hc
  have hNF : ∀ {N : ℕ}, 0 < N → (N : F) ≠ 0 := fun h => by exact_mod_cast h.ne'
  unfold NADual
  refine ⟨inferInstance, ht2, hlc, hsc, inferInstance, hμ, ?_, ?_, ?_, hsymm, fun x y => hnorm _,
    hadd, ?_⟩
  · intro U hU
    obtain ⟨N, hN, h⟩ := hsm U hU
    refine ⟨lat (N : F), (hl (hNF hN)).1, (hl (hNF hN)).2.1, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    have e : AddMonoidHom.mulLeft (algebraMap F (A F) (N : F)) z = (N : A F) * z := by
      show algebraMap F (A F) (N : F) * z = _
      rw [map_natCast]
    rw [e]
    exact h z hz
  · intro x
    obtain ⟨N, hN, h⟩ := hbd {x} isCompact_singleton
    have hi := inv_ne_zero (hNF hN)
    exact ⟨lat (N : F)⁻¹, (hl hi).1, (hl hi).2.1, mem_lat_inv hN (h x rfl)⟩
  · exact hψ.1.comp (continuous_fst.mul continuous_snd)
  · intro L hLc hLo
    obtain ⟨N₁, hN₁, k₁⟩ := hsm _ (hLo.mem_nhds L.zero_mem)
    obtain ⟨N₂, hN₂, k₂⟩ := hbd _ hLc
    have a := hl (hNF hN₁)
    have b := hl (inv_ne_zero (hNF hN₂))
    refine GlobalTheory.T.annihilator_of_annihilator_le (A F) (fun x y => ψ (x * y)) (ENNReal.ofReal (kap F) • lf) hμ hsymm
      (fun x y => hnorm _) hadd (lat (N₁ : F)) L (lat (N₂ : F)⁻¹) ?_ ?_ a.2.1 b.1 a.2.2.1 b.2.2.2.1
      a.2.2.2.2.1 b.2.2.2.2.1 a.2.2.2.2.2 b.2.2.2.2.2
    · rintro _ ⟨z, hz, rfl⟩
      have e : AddMonoidHom.mulLeft (algebraMap F (A F) (N₁ : F)) z = (N₁ : A F) * z := by
        show algebraMap F (A F) (N₁ : F) * z = _
        rw [map_natCast]
      rw [e]
      exact k₁ z hz
    · exact fun x hx => mem_lat_inv hN₂ (k₂ x hx)

end GlobalTheory.CompanionTheory.SW.Core.SelfDual
end
end

section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adeles_self_dual : ∀ (F : Type) [Field F] [NumberField F] [MeasurableSpace (A F)] [BorelSpace (A F)] (lf : Measure (A F)), lf.IsAddHaarMeasure → lf (Oh F) = 1 → ∀ ψ : AddChar (A F) ℂ, IsStdChar F ψ → NADual (A F) (fun x y => ψ (x * y)) (ENNReal.ofReal (kap F) • lf) := by
  first | exact @GlobalTheory.CompanionTheory.SW.Core.SelfDual.finiteAdeles_selfDual | exact GlobalTheory.CompanionTheory.SW.Core.SelfDual.finiteAdeles_selfDual | (intros; apply GlobalTheory.CompanionTheory.SW.Core.SelfDual.finiteAdeles_selfDual <;> assumption)
end

section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

noncomputable section
namespace GlobalTheory.CompanionTheory.SW.Core.SelfDual

def OhR (F : Type) [Field F] [NumberField F] : Subring (A F) where
  carrier := Oh F
  mul_mem' := fun {_ _} ha hb v => mul_mem (ha v) (hb v)
  one_mem' := fun _ => one_mem _
  add_mem' := fun {_ _} ha hb v => add_mem (ha v) (hb v)
  zero_mem' := fun _ => zero_mem _
  neg_mem' := fun {_} ha v => neg_mem (ha v)

variable {F : Type} [Field F] [NumberField F] {ι : Type}

def LL (ι : Type) (c : F) : AddSubgroup (ι → A F) where
  carrier := {x | ∀ i, algebraMap F (A F) c⁻¹ * x i ∈ Oh F}
  add_mem' := fun {a b} ha hb i => by
    have h : _ ∈ OhR F := (OhR F).add_mem (ha i) (hb i)
    rw [Pi.add_apply, mul_add]
    exact h
  zero_mem' := fun i => by
    rw [Pi.zero_apply, mul_zero]
    exact (OhR F).zero_mem
  neg_mem' := fun {a} ha i => by
    rw [Pi.neg_apply, mul_neg]
    exact (OhR F).neg_mem (ha i)

variable [Fintype ι] [DecidableEq ι]

lemma Bf_mul (g h : Matrix ι ι F) : Bf (g * h) = Bf g * Bf h := Matrix.map_mul

lemma Bf_one : Bf (1 : Matrix ι ι F) = 1 := Matrix.map_one _ (map_zero _) (map_one _)

lemma Bf_transpose (g : Matrix ι ι F) : Bf gᵀ = (Bf g)ᵀ := by
  ext i j; rfl

lemma Bf_inv_mul {g : Matrix ι ι F} (hg : g.det ≠ 0) : Bf g⁻¹ * Bf g = 1 := by
  rw [← Bf_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hg), Bf_one]

lemma Bf_mul_inv {g : Matrix ι ι F} (hg : g.det ≠ 0) : Bf g * Bf g⁻¹ = 1 := by
  rw [← Bf_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hg), Bf_one]

lemma Bf_smul_one (c : F) : Bf (c • (1 : Matrix ι ι F)) = algebraMap F (A F) c • 1 := by
  ext i j
  by_cases h : i = j
  · subst h; simp [Bf]
  · simp [Bf, Matrix.one_apply, h]

def Gs (g : Matrix ι ι F) (S : Set (A F)) : Set (ι → A F) :=
  (fun x => Bf g *ᵥ x) '' Set.univ.pi fun _ => S

lemma mem_Gs_iff {g : Matrix ι ι F} (hg : g.det ≠ 0) {S : Set (A F)} {y : ι → A F} :
    y ∈ Gs g S ↔ ∀ i, (Bf g⁻¹ *ᵥ y) i ∈ S := by
  constructor
  · rintro ⟨x, hx, rfl⟩ i
    simp only [Matrix.mulVec_mulVec, Bf_inv_mul hg, Matrix.one_mulVec]
    exact hx i (Set.mem_univ i)
  · intro h
    refine ⟨Bf g⁻¹ *ᵥ y, fun i _ => h i, ?_⟩
    simp only [Matrix.mulVec_mulVec, Bf_mul_inv hg, Matrix.one_mulVec]

lemma continuous_mulVec' (M : Matrix ι ι (A F)) : Continuous fun y : ι → A F => M *ᵥ y :=
  Continuous.matrix_mulVec continuous_const continuous_id

lemma isOpen_Gs {g : Matrix ι ι F} (hg : g.det ≠ 0) {S : Set (A F)} (hS : IsOpen S) :
    IsOpen (Gs g S) := by
  have h : Gs g S = (fun y => Bf g⁻¹ *ᵥ y) ⁻¹' Set.univ.pi fun _ => S := by
    ext y
    simp [mem_Gs_iff hg]
  rw [h]
  exact (isOpen_set_pi Set.finite_univ fun _ _ => hS).preimage (continuous_mulVec' _)

lemma isCompact_Gs (g : Matrix ι ι F) {S : Set (A F)} (hS : IsCompact S) :
    IsCompact (Gs g S) :=
  (isCompact_univ_pi fun _ => hS).image (continuous_mulVec' _)

lemma Gs_mono (g : Matrix ι ι F) {S T : Set (A F)} (h : S ⊆ T) : Gs g S ⊆ Gs g T :=
  Set.image_mono (Set.pi_mono fun _ _ => h)

lemma det_inv_ne {g : Matrix ι ι F} (hg : g.det ≠ 0) : (g⁻¹).det ≠ 0 := by
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  exact inv_ne_zero hg

lemma psi_sum {R : Type} [CommRing R] (ψ : AddChar R ℂ) (s : Finset ι) (f : ι → R) :
    ψ (∑ i ∈ s, f i) = ∏ i ∈ s, ψ (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

lemma perp_Gs (ψ : AddChar (A F) ℂ) (B g : Matrix ι ι F) (hg : (gᵀ * B).det ≠ 0) {S : Set (A F)}
    (h0 : (0 : A F) ∈ S) :
    perp (chiB ψ (Bf B)) (Gs g S) = Gs (gᵀ * B)⁻¹ (perp (fun x y => ψ (x * y)) S) := by
  have key : ∀ s y : ι → A F, chiB ψ (Bf B) (Bf g *ᵥ s) y = ψ (s ⬝ᵥ (Bf (gᵀ * B) *ᵥ y)) := by
    intro s y
    unfold chiB
    rw [Bf_mul, Bf_transpose, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec s,
      Matrix.vecMul_transpose]
  ext y
  rw [mem_Gs_iff (det_inv_ne hg), Matrix.nonsing_inv_nonsing_inv _ (isUnit_iff_ne_zero.2 hg)]
  constructor
  · intro h i a ha
    have h1 := h (Bf g *ᵥ Pi.single i a) ⟨_, fun j _ => by
      by_cases hj : j = i
      · subst hj; simpa using ha
      · simpa [hj] using h0, rfl⟩
    rw [key] at h1
    simpa using h1
  · rintro h x ⟨s, hs, rfl⟩
    show chiB ψ (Bf B) (Bf g *ᵥ s) y = 1
    rw [key, dotProduct, psi_sum]
    exact Finset.prod_eq_one fun i _ => h i (s i) (hs i (Set.mem_univ i))

lemma norm_inv' (x : F) (hx : x ≠ 0) : Algebra.norm ℚ x⁻¹ = (Algebra.norm ℚ x)⁻¹ := by
  have h := map_mul (Algebra.norm ℚ) x x⁻¹
  rw [mul_inv_cancel₀ hx, map_one] at h
  exact (inv_eq_of_mul_eq_one_right h.symm).symm

lemma coe_LL {c : F} (hc : c ≠ 0) :
    (LL ι c : Set (ι → A F)) = Gs (c • (1 : Matrix ι ι F)) (Oh F) := by
  have hd : (c • (1 : Matrix ι ι F)).det ≠ 0 := by
    rw [Matrix.det_smul, Matrix.det_one, mul_one]
    exact pow_ne_zero _ hc
  have hi : (c • (1 : Matrix ι ι F))⁻¹ = c⁻¹ • 1 := by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, inv_mul_cancel₀ hc, one_smul]
  ext x
  have e : (algebraMap F (A F) c⁻¹ • (1 : Matrix ι ι (A F))) *ᵥ x =
      fun i => algebraMap F (A F) c⁻¹ * x i := by
    rw [Matrix.smul_mulVec, Matrix.one_mulVec]
    rfl
  rw [mem_Gs_iff hd, hi, Bf_smul_one, e]
  exact Iff.rfl

section Measure

variable [MeasurableSpace (A F)] [BorelSpace (A F)]

lemma pi_Gs (lf : Measure (A F)) (hlf : lf.IsAddHaarMeasure) (h1 : lf (Oh F) = 1)
    {g : Matrix ι ι F} (hg : g.det ≠ 0) {S : Set (A F)} (hS : MeasurableSet S) :
    (Measure.pi fun _ : ι => lf) (Gs g S) =
      ENNReal.ofReal (|((Algebra.norm ℚ g.det : ℚ) : ℝ)|⁻¹) * lf S ^ Fintype.card ι := by
  obtain ⟨hlc, hsc, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  haveI := hlc
  haveI := hsc
  haveI : SigmaFinite lf := inferInstance
  have h := (GlobalTheory.T.adelic_haar_measure_linear_change F lf hlf h1 ι).1 g hg (Set.univ.pi fun _ => S)
    (MeasurableSet.univ_pi fun _ => hS)
  rw [Gs, h, Measure.pi_pi]
  simp

end Measure

lemma exists_LL_subset {U : Set (ι → A F)} (hU : U ∈ 𝓝 (0 : ι → A F)) :
    ∃ N : ℕ, 0 < N ∧ (LL ι (N : F) : Set (ι → A F)) ⊆ U := by
  rw [nhds_pi, Filter.mem_pi] at hU
  obtain ⟨I, -, t, ht, hsub⟩ := hU
  have hU' : (⋂ i, t i) ∈ 𝓝 (0 : A F) := Filter.iInter_mem.2 fun i => ht i
  obtain ⟨-, -, -, -, -, -, -, hnb, -, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  obtain ⟨N, hN, hNU⟩ := hnb _ hU'
  refine ⟨N, hN, fun x hx => hsub fun i _ => ?_⟩
  have hN' : (N : F) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have h := hNU _ (hx i)
  have e : (N : A F) * (algebraMap F (A F) (N : F)⁻¹ * x i) = x i := by
    rw [← mul_assoc, ← map_natCast (algebraMap F (A F)) N, ← map_mul, mul_inv_cancel₀ hN', map_one,
      one_mul]
  rw [e] at h
  exact Set.mem_iInter.1 h i

lemma exists_subset_LL {K : Set (ι → A F)} (hK : IsCompact K) :
    ∃ N : ℕ, 0 < N ∧ K ⊆ (LL ι ((N : F)⁻¹) : Set (ι → A F)) := by
  have hK' : IsCompact (⋃ i, (fun x : ι → A F => x i) '' K) :=
    isCompact_iUnion fun i => hK.image (continuous_apply i)
  obtain ⟨-, -, -, -, -, -, -, -, hcp, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  obtain ⟨N, hN, hNK⟩ := hcp _ hK'
  refine ⟨N, hN, fun x hx i => ?_⟩
  rw [inv_inv, map_natCast]
  exact hNK _ (Set.mem_iUnion.2 ⟨i, x, hx, rfl⟩)

section Main

variable [MeasurableSpace (A F)] [BorelSpace (A F)]

lemma real_id (k s d : ℝ) (n : ℕ) (hk : k ≠ 0) (hs : s ≠ 0) (hd : d ≠ 0) :
    k ^ n * s⁻¹ * d⁻¹ * (k ^ n * s⁻¹ * (d * (s * s) * ((k * k)⁻¹) ^ n)) = 1 := by
  have h : ((k * k)⁻¹) ^ n = (k ^ n)⁻¹ * (k ^ n)⁻¹ := by rw [inv_pow, mul_pow, mul_inv]
  have hkn := pow_ne_zero n hk
  rw [h]
  field_simp

lemma mass_one (lf : Measure (A F)) (hlf : lf.IsAddHaarMeasure) (h1 : lf (Oh F) = 1)
    {B g : Matrix ι ι F} (hB : B.det ≠ 0) (hg : g.det ≠ 0) {P : Set (A F)} (hPm : MeasurableSet P)
    (hP : ENNReal.ofReal (kap F) * (ENNReal.ofReal (kap F) * lf P) = 1) :
    muF B lf (Gs g (Oh F)) * muF B lf (Gs (gᵀ * B)⁻¹ P) = 1 := by
  have hk : 0 < kap F := by
    have : (discr F : ℝ) ≠ 0 := by exact_mod_cast discr_ne_zero F
    unfold kap
    positivity
  have hnorm : ∀ {x : F}, x ≠ 0 → 0 < |((Algebra.norm ℚ x : ℚ) : ℝ)| := by
    intro x hx
    have : Algebra.norm ℚ x ≠ 0 := Algebra.norm_ne_zero_iff.2 hx
    have : ((Algebra.norm ℚ x : ℚ) : ℝ) ≠ 0 := by exact_mod_cast this
    positivity
  have hd : (gᵀ * B).det ≠ 0 := by
    rw [Matrix.det_mul, Matrix.det_transpose]
    exact mul_ne_zero hg hB
  have hOm : MeasurableSet (Oh F) := by
    obtain ⟨-, -, -, -, hOo, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
    exact hOo.measurableSet
  have hlP : lf P = ENNReal.ofReal ((kap F * kap F)⁻¹) := by
    rw [← mul_assoc, ← ENNReal.ofReal_mul hk.le] at hP
    rw [ENNReal.ofReal_inv_of_pos (mul_pos hk hk)]
    exact ENNReal.eq_inv_of_mul_eq_one_left (by rwa [mul_comm] at hP)
  have e2 : |((Algebra.norm ℚ ((gᵀ * B)⁻¹).det : ℚ) : ℝ)|⁻¹ =
      |((Algebra.norm ℚ g.det : ℚ) : ℝ)| * |((Algebra.norm ℚ B.det : ℚ) : ℝ)| := by
    rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv', norm_inv' _ hd, Matrix.det_mul,
      Matrix.det_transpose, map_mul]
    push_cast
    rw [abs_inv, inv_inv, abs_mul]
  simp only [muF, Measure.smul_apply, smul_eq_mul]
  rw [pi_Gs lf hlf h1 hg hOm, pi_Gs lf hlf h1 (det_inv_ne hd) hPm, h1, hlP, e2, one_pow, mul_one]
  have hnd := hnorm hg
  have hnD := hnorm hB
  set nd := |((Algebra.norm ℚ g.det : ℚ) : ℝ)|
  set nD := |((Algebra.norm ℚ B.det : ℚ) : ℝ)|
  set n := Fintype.card ι
  have hs : Real.sqrt nD * Real.sqrt nD = nD := Real.mul_self_sqrt hnD.le
  have hsp : 0 < Real.sqrt nD := Real.sqrt_pos.2 hnD
  have ha : 0 ≤ kap F ^ n * (Real.sqrt nD)⁻¹ := by positivity
  rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul ha,
    ← ENNReal.ofReal_mul (p := nd * nD) (by positivity), ← ENNReal.ofReal_mul ha,
    ← ENNReal.ofReal_mul (by positivity)]
  have : kap F ^ n * (Real.sqrt nD)⁻¹ * nd⁻¹ *
      (kap F ^ n * (Real.sqrt nD)⁻¹ * (nd * nD * ((kap F * kap F)⁻¹) ^ n)) = 1 := by
    have h := real_id (kap F) (Real.sqrt nD) nd n hk.ne' hsp.ne' hnd.ne'
    rwa [hs] at h
  rw [this, ENNReal.ofReal_one]

lemma LL_good (lf : Measure (A F)) (hlf : lf.IsAddHaarMeasure) (h1 : lf (Oh F) = 1)
    (ψ : AddChar (A F) ℂ) {B : Matrix ι ι F} (hS : B.IsSymm) (hB : B.det ≠ 0)
    (hOc : IsCompact (Oh F)) (hOo : IsOpen (Oh F))
    (hPc : IsCompact (perp (fun x y => ψ (x * y)) (Oh F)))
    (hPo : IsOpen (perp (fun x y => ψ (x * y)) (Oh F)))
    (hPP : perp (fun x y => ψ (x * y)) (perp (fun x y => ψ (x * y)) (Oh F)) ⊆ Oh F)
    (hP : ENNReal.ofReal (kap F) *
      (ENNReal.ofReal (kap F) * lf (perp (fun x y => ψ (x * y)) (Oh F))) = 1)
    {c : F} (hc : c ≠ 0) :
    IsCompact (LL ι c : Set (ι → A F)) ∧ IsOpen (LL ι c : Set (ι → A F)) ∧
      IsCompact (perp (chiB ψ (Bf B)) (LL ι c : Set (ι → A F))) ∧
      IsOpen (perp (chiB ψ (Bf B)) (LL ι c : Set (ι → A F))) ∧
      perp (chiB ψ (Bf B)) (perp (chiB ψ (Bf B)) (LL ι c : Set (ι → A F))) ⊆ LL ι c ∧
      muF B lf (LL ι c : Set (ι → A F)) *
        muF B lf (perp (chiB ψ (Bf B)) (LL ι c : Set (ι → A F))) = 1 := by
  set g : Matrix ι ι F := c • 1 with hgdef
  have hg : g.det ≠ 0 := by
    rw [hgdef, Matrix.det_smul, Matrix.det_one, mul_one]
    exact pow_ne_zero _ hc
  have hh : (gᵀ * B).det ≠ 0 := by
    rw [Matrix.det_mul, Matrix.det_transpose]
    exact mul_ne_zero hg hB
  have h0 : (0 : A F) ∈ Oh F := (OhR F).zero_mem
  have h0P : (0 : A F) ∈ perp (fun x y => ψ (x * y)) (Oh F) := by
    intro x _
    simp
  have hperp := perp_Gs ψ B g hh h0
  have hhe : gᵀ * B = c • B := by
    simp [hgdef, Matrix.transpose_smul]
  have hmat : (((gᵀ * B)⁻¹)ᵀ * B)⁻¹ = g := by
    apply Matrix.inv_eq_right_inv
    have hsym : (gᵀ * B)ᵀ = gᵀ * B := by
      rw [hhe, Matrix.transpose_smul, hS.eq]
    rw [Matrix.transpose_nonsing_inv, hsym, Matrix.mul_assoc]
    have : B * g = gᵀ * B := by
      rw [hhe, hgdef]
      simp
    rw [this]
    exact Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hh)
  have hh' : (((gᵀ * B)⁻¹)ᵀ * B).det ≠ 0 := by
    rw [Matrix.det_mul, Matrix.det_transpose]
    exact mul_ne_zero (det_inv_ne hh) hB
  have hperp2 := perp_Gs ψ B (gᵀ * B)⁻¹ hh' h0P
  rw [coe_LL hc, ← hgdef]
  rw [hperp, hperp2, hmat]
  refine ⟨isCompact_Gs g hOc, isOpen_Gs hg hOo, isCompact_Gs _ hPc, isOpen_Gs (det_inv_ne hh) hPo,
    Gs_mono g hPP, mass_one lf hlf h1 hB hg hPo.measurableSet hP⟩

theorem naQuad : ∀ (F : Type) [Field F] [NumberField F] [MeasurableSpace (A F)] [BorelSpace (A F)]
    (lf : Measure (A F)), lf.IsAddHaarMeasure → lf (Oh F) = 1 →
    ∀ ψ : AddChar (A F) ℂ, IsStdChar F ψ → ∀ (ι : Type) [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι F), B.IsSymm → B.det ≠ 0 → NAQuad ψ (hf F) (Bf B) (muF B lf) := by
  intro F _ _ _ _ lf hlf h1 ψ hψ ι _ _ B hS hB
  obtain ⟨hlc, hsc, ht2, hOc, hOo, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  haveI := hlc
  haveI := hsc
  haveI := ht2
  haveI : SigmaFinite lf := inferInstance
  obtain ⟨hnorm, -, -⟩ := (GlobalTheory.T.standard_adelic_character F).2 ψ hψ
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hL⟩ := GlobalTheory.T.adeles_self_dual F lf hlf h1 ψ hψ
  have hO : IsCompact (perp (fun x y => ψ (x * y)) (Oh F)) ∧
      IsOpen (perp (fun x y => ψ (x * y)) (Oh F)) ∧
      perp (fun x y => ψ (x * y)) (perp (fun x y => ψ (x * y)) (Oh F)) ⊆ Oh F ∧
      (ENNReal.ofReal (kap F) • lf) (Oh F) *
        (ENNReal.ofReal (kap F) • lf) (perp (fun x y => ψ (x * y)) (Oh F)) = 1 :=
    hL (OhR F).toAddSubgroup hOc hOo
  obtain ⟨hPc, hPo, hPP, hPm⟩ := hO
  have hP : ENNReal.ofReal (kap F) *
      (ENNReal.ofReal (kap F) * lf (perp (fun x y => ψ (x * y)) (Oh F))) = 1 := by
    simpa [Measure.smul_apply, h1] using hPm
  have good : ∀ {c : F}, c ≠ 0 → _ := fun {c} hc =>
    LL_good (ι := ι) lf hlf h1 ψ hS hB hOc hOo hPc hPo hPP hP hc
  have hk : 0 < kap F := by
    have : (discr F : ℝ) ≠ 0 := by exact_mod_cast discr_ne_zero F
    unfold kap
    positivity
  have hnB : 0 < |((Algebra.norm ℚ B.det : ℚ) : ℝ)| := by
    have : Algebra.norm ℚ B.det ≠ 0 := Algebra.norm_ne_zero_iff.2 hB
    have : ((Algebra.norm ℚ B.det : ℚ) : ℝ) ≠ 0 := by exact_mod_cast this
    positivity
  have hhaar : (muF B lf).IsAddHaarMeasure := by
    haveI : (Measure.pi fun _ : ι => lf).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
    refine Measure.IsAddHaarMeasure.smul _ ?_ ENNReal.ofReal_ne_top
    have : 0 < kap F ^ Fintype.card ι * (Real.sqrt |((Algebra.norm ℚ B.det : ℚ) : ℝ)|)⁻¹ := by
      have := Real.sqrt_pos.2 hnB
      positivity
    exact (ENNReal.ofReal_pos.2 this).ne'
  have hsym : ∀ x y : ι → A F, chiB ψ (Bf B) x y = chiB ψ (Bf B) y x := by
    intro x y
    unfold chiB
    have hsB : (Bf B)ᵀ = Bf B := (hS.map (algebraMap F (A F))).eq
    rw [Matrix.dotProduct_mulVec, dotProduct_comm, ← Matrix.mulVec_transpose, hsB]
  have hadd : ∀ x x' y : ι → A F,
      chiB ψ (Bf B) (x + x') y = chiB ψ (Bf B) x y * chiB ψ (Bf B) x' y := by
    intro x x' y
    unfold chiB
    rw [add_dotProduct, AddChar.map_add_eq_mul]
  refine ⟨inferInstance, ?_, hψ.1, hnorm, hS.map _, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, hhaar, ?_, ?_, ?_, ?_, fun _ _ => hnorm _, ?_, ?_⟩
  · rw [hf, ← map_ofNat (algebraMap F (A F)) 2, ← map_mul]
    simp
  · intro U hU
    obtain ⟨N, hN, hNU⟩ := exists_LL_subset hU
    have hN' : (N : F) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    exact ⟨LL ι (N : F), (good hN').1, (good hN').2.1, hNU⟩
  · intro x
    obtain ⟨N, hN, hNK⟩ := exists_subset_LL (isCompact_singleton (x := x))
    have hN' : ((N : F)⁻¹) ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.2 hN.ne')
    exact ⟨LL ι ((N : F)⁻¹), (good hN').1, (good hN').2.1, hNK rfl⟩
  · exact hψ.1.comp (Continuous.dotProduct continuous_fst
      (Continuous.matrix_mulVec continuous_const continuous_snd))
  · exact hsym
  · exact hadd
  · intro L hLc hLo
    obtain ⟨N, hN, hNU⟩ := exists_LL_subset (hLo.mem_nhds L.zero_mem)
    obtain ⟨M, hM, hMK⟩ := exists_subset_LL hLc
    have hN' : (N : F) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    have hM' : ((M : F)⁻¹) ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.2 hM.ne')
    obtain ⟨-, h1o, h1c, -, h1p, h1m⟩ := good hN'
    obtain ⟨h2c, -, -, h2o, h2p, h2m⟩ := good hM'
    exact GlobalTheory.T.annihilator_of_annihilator_le (ι → A F) (chiB ψ (Bf B)) (muF B lf) hhaar
      hsym (fun _ _ => hnorm _) hadd (LL ι (N : F)) L (LL ι ((M : F)⁻¹))
      hNU hMK h1o h2c h1c h2o h1p h2p h1m h2m

end Main

end GlobalTheory.CompanionTheory.SW.Core.SelfDual
end
end
