import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfSurj
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.FullOfSoLoc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilObjectsInhabited

section
noncomputable section

namespace PositivityTheory.ThKG.LocalRamifiedLeviRestriction

open GlobalTheory.WeilM Filter Topology ValuativeRel Matrix PositivityTheory.KCo

section Grp

variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V]

def cs (H : AddSubgroup V) (x : V) : V → ℂ := Set.indicator {y | y - x ∈ H} 1

theorem cs_mem {H : AddSubgroup V} (ho : IsOpen (H : Set V)) (hc : IsCompact (H : Set V)) (x : V) : cs H x ∈ SB V := by
  have o : IsOpen {y | y - x ∈ H} := ho.preimage (continuous_id.sub continuous_const)
  have c : IsClosed {y | y - x ∈ H} := (H.isClosed_of_isOpen ho).preimage (continuous_id.sub continuous_const)
  refine ⟨(LocallyConstant.charFn ℂ ⟨c, o⟩).2, HasCompactSupport.intro (hc.image (continuous_add_right x)) fun y hy => ?_⟩
  exact Set.indicator_of_notMem (s := {y | y - x ∈ H}) (fun h => hy ⟨y - x, h, sub_add_cancel y x⟩) (1 : V → ℂ)

theorem exists_invar {f : V → ℂ} (hf : f ∈ SB V) : ∃ W ∈ 𝓝 (0 : V), ∀ h ∈ W, ∀ y, f (y + h) = f y := by
  have ho : IsOpen {p : V × V | f (p.2 + p.1) - f p.2 = 0} :=
    ((hf.1.comp_continuous (continuous_snd.add continuous_fst)).sub (hf.1.comp_continuous continuous_snd)).isOpen_fiber 0
  obtain ⟨u, w, hu, -, h0, hK, huw⟩ := generalized_tube_lemma (isCompact_singleton (x := (0 : V))) hf.2 ho
    (by rintro ⟨a, b⟩ ⟨ha, -⟩; simp only [Set.mem_singleton_iff] at ha; simp [ha])
  have hu0 : u ∈ 𝓝 (0 : V) := hu.mem_nhds (h0 rfl)
  refine ⟨u ∩ -u, inter_mem hu0 (neg_mem_nhds_zero V hu0), fun h hh y => ?_⟩
  by_cases hy : y ∈ tsupport f
  · exact sub_eq_zero.1 (huw (⟨hh.1, hK hy⟩ : (h, y) ∈ u ×ˢ w))
  · by_cases hy' : y + h ∈ tsupport f
    · have := sub_eq_zero.1 (huw (⟨hh.2, hK hy'⟩ : (-h, y + h) ∈ u ×ˢ w))
      simpa using this.symm
    · rw [image_eq_zero_of_notMem_tsupport hy, image_eq_zero_of_notMem_tsupport hy']

theorem mem_of_cs {H : AddSubgroup V} (ho : IsOpen (H : Set V)) {f : V → ℂ} (hf : f ∈ SB V) (hi : ∀ h ∈ H, ∀ y, f (y + h) = f y)
    (Z : Submodule ℂ (V → ℂ)) (hZ : ∀ x, f x ≠ 0 → cs H x ∈ Z) : f ∈ Z := by
  classical
  haveI : DiscreteTopology (V ⧸ H) := QuotientAddGroup.discreteTopology ho
  have hfin : ((QuotientAddGroup.mk : V → V ⧸ H) '' tsupport f).Finite :=
    (hf.2.isCompact.image QuotientAddGroup.continuous_mk).finite_of_discrete
  have e : f = ∑ q ∈ hfin.toFinset, f q.out • cs H q.out := by
    funext y
    have k : ∀ q : V ⧸ H, y - q.out ∈ H ↔ q = QuotientAddGroup.mk y := fun q => by
      rw [← QuotientAddGroup.out_eq' q, QuotientAddGroup.eq, QuotientAddGroup.out_eq', neg_add_eq_sub]
    have k2 : f (QuotientAddGroup.mk y : V ⧸ H).out = f y := by
      rw [← hi _ ((k _).2 rfl), add_sub_cancel]
    rw [Finset.sum_apply, Finset.sum_eq_single (QuotientAddGroup.mk y)]
    · simp [cs, Set.indicator_of_mem (show y ∈ {z | z - (QuotientAddGroup.mk y : V ⧸ H).out ∈ H} from (k _).2 rfl), k2]
    · intro q _ hq
      simp [cs, Set.indicator_of_notMem (show y ∉ {z | z - q.out ∈ H} from fun h => hq ((k q).1 h))]
    · intro h
      have : f y = 0 := by
        by_contra h0
        exact h (hfin.mem_toFinset.2 ⟨y, subset_tsupport _ h0, rfl⟩)
      simp [k2, this]
  rw [e]
  refine Z.sum_mem fun q _ => ?_
  by_cases h : f q.out = 0
  · simp [h]
  · exact Z.smul_mem _ (hZ _ h)

def Kil (Z : Submodule ℂ (V → ℂ)) (U : Set V) : Prop := ∀ Φ ∈ SB V, (∀ y, Φ y ≠ 0 → y ∈ U) → Φ ∈ Z

theorem cs_ne {H : AddSubgroup V} {x y : V} (h : cs H x y ≠ 0) : y - x ∈ H := by
  by_contra h'
  exact h (Set.indicator_of_notMem (s := {y | y - x ∈ H}) h' _)

theorem nhds_sub {x : V} {B : Set V} (hB : B ∈ 𝓝 x) : {h | x + h ∈ B} ∈ 𝓝 (0 : V) :=
  (continuous_add_left x).continuousAt.preimage_mem_nhds (by simpa using hB)

theorem kil_loc (hV : ∀ W ∈ 𝓝 (0 : V), ∃ H : AddSubgroup V, IsOpen (H : Set V) ∧ IsCompact (H : Set V) ∧ (H : Set V) ⊆ W)
    {Z : Submodule ℂ (V → ℂ)} {U : Set V} (h : ∀ x ∈ U, ∃ B ∈ 𝓝 x, Kil Z B) : Kil Z U := by
  intro Φ hΦ hs
  have hcl : IsClosed (Function.support Φ) := by
    have := (hΦ.1.isOpen_fiber 0).isClosed_compl
    exact this
  have hK : IsCompact (Function.support Φ) := hΦ.2.isCompact.of_isClosed_subset hcl (subset_tsupport _)
  have : ∀ x : Function.support Φ, ∃ H : AddSubgroup V, IsOpen (H : Set V) ∧ Kil Z {y | y - x.1 ∈ H} := fun x => by
    obtain ⟨B, hB, hk⟩ := h x (hs x x.2)
    obtain ⟨H, o, -, s⟩ := hV _ (nhds_sub hB)
    exact ⟨H, o, fun Ψ hΨ h' => hk Ψ hΨ fun y hy => by simpa using s (h' y hy)⟩
  choose H o hk using this
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x : Function.support Φ => {y | y - x.1 ∈ H x})
    (fun x => (o x).preimage (continuous_id.sub continuous_const)) fun y hy => Set.mem_iUnion.2 ⟨⟨y, hy⟩, by simp⟩
  obtain ⟨W, hW, hi⟩ := exists_invar hΦ
  obtain ⟨H₀, o₀, c₀, s₀⟩ := hV (W ∩ ⋂ x ∈ t, (H x : Set V))
    (inter_mem hW ((biInter_finset_mem t).2 fun x _ => (o x).mem_nhds (H x).zero_mem))
  refine mem_of_cs o₀ hΦ (fun a ha => hi a (s₀ ha).1) Z fun y hy => ?_
  obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.1 (ht hy)
  refine hk x _ (cs_mem o₀ c₀ y) fun z hz => ?_
  have := (H x).add_mem (Set.mem_iInter₂.1 (s₀ (cs_ne hz)).2 x hx) hyx
  simpa using this

end Grp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {m n p : Type} [Fintype m] [Fintype n] [Fintype p]

def mb (m n : Type) (c : k) : AddSubgroup (Matrix m n k) where
  carrier := {b | ∀ i j, valuation k (b i j) ≤ valuation k c}
  add_mem' ha hb i j := (valuation k).map_add_le (ha i j) (hb i j)
  zero_mem' i j := by simp
  neg_mem' ha i j := by simpa using ha i j

theorem cont_unc : Continuous fun (S : Matrix m n k) (x : m × n) => S x.1 x.2 :=
  continuous_pi fun x => continuous_id.matrix_elem x.1 x.2

theorem cont_cur : Continuous fun (b : m × n → k) => (Matrix.of fun i j => b (i, j) : Matrix m n k) :=
  continuous_matrix fun i j => continuous_apply (i, j)

theorem mb_open {c : k} (hc : c ≠ 0) : IsOpen (mb m n c : Set (Matrix m n k)) := by
  have := (bx_open (S := m × n) hc).preimage (cont_unc (k := k))
  convert this using 1
  ext S
  exact ⟨fun h x => h x.1 x.2, fun h i j => h (i, j)⟩

theorem mb_compact (c : k) : IsCompact (mb m n c : Set (Matrix m n k)) := by
  have := (bx_compact (S := m × n) c).image (cont_cur (k := k))
  convert this using 1
  ext S
  exact ⟨fun h => ⟨fun x => S x.1 x.2, fun x => h x.1 x.2, rfl⟩, by rintro ⟨b, hb, rfl⟩ i j; exact hb (i, j)⟩

theorem mb_small {W : Set (Matrix m n k)} (hW : W ∈ 𝓝 (0 : Matrix m n k)) : ∃ c : k, c ≠ 0 ∧ (mb m n c : Set (Matrix m n k)) ⊆ W := by
  obtain ⟨c, hc, h⟩ := bx_small (S := m × n) ((cont_cur (k := k)).continuousAt.preimage_mem_nhds (x := 0) hW)
  exact ⟨c, hc, fun S hS => h (show (fun x : m × n => S x.1 x.2) ∈ bx (m × n) c from fun x => hS x.1 x.2)⟩

theorem mb_large (S : Matrix m n k) : ∃ c : k, 1 ≤ valuation k c ∧ S ∈ mb m n c := by
  obtain ⟨c, hc, h⟩ := bx_large (S := Option (m × n)) (isCompact_singleton (x := fun x => x.elim 1 fun x => S x.1 x.2))
  have := h rfl
  exact ⟨c, by simpa using this none, fun i j => this (some (i, j))⟩

theorem hV_mat : ∀ W ∈ 𝓝 (0 : Matrix m n k), ∃ H : AddSubgroup (Matrix m n k), IsOpen (H : Set (Matrix m n k)) ∧
    IsCompact (H : Set (Matrix m n k)) ∧ (H : Set (Matrix m n k)) ⊆ W := fun _ hW =>
  let ⟨c, hc, h⟩ := mb_small hW
  ⟨mb m n c, mb_open hc, mb_compact c, h⟩

theorem mb_mul {a b : k} {A : Matrix m n k} {B : Matrix n p k} (hA : A ∈ mb m n a) (hB : B ∈ mb n p b) : A * B ∈ mb m p (a * b) :=
  fun i j => by
    rw [Matrix.mul_apply]
    refine (valuation k).map_sum_le fun l _ => ?_
    rw [map_mul, map_mul]
    exact mul_le_mul' (hA i l) (hB l j)

theorem mb_mono {a b : k} (h : valuation k a ≤ valuation k b) {A : Matrix m n k} (hA : A ∈ mb m n a) : A ∈ mb m n b :=
  fun i j => (hA i j).trans h

theorem mb_smul {a b : k} (h : valuation k a ≤ 1) {A : Matrix m n k} (hA : A ∈ mb m n b) : a • A ∈ mb m n b := fun i j => by
  rw [Matrix.smul_apply, smul_eq_mul, map_mul]
  exact (mul_le_of_le_one_left' h).trans (hA i j)

variable [DecidableEq m] [DecidableEq n]

def lam (P : Matrix m m k) (Q : Matrix n n k) (c : k) : AddSubgroup (Matrix m n k) where
  carrier := {S | S ∈ mb m n c ∧ P * S ∈ mb m n c ∧ S * Q ∈ mb m n c ∧ P * S * Q ∈ mb m n c}
  add_mem' ha hb := by
    refine ⟨add_mem ha.1 hb.1, ?_, ?_, ?_⟩ <;> simp only [Matrix.mul_add, Matrix.add_mul]
    exacts [add_mem ha.2.1 hb.2.1, add_mem ha.2.2.1 hb.2.2.1, add_mem ha.2.2.2 hb.2.2.2]
  zero_mem' := by simp [zero_mem]
  neg_mem' ha := by simpa using ha

def idp (P : Matrix m m k) (x : k) : Matrix m m k := 1 + x • P

theorem fixk [T2Space k] {Z : Submodule ℂ (Matrix m n k → ℂ)} {U₀ : Set (Matrix m n k)} (hU : Kil Z U₀) {X₀ : Matrix m n k}
    {P : Matrix m n k → Matrix m m k} {Q : Matrix m n k → Matrix n n k} (cP : ContinuousAt P X₀) (cQ : ContinuousAt Q X₀)
    (P₀ : P X₀ * P X₀ = P X₀) (Q₀ : Q X₀ * Q X₀ = Q X₀) {l : kˣ} (hl : valuation k (l : k) = 1) {c : ℂ} (hc : c ≠ 1)
    {B₀ : Set (Matrix m n k)} (hB : B₀ ∈ 𝓝 X₀)
    (h : ∀ X ∈ B₀, X ∈ U₀ ∨ (P X * P X = P X ∧ Q X * Q X = Q X ∧ P X * X = X * Q X ∧ ∀ Φ ∈ SB (Matrix m n k),
      (fun S : Matrix m n k => Φ (idp (P X) ((l⁻¹ : kˣ) - 1) * S * idp (Q X) (l - 1))) - c • Φ ∈ Z)) :
    ∃ B ∈ 𝓝 X₀, Kil Z B := by
  obtain ⟨a, ha, hPa⟩ := mb_large (P X₀)
  obtain ⟨b, hb, hQb⟩ := mb_large (Q X₀)
  have a0 : a ≠ 0 := by rintro rfl; simp at ha
  have b0 : b ≠ 0 := by rintro rfl; simp at hb
  set e := (a * b)⁻¹ with he
  have e0 : e ≠ 0 := inv_ne_zero (mul_ne_zero a0 b0)
  have sm : ∀ c' : k, ∀ S ∈ mb m n (e * c'), S ∈ lam (P X₀) (Q X₀) c' := fun c' S hS => by
    have k1 : a * (e * c') * b = c' := by rw [he]; field_simp
    have k2 : valuation k (a * (e * c')) ≤ valuation k c' := by
      conv_rhs => rw [← k1, map_mul]
      exact le_mul_of_one_le_right' hb
    have k3 : valuation k (e * c' * b) ≤ valuation k c' := by
      conv_rhs => rw [← k1, mul_assoc, map_mul]
      exact le_mul_of_one_le_left' ha
    have k4 : valuation k (e * c') ≤ valuation k c' := le_trans (by rw [map_mul _ _ b]; exact le_mul_of_one_le_right' hb) k3
    exact ⟨mb_mono k4 hS, mb_mono k2 (mb_mul hPa hS), mb_mono k3 (mb_mul hS hQb), k1 ▸ mb_mul (mb_mul hPa hS) hQb⟩
  have lo : ∀ c' : k, c' ≠ 0 → IsOpen (lam (P X₀) (Q X₀) c' : Set (Matrix m n k)) := fun c' h0 =>
    AddSubgroup.isOpen_mono (H₁ := mb m n (e * c')) (sm c') (mb_open (mul_ne_zero e0 h0))
  have lc : ∀ c' : k, c' ≠ 0 → IsCompact (lam (P X₀) (Q X₀) c' : Set (Matrix m n k)) := fun c' h0 =>
    (mb_compact c').of_isClosed_subset (AddSubgroup.isClosed_of_isOpen _ (lo c' h0)) fun S hS => hS.1
  have sl : ∀ (c' x : k), valuation k x ≤ 1 → ∀ S ∈ lam (P X₀) (Q X₀) c', x • S ∈ lam (P X₀) (Q X₀) c' := fun c' x hx S hS => by
    refine ⟨mb_smul hx hS.1, ?_, ?_, ?_⟩ <;> simp only [Matrix.mul_smul, Matrix.smul_mul]
    exacts [mb_smul hx hS.2.1, mb_smul hx hS.2.2.1, mb_smul hx hS.2.2.2]
  have stL : ∀ (c' x : k) (P' : Matrix m m k), P' - P X₀ ∈ mb m m e → valuation k x ≤ 1 → ∀ S ∈ lam (P X₀) (Q X₀) c',
      idp P' x * S ∈ lam (P X₀) (Q X₀) c' := fun c' x P' hP hx S hS => by
    have : idp P' x * S = S + x • (P X₀ * S + (P' - P X₀) * S) := by
      simp [idp, Matrix.add_mul, Matrix.sub_mul]
    rw [this]
    refine add_mem hS (sl _ _ hx _ (add_mem ⟨hS.2.1, ?_, hS.2.2.2, ?_⟩ (sm _ _ (mb_mul hP hS.1))))
    · rw [← Matrix.mul_assoc, P₀]; exact hS.2.1
    · rw [← Matrix.mul_assoc, P₀]; exact hS.2.2.2
  have stR : ∀ (c' x : k) (Q' : Matrix n n k), Q' - Q X₀ ∈ mb n n e → valuation k x ≤ 1 → ∀ S ∈ lam (P X₀) (Q X₀) c',
      S * idp Q' x ∈ lam (P X₀) (Q X₀) c' := fun c' x Q' hQ hx S hS => by
    have : S * idp Q' x = S + x • (S * Q X₀ + S * (Q' - Q X₀)) := by
      simp [idp, Matrix.mul_add, Matrix.mul_sub]
    rw [this]
    refine add_mem hS (sl _ _ hx _ (add_mem ⟨hS.2.2.1, ?_, ?_, ?_⟩ (sm _ _ (mul_comm c' e ▸ mb_mul hS.1 hQ))))
    · rw [← Matrix.mul_assoc]; exact hS.2.2.2
    · rw [Matrix.mul_assoc, Q₀]; exact hS.2.2.1
    · rw [← Matrix.mul_assoc, Matrix.mul_assoc _ (Q X₀), Q₀]; exact hS.2.2.2
  have n1 : {X | P X - P X₀ ∈ mb m m e} ∈ 𝓝 X₀ :=
    (cP.sub continuousAt_const).preimage_mem_nhds ((mb_open e0).mem_nhds (by simp [zero_mem]))
  have n2 : {X | Q X - Q X₀ ∈ mb n n e} ∈ 𝓝 X₀ :=
    (cQ.sub continuousAt_const).preimage_mem_nhds ((mb_open e0).mem_nhds (by simp [zero_mem]))
  obtain ⟨r, r0, hr⟩ := mb_small (nhds_sub (inter_mem hB (inter_mem n1 n2)))
  refine ⟨{X | X - X₀ ∈ mb m n r}, ((mb_open r0).preimage (continuous_id.sub continuous_const)).mem_nhds (by simp [zero_mem]),
    fun Φ hΦ hs => ?_⟩
  obtain ⟨W, hW, hi⟩ := exists_invar hΦ
  obtain ⟨c', c0, hc'⟩ := mb_small (inter_mem hW ((mb_open r0).mem_nhds (zero_mem _)))
  refine mem_of_cs (lo c' c0) hΦ (fun S hS => hi S (hc' hS.1).1) Z fun y hy => ?_
  have inB : ∀ X, X - y ∈ lam (P X₀) (Q X₀) c' → X ∈ B₀ ∩ ({X | P X - P X₀ ∈ mb m m e} ∩ {X | Q X - Q X₀ ∈ mb n n e}) := fun X hX => by
    have := hr (add_mem (hc' hX.1).2 (hs y hy))
    simpa using this
  by_cases hU' : ∀ X, X - y ∈ lam (P X₀) (Q X₀) c' → X ∈ U₀
  · exact hU _ (cs_mem (lo c' c0) (lc c' c0) y) fun X hX => hU' X (cs_ne hX)
  push Not at hU'
  obtain ⟨X, hX, hXU⟩ := hU'
  obtain ⟨hX0, hX1, hX2⟩ := inB X hX
  obtain ⟨p2, q2, pq, hop⟩ := (h X hX0).resolve_left hXU
  have v1 : valuation k ((l : k) - 1) ≤ 1 := (valuation k).map_sub_le hl.le (by simp)
  have v2 : valuation k (((l⁻¹ : kˣ) : k) - 1) ≤ 1 := (valuation k).map_sub_le (by simp [hl]) (by simp)
  have l0 : (l : k) ≠ 0 := l.ne_zero
  have iP : idp (P X) (l - 1) * idp (P X) ((l⁻¹ : kˣ) - 1) = 1 := by
    simp only [idp, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_smul, Matrix.smul_mul, p2, smul_add, smul_smul,
      add_assoc, ← add_smul, Units.val_inv_eq_inv_val]
    rw [show (l : k) - 1 + (((l : k)⁻¹ - 1) + ((l : k)⁻¹ - 1) * (l - 1)) = 0 by field_simp; ring]; simp
  have iQ : idp (Q X) (l - 1) * idp (Q X) ((l⁻¹ : kˣ) - 1) = 1 := by
    simp only [idp, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_smul, Matrix.smul_mul, q2, smul_add, smul_smul,
      add_assoc, ← add_smul, Units.val_inv_eq_inv_val]
    rw [show (l : k) - 1 + (((l : k)⁻¹ - 1) + ((l : k)⁻¹ - 1) * (l - 1)) = 0 by field_simp; ring]; simp
  have fx : idp (P X) ((l⁻¹ : kˣ) - 1) * X * idp (Q X) (l - 1) = X := by
    have : idp (P X) ((l⁻¹ : kˣ) - 1) * X = X * idp (Q X) ((l⁻¹ : kˣ) - 1) := by
      simp [idp, Matrix.mul_add, Matrix.add_mul, pq]
    rw [this, Matrix.mul_assoc, mul_eq_one_comm.1 iQ, Matrix.mul_one]
  have e1 : (fun S : Matrix m n k => cs (lam (P X₀) (Q X₀) c') y (idp (P X) ((l⁻¹ : kˣ) - 1) * S * idp (Q X) (l - 1))) =
      cs (lam (P X₀) (Q X₀) c') y := by
    funext S
    have d : idp (P X) ((l⁻¹ : kˣ) - 1) * S * idp (Q X) (l - 1) - X =
        idp (P X) ((l⁻¹ : kˣ) - 1) * (S - X) * idp (Q X) (l - 1) := by
      rw [Matrix.mul_sub, Matrix.sub_mul, fx]
    have sh : ∀ T, T - y ∈ lam (P X₀) (Q X₀) c' ↔ T - X ∈ lam (P X₀) (Q X₀) c' := fun T =>
      ⟨fun hT => by simpa using sub_mem hT hX, fun hT => by simpa using add_mem hT hX⟩
    have : idp (P X) ((l⁻¹ : kˣ) - 1) * S * idp (Q X) (l - 1) - y ∈ lam (P X₀) (Q X₀) c' ↔
        S - y ∈ lam (P X₀) (Q X₀) c' := by
      rw [sh, sh, d]
      refine ⟨fun hT => ?_, fun hT => stR _ _ _ hX2 v1 _ (stL _ _ _ hX1 v2 _ hT)⟩
      have := stR _ _ _ hX2 v2 _ (stL _ _ _ hX1 v1 _ hT)
      rwa [← Matrix.mul_assoc, ← Matrix.mul_assoc, iP, Matrix.one_mul, Matrix.mul_assoc, iQ, Matrix.mul_one] at this
    classical
    simp only [cs, Set.indicator_apply, Set.mem_setOf_eq, this, Pi.one_apply]
  have := hop _ (cs_mem (lo c' c0) (lc c' c0) y)
  rw [e1] at this
  have h2 := Z.smul_mem (1 - c)⁻¹ this
  rwa [show cs (lam (P X₀) (Q X₀) c') y - c • cs (lam (P X₀) (Q X₀) c') y = (1 - c) • cs (lam (P X₀) (Q X₀) c') y by
    rw [sub_smul, one_smul], smul_smul, inv_mul_cancel₀ (sub_ne_zero.2 hc.symm), one_smul] at h2

end PositivityTheory.ThKG.LocalRamifiedLeviRestriction
end
end

section
noncomputable section

namespace PositivityTheory.ThKG.LocalRamifiedLeviRestriction

section
open Polynomial

theorem dixmier_aeval_injective {V : Type} [AddCommGroup V] [Module ℂ V] (T : Module.End ℂ V)
    (hT : ∀ c : ℂ, Function.Injective ⇑(T - c • (1 : Module.End ℂ V))) (p : ℂ[X]) (hp : p ≠ 0) :
    Function.Injective (aeval T p) := by
  have hs := C_leadingCoeff_mul_prod_multiset_X_sub_C (p := p) IsAlgClosed.card_roots_eq_natDegree
  have hlin : ∀ a : ℂ, aeval T (X - C a) = T - a • 1 := by
    intro a; simp [Algebra.algebraMap_eq_smul_one]
  have key : ∀ m : Multiset ℂ, Function.Injective (aeval T (m.map fun a => X - C a).prod) := by
    intro m
    induction m using Multiset.induction_on with
    | empty =>
      simp only [Multiset.map_zero, Multiset.prod_zero, map_one, Module.End.one_eq_id, LinearMap.id_coe]
      exact Function.injective_id
    | cons a m ih =>
      rw [Multiset.map_cons, Multiset.prod_cons, map_mul, Module.End.mul_eq_comp, LinearMap.coe_comp]
      refine Function.Injective.comp ?_ ih
      rw [hlin]; exact hT a
  rw [← hs, map_mul, Module.End.mul_eq_comp, LinearMap.coe_comp]
  refine Function.Injective.comp ?_ (key _)
  rw [aeval_C, Algebra.algebraMap_eq_smul_one]
  intro x y hxy
  simp only [LinearMap.smul_apply, Module.End.one_apply] at hxy
  exact smul_right_injective V (leadingCoeff_ne_zero.mpr hp) hxy

theorem dixmier_commutant_scalar (ι V : Type) [AddCommGroup V] [Module ℂ V] (ρ : ι → Module.End ℂ V)
    (hrank : Module.rank ℂ V ≤ Cardinal.aleph0)
    (hirr : ∀ N : Submodule ℂ V, (∀ i, ∀ x ∈ N, ρ i x ∈ N) → N = ⊥ ∨ N = ⊤)
    (T : Module.End ℂ V) (hT : ∀ i, T * ρ i = ρ i * T) : ∃ c : ℂ, T = c • 1 := by
  by_contra hne
  push_neg at hne
  have hcomm : ∀ c : ℂ, ∀ i, (T - c • 1) * ρ i = ρ i * (T - c • 1) := by
    intro c i; rw [sub_mul, mul_sub, hT i, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  have hinj : ∀ c : ℂ, Function.Injective ⇑(T - c • (1 : Module.End ℂ V)) := by
    intro c
    rw [← LinearMap.ker_eq_bot]
    rcases hirr (LinearMap.ker (T - c • 1)) (fun i x hx => by
      rw [LinearMap.mem_ker] at hx ⊢
      rw [← Module.End.mul_apply, hcomm c i, Module.End.mul_apply, hx, map_zero]) with h | h
    · exact h
    · exact absurd (sub_eq_zero.mp (LinearMap.ker_eq_top.mp h)) (hne c)
  obtain ⟨v₀, hv₀⟩ : ∃ v : V, v ≠ 0 := by
    by_contra h; push_neg at h
    exact hne 0 (LinearMap.ext fun v => (h _).trans (h _).symm)
  have hsurj : ∀ c : ℂ, Function.Surjective ⇑(T - c • (1 : Module.End ℂ V)) := by
    intro c
    rw [← LinearMap.range_eq_top]
    rcases hirr (LinearMap.range (T - c • 1)) (fun i x hx => by
      obtain ⟨y, rfl⟩ := hx
      exact ⟨ρ i y, by rw [← Module.End.mul_apply, hcomm c i, Module.End.mul_apply]⟩) with h | h
    · exfalso
      have h1 : (T - c • 1) v₀ ∈ LinearMap.range (T - c • 1) := LinearMap.mem_range_self _ _
      rw [h, Submodule.mem_bot] at h1
      exact hv₀ (hinj c (by rw [h1, map_zero]))
    · exact h
  let S : ℂ → V ≃ₗ[ℂ] V := fun c => LinearEquiv.ofBijective (T - c • 1) ⟨hinj c, hsurj c⟩
  let w : ℂ → V := fun c => (S c).symm v₀
  have hw : ∀ c, (T - c • (1 : Module.End ℂ V)) (w c) = v₀ := fun c => (S c).apply_symm_apply v₀
  have hlin : ∀ a : ℂ, aeval T (X - C a) = T - a • 1 := by
    intro a; simp [Algebra.algebraMap_eq_smul_one]
  have hli : LinearIndependent ℂ w := by
    rw [linearIndependent_iff']
    intro s g hsum i hi
    let q : ℂ → ℂ[X] := fun c => ∏ d ∈ s.erase c, (X - C d)
    have hq : ∀ c ∈ s, aeval T (∏ d ∈ s, (X - C d)) (w c) = aeval T (q c) v₀ := by
      intro c hc
      rw [← Finset.mul_prod_erase s _ hc, mul_comm, map_mul, Module.End.mul_apply, hlin, hw]
    have h0 : aeval T (∑ c ∈ s, g c • q c) v₀ = 0 := by
      have h2 := congrArg (aeval T (∏ d ∈ s, (X - C d))) hsum
      rw [map_zero, map_sum] at h2
      rw [map_sum, LinearMap.sum_apply, ← h2]
      refine Finset.sum_congr rfl fun c hc => ?_
      rw [LinearMap.map_smul, hq c hc, map_smul, LinearMap.smul_apply]
    have hp0 : ∑ c ∈ s, g c • q c = 0 := by
      by_contra hp
      exact hv₀ (dixmier_aeval_injective T hinj _ hp (by rw [h0, map_zero]))
    have h3 := congrArg (Polynomial.eval i) hp0
    rw [eval_finset_sum, Finset.sum_eq_single i] at h3
    · simp only [eval_smul, q, eval_prod, eval_sub, eval_X, eval_C, smul_eq_mul, eval_zero] at h3
      rcases mul_eq_zero.mp h3 with h | h
      · exact h
      · exfalso
        rw [Finset.prod_eq_zero_iff] at h
        obtain ⟨d, hd, hd0⟩ := h
        exact (Finset.ne_of_mem_erase hd) (sub_eq_zero.mp hd0).symm
    · intro c hc hci
      simp only [eval_smul, q, eval_prod, eval_sub, eval_X, eval_C, smul_eq_mul]
      rw [Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hci, hi⟩) (sub_self i), mul_zero]
    · intro h; exact absurd hi h
  have h4 := hli.cardinal_le_rank
  rw [Cardinal.mk_complex] at h4
  exact absurd (h4.trans hrank) (not_le.mpr Cardinal.aleph0_lt_continuum)

end

section
open PositivityTheory.KCo GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen Matrix Topology GlobalTheory.SplitFlip

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ}

theorem irrF' (hB : GlobalTheory.Published.BernsteinUnitaryProductIrreducible) {ν α : kˣ →* ℂˣ} (hnd : n ≤ d) (hν : USm ν)
    (N : Submodule ℂ (Matrix (Fin n) (Fin d) k → ℂ)) (hA : augF n d ν α ≤ N)
    (hN : ∀ h : GL (Fin d) k, ∀ Φ ∈ N, Φ ∈ GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k) → omB ν α 1 h Φ ∈ N) :
    (∀ Φ, Full Φ → Φ ∈ N) ∨ ∀ Φ ∈ N, Full Φ → Φ ∈ augF n d ν α := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hnd
  have hμ : IsSmoothChar ν⁻¹ := IsSmoothChar.inv hν.2
  obtain ⟨E⟩ := GlobalTheory.T.omega_equiv_induced_fibre k (Fin n) (Fin (n + t)) (Fin n) (Fin t) (stdSum rfl) n (Fintype.card_fin n).symm ν⁻¹ hμ
  have hR : twRel ((omegaOn (Fin n) (Fin (n + t)) ν⁻¹ {n}).comp (MonoidHom.inl _ _)) 1 ≤
      (augF n (n + t) ν α).comap extZ := Submodule.span_le.2 (by
    rintro _ ⟨g, φ, rfl⟩
    refine Submodule.subset_span ⟨g, extZ φ, ⟨extZ_mem φ, fun Y hY => extZ_neg φ (by rwa [rank_transpose])⟩, ?_⟩
    rw [MonoidHom.one_apply, Units.val_one, one_smul, map_sub]
    congr 1
    refine funext fun Y => (extZ_act _ g 1 φ Y).trans ?_
    have n1 : nabs k 1 = 1 := by simp [nabs]
    simp [omB, omChar, apow, val_absPow, n1])
  rcases irr_equiv E (irr_ind hB n t hμ (fun y => by simp [hν.1 y])) (N.comap extZ) (hR.trans (Submodule.comap_mono hA)) (by
    intro h φ hf
    have h1 := hN (invT h) _ hf (extZ_mem φ)
    rw [Submodule.mem_comap]
    have c0 : (α (gdet (invT h)) : ℂ) * apow (gdet (invT h)) ((n : ℂ) / 2) ≠ 0 :=
      mul_ne_zero (Units.ne_zero _) (Units.ne_zero (absPow k ((n : ℂ) / 2) (gdet (invT h))))
    convert N.smul_mem ((omChar (Fin n) (Fin (n + t)) ν⁻¹ (1, h) : ℂ) /
      ((α (gdet (invT h)) : ℂ) * apow (gdet (invT h)) ((n : ℂ) / 2))) h1 using 1
    funext Y
    have e1 : omB ν α 1 (invT h) (extZ φ) Y = (α (gdet (invT h)) : ℂ) * apow (gdet (invT h)) ((n : ℂ) / 2) *
        extZ φ ((1 : GL (Fin n) k).valᵀ * Y * (invT h).val) := by
      simp [omB, apow, nabs]
    rw [extZ_act, Pi.smul_apply, e1, smul_eq_mul, ← mul_assoc, div_mul_cancel₀ _ c0]) with h | h
  · refine Or.inl fun Φ hΦ => ?_
    obtain ⟨φ, rfl⟩ := exists_extZ hΦ
    exact (h ▸ Submodule.mem_top : φ ∈ N.comap extZ)
  · refine Or.inr fun Φ hm hΦ => ?_
    obtain ⟨φ, rfl⟩ := exists_extZ hΦ
    exact hR (h hm)

end

theorem rank_SB (V : Type) [TopologicalSpace V] [SecondCountableTopology V] [T2Space V] :
    Module.rank ℂ (GlobalTheory.WeilM.SB V) ≤ Cardinal.aleph0 := by
  classical
  have hc : {K : Set V | IsCompact K ∧ IsOpen K}.Countable := by
    refine ((Set.countable_setOf_finite_subset (TopologicalSpace.countable_countableBasis V)).image Set.sUnion).mono ?_
    rintro K ⟨h1, h2⟩
    obtain ⟨S, hS, rfl⟩ := (TopologicalSpace.isBasis_countableBasis V).open_eq_sUnion h2
    obtain ⟨T, hT, hf, hcov⟩ := h1.elim_finite_subcover_image (b := S) (c := id)
      (fun s hs => (TopologicalSpace.isBasis_countableBasis V).isOpen (hS hs)) (by rw [Set.sUnion_eq_biUnion]; rfl)
    refine ⟨T, ⟨hf, hT.trans hS⟩, subset_antisymm (Set.sUnion_mono hT) ?_⟩
    rw [Set.sUnion_eq_biUnion (s := T)]; exact hcov
  have hle : GlobalTheory.WeilM.SB V ≤ Submodule.span ℂ ((fun K : Set V => K.indicator (1 : V → ℂ)) '' {K | IsCompact K ∧ IsOpen K}) := by
    intro f hf
    have hfin : (f '' tsupport f).Finite := by
      haveI : CompactSpace (tsupport f) := isCompact_iff_compactSpace.1 hf.2.isCompact
      have h2 := (hf.1.comp_continuous (continuous_subtype_val (p := (· ∈ tsupport f)))).range_finite
      rwa [Set.range_comp, Subtype.range_coe_subtype, Set.setOf_mem_eq] at h2
    have e : f = ∑ c ∈ hfin.toFinset.erase 0, c • (f ⁻¹' {c}).indicator (1 : V → ℂ) := by
      funext y
      rw [Finset.sum_apply, Finset.sum_eq_single (f y)]
      · simp
      · intro c _ hc
        simp [Set.indicator_apply, hc.symm]
      · intro h
        have : f y = 0 := by
          by_contra h0
          exact h (Finset.mem_erase.2 ⟨h0, hfin.mem_toFinset.2 ⟨y, subset_tsupport _ h0, rfl⟩⟩)
        simp [this]
    rw [e]
    refine Submodule.sum_mem _ fun c hc => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ⟨?_, hf.1 _⟩, rfl⟩)
    refine hf.2.isCompact.of_isClosed_subset (hf.1.isClopen_fiber c).1 fun y hy => subset_tsupport _ ?_
    rw [Function.mem_support, show f y = c from hy]
    exact (Finset.mem_erase.1 hc).1
  exact (Submodule.rank_mono hle).trans ((rank_span_le _).trans (Cardinal.mk_le_aleph0_iff.2 (hc.image _).to_subtype))

end PositivityTheory.ThKG.LocalRamifiedLeviRestriction
end
end

section
noncomputable section

namespace PositivityTheory.ThKG.LocalRamifiedLeviRestriction

open GlobalTheory.WeilM Filter Topology ValuativeRel Matrix PositivityTheory.KCo GlobalTheory.SplitFlip

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [T2Space k]
  {n d d₁ : ℕ} (e : Fin d₁ ⊕ Bool ≃ Fin d) {W : Type} [AddCommGroup W] [Module ℂ W]

def RI {m : ℕ} (Y : Matrix (Fin n) (Fin m) k) : Prop := ∃ R : Matrix (Fin m) (Fin n) k, Y * R = 1

theorem ri_iff {m : ℕ} {Y : Matrix (Fin n) (Fin m) k} : RI Y ↔ Y.rank = n := by
  constructor
  · rintro ⟨R, h⟩
    refine le_antisymm (rank_le_height Y) ?_
    have := rank_mul_le_left Y R
    rwa [h, rank_one, Fintype.card_fin] at this
  · intro h
    have hs : LinearMap.range Y.mulVecLin = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [Module.finrank_fin_fun]; exact h)
    choose u hu using fun j : Fin n => LinearMap.range_eq_top.1 hs (Pi.single j 1)
    refine ⟨Matrix.of fun i j => u j i, Matrix.ext fun i j => ?_⟩
    have := congrFun (hu j) i
    rw [Pi.single_apply] at this
    rw [Matrix.one_apply]
    exact this

theorem not_ri {m : ℕ} {Y : Matrix (Fin n) (Fin m) k} (h : ¬ RI Y) : ∃ c : Fin n → k, c ≠ 0 ∧ c ᵥ* Y = 0 := by
  by_contra h'
  push Not at h'
  have : Function.Injective Y.vecMul := fun a b hab => by
    by_contra hne
    exact h' (a - b) (sub_ne_zero.2 hne) (by rw [sub_vecMul]; exact sub_eq_zero.2 hab)
  exact h (ri_iff.2 (by rw [(vecMul_injective_iff.1 this).rank_matrix, Fintype.card_fin]))

theorem ri_of_det {m : ℕ} {Y : Matrix (Fin n) (Fin m) k} {R : Matrix (Fin m) (Fin n) k} (h : (Y * R).det ≠ 0) : RI Y :=
  ⟨R * (Y * R)⁻¹, by rw [← Matrix.mul_assoc, mul_nonsing_inv _ (Ne.isUnit h)]⟩

theorem det_nhds {m : ℕ} {Y : Matrix (Fin n) (Fin m) k} {R : Matrix (Fin m) (Fin n) k} (h : Y * R = 1) :
    {X : Matrix (Fin n) (Fin m) k | (X * R).det ≠ 0} ∈ 𝓝 Y :=
  (isOpen_ne_fun (continuous_id.matrix_mul continuous_const).matrix_det continuous_const).mem_nhds (by simp [h])

def mid (Y : Matrix (Fin n) (Fin d) k) : Matrix (Fin n) (Fin d₁) k := Y.submatrix id fun s => e (.inl s)

def cl (t : Bool) (Y : Matrix (Fin n) (Fin d) k) : Fin n → k := fun i => Y i (e (.inr t))

def InP (h : Matrix (Fin d) (Fin d) k) : Prop :=
  (∀ i, i ≠ e (.inr false) → h i (e (.inr false)) = 0) ∧ valuation k (h (e (.inr false)) (e (.inr false))) = 1 ∧
    valuation k (h (e (.inr true)) (e (.inr true))) = 1 ∧
    (∀ s s', h (e (.inl s)) (e (.inl s')) = (1 : Matrix (Fin d₁) (Fin d₁) k) s s') ∧ ∀ s, h (e (.inr true)) (e (.inl s)) = 0

structure Inv (ν : kˣ →* ℂˣ) (L : (Matrix (Fin n) (Fin d) k → ℂ) →ₗ[ℂ] W) : Prop where
  left : ∀ g : GL (Fin n) k, ∀ Φ ∈ SB (Matrix (Fin n) (Fin d) k), L (omB ν 1 g 1 Φ) = L Φ
  right : ∀ h, InP e h → ∀ Φ ∈ SB (Matrix (Fin n) (Fin d) k), (fun Y : Matrix (Fin n) (Fin d) k => Φ (Y * h)) ∈ SB (Matrix (Fin n) (Fin d) k) ∧
    L (fun Y : Matrix (Fin n) (Fin d) k => Φ (Y * h)) = L Φ

variable {e} {ν : kˣ →* ℂˣ} {L : (Matrix (Fin n) (Fin d) k → ℂ) →ₗ[ℂ] W}

theorem Inv.op (hL : Inv e ν L) {l : kˣ} (hl : valuation k (l : k) = 1) {x c : Fin n → k} (hc : c ⬝ᵥ x = 1)
    {h : Matrix (Fin d) (Fin d) k} (hh : InP e h) (Φ) (hΦ : Φ ∈ SB (Matrix (Fin n) (Fin d) k)) :
    (fun S : Matrix (Fin n) (Fin d) k => Φ (idp (vecMulVec x c) ((l⁻¹ : kˣ) - 1) * S * h)) - (ν l : ℂ) • Φ ∈ LinearMap.ker L := by
  have hd : (idp (vecMulVec x c) ((l⁻¹ : kˣ) - 1))ᵀ.det = (l⁻¹ : kˣ) := by
    rw [det_transpose, idp, ← smul_vecMulVec, vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow, dotProduct_smul, hc]
    simp
  let g : GL (Fin n) k := GeneralLinearGroup.mkOfDetNeZero _ (hd ▸ (l⁻¹).ne_zero)
  have hg : gdet g = l⁻¹ := Units.ext hd
  obtain ⟨s, e1⟩ := hL.right h hh Φ hΦ
  have gv : g.valᵀ = idp (vecMulVec x c) ((l⁻¹ : kˣ) - 1) := transpose_transpose _
  have e3 : omB ν 1 g 1 (fun Y : Matrix (Fin n) (Fin d) k => Φ (Y * h)) = ((ν l)⁻¹ : ℂ) • fun S : Matrix (Fin n) (Fin d) k => Φ (idp (vecMulVec x c) ((l⁻¹ : kˣ) - 1) * S * h) := by
    funext Y
    have : apow l⁻¹ ((d : ℂ) / 2) = 1 := apow_of_valuation_eq_one (by simp [hl]) _
    simp only [omB, hg, gv, Fintype.card_fin, this]
    simp
  have e2 := (congrArg L e3).symm.trans (hL.left g _ s)
  rw [map_smul, e1] at e2
  rw [LinearMap.mem_ker, map_sub, map_smul, ← e2, smul_smul, mul_inv_cancel₀ (Units.ne_zero _), one_smul, sub_self]

theorem idem_vmv {m : Type} [Fintype m] {x c : m → k} (hc : c ⬝ᵥ x = 1) : vecMulVec x c * vecMulVec x c = vecMulVec x c := by
  rw [vecMulVec_mul_vecMulVec, hc, one_smul]

theorem fix_col (hL : Inv e ν L) {l : kˣ} (hl : valuation k (l : k) = 1) (hν : ν l ≠ 1) {U₀} (hU : Kil (LinearMap.ker L) U₀) (t : Bool)
    {X₀ : Matrix (Fin n) (Fin d) k} {c : Matrix (Fin n) (Fin d) k → Fin n → k} (cc : ContinuousAt c X₀) (h0 : c X₀ ⬝ᵥ cl e t X₀ = 1)
    {B₀} (hB : B₀ ∈ 𝓝 X₀) (h : ∀ X ∈ B₀, X ∈ U₀ ∨ (c X ⬝ᵥ cl e t X = 1 ∧
      InP e (idp (vecMulVec (Pi.single (e (.inr t)) 1) (c X ᵥ* X)) (l - 1)))) : ∃ B ∈ 𝓝 X₀, Kil (LinearMap.ker L) B := by
  have q : ∀ X, c X ⬝ᵥ cl e t X = 1 → (c X ᵥ* X) ⬝ᵥ Pi.single (e (.inr t)) 1 = 1 := fun X hX => by
    rw [dotProduct_single, mul_one]; exact hX
  refine fixk hU (P := fun X => vecMulVec (cl e t X) (c X)) (Q := fun X => vecMulVec (Pi.single (e (.inr t)) 1) (c X ᵥ* X))
    ?_ ?_ (idem_vmv h0) (idem_vmv (q _ h0)) hl (c := ν l) (fun h => hν (Units.ext h)) hB fun X hX => (h X hX).imp_right fun ⟨h1, h2⟩ =>
      ⟨idem_vmv h1, idem_vmv (q _ h1), ?_, hL.op hl h1 h2⟩
  · refine continuousAt_pi.2 fun i => continuousAt_pi.2 fun j => ?_
    exact (continuous_id.matrix_elem i _).continuousAt.mul (continuousAt_pi.1 cc j)
  · refine continuousAt_pi.2 fun i => continuousAt_pi.2 fun j => continuousAt_const.mul ?_
    change ContinuousAt (fun y : Matrix (Fin n) (Fin d) k => ∑ r, c y r * y r j) X₀
    exact tendsto_finset_sum Finset.univ fun r _ => (continuousAt_pi.1 cc r).mul (continuous_id.matrix_elem r j).continuousAt
  · rw [vecMulVec_mul, mul_vecMulVec, mulVec_single_one]
    rfl

theorem kil_empty {V : Type} [TopologicalSpace V] (Z : Submodule ℂ (V → ℂ)) : Kil Z ∅ := fun Φ _ h => by
  rw [show Φ = 0 from funext fun y => by by_contra h'; exact h y h']
  exact zero_mem _

theorem kil_one (hL : Inv e ν L) {l : kˣ} (hl : valuation k (l : k) = 1) (hν : ν l ≠ 1) :
    Kil (LinearMap.ker L) {Y | cl e false Y ≠ 0} := by
  refine kil_loc hV_mat fun X₀ hX => ?_
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hX
  have ci : Continuous fun X : Matrix (Fin n) (Fin d) k => cl e false X i := continuous_id.matrix_elem i _
  have k1 : ∀ X : Matrix (Fin n) (Fin d) k, cl e false X i ≠ 0 →
      (Pi.single i (cl e false X i)⁻¹ : Fin n → k) ⬝ᵥ cl e false X = 1 := fun X h => by
    rw [single_dotProduct, inv_mul_cancel₀ h]
  refine fix_col hL hl hν (kil_empty _) false (c := fun X => Pi.single i (cl e false X i)⁻¹) ?_ (k1 _ hi)
    ((isOpen_ne_fun ci continuous_const).mem_nhds hi) fun X hX => Or.inr ⟨k1 X hX, ?_, ?_, ?_, ?_, ?_⟩
  · exact (continuous_single (A := fun _ : Fin n => k) i).continuousAt.comp (ci.continuousAt.inv₀ hi)
  · intro r hr
    simp [idp, vecMulVec_apply, hr]
  · have : ((Pi.single i (cl e false X i)⁻¹ : Fin n → k) ᵥ* X) (e (.inr false)) = 1 := k1 X hX
    simp only [idp, vecMulVec_apply, Matrix.add_apply, Matrix.smul_apply, this]
    simp [hl]
  · simp [idp, vecMulVec_apply]
  · intro s s'
    simp [idp, vecMulVec_apply, Matrix.one_apply]
  · intro s
    simp [idp, vecMulVec_apply]

theorem kil_full (hL : Inv e ν L) {l : kˣ} (hl : valuation k (l : k) = 1) (hν : ν l ≠ 1)
    (h2 : Kil (LinearMap.ker L) {Y | RI (mid e Y)}) : Kil (LinearMap.ker L) {Y | RI Y} := by
  have h12 : Kil (LinearMap.ker L) {Y | cl e false Y ≠ 0 ∨ RI (mid e Y)} := by
    refine kil_loc hV_mat fun X hX => hX.elim (fun h => ⟨_, ?_, kil_one hL hl hν⟩) fun ⟨R, h⟩ => ⟨_, ?_, h2⟩
    · exact (isOpen_ne_fun (continuous_pi fun i => continuous_id.matrix_elem i _) continuous_const).mem_nhds h
    · have cm : Continuous (mid e : Matrix (Fin n) (Fin d) k → _) := continuous_id.matrix_submatrix _ _
      exact mem_of_superset (cm.continuousAt.preimage_mem_nhds (det_nhds h)) fun Y hY => ri_of_det hY
  refine kil_loc hV_mat fun X₀ ⟨R, hR⟩ => ?_
  have key : ∀ X : Matrix (Fin n) (Fin d) k, (X * R).det ≠ 0 → ¬ (cl e false X ≠ 0 ∨ RI (mid e X)) →
      (R (e (.inr true)) ᵥ* (X * R)⁻¹) ᵥ* X = Pi.single (e (.inr true)) 1 := fun X hd hX => by
    push Not at hX
    obtain ⟨c, c0, hc⟩ := not_ri hX.2
    have r : c ᵥ* X = Pi.single (e (.inr true)) ((c ᵥ* X) (e (.inr true))) := by
      funext j
      obtain ⟨j, rfl⟩ := e.surjective j
      rcases j with s | _ | _
      · rw [Pi.single_eq_of_ne (by simp)]
        exact congrFun hc s
      · have : (c ᵥ* X) (e (.inr false)) = c ⬝ᵥ cl e false X := rfl
        simp [this, hX.1]
      · simp
    set a := (c ᵥ* X) (e (.inr true))
    have e1 : c = a • (R (e (.inr true)) ᵥ* (X * R)⁻¹) := by
      conv_lhs => rw [← vecMul_one c, ← mul_nonsing_inv _ (Ne.isUnit hd), ← vecMul_vecMul, ← vecMul_vecMul, r, single_vecMul]
      rw [smul_vecMul]; rfl
    have a0 : a ≠ 0 := fun h => c0 (by rw [e1, h, zero_smul])
    apply smul_right_injective _ a0
    simp only
    rw [← smul_vecMul, ← e1, r, ← Pi.single_smul, smul_eq_mul, mul_one]
  by_cases h0 : cl e false X₀ ≠ 0 ∨ RI (mid e X₀)
  · obtain ⟨B, hB, hk⟩ : ∃ B ∈ 𝓝 X₀, B ⊆ {Y | cl e false Y ≠ 0 ∨ RI (mid e Y)} := by
      refine h0.elim (fun h => ⟨_, ?_, fun _ => Or.inl⟩) fun ⟨R, h⟩ => ⟨_, ?_, fun _ => Or.inr⟩
      · exact (isOpen_ne_fun (continuous_pi fun i => continuous_id.matrix_elem i _) continuous_const).mem_nhds h
      · have cm : Continuous (mid e : Matrix (Fin n) (Fin d) k → _) := continuous_id.matrix_submatrix _ _
        exact mem_of_superset (cm.continuousAt.preimage_mem_nhds (det_nhds h)) fun Y hY => ri_of_det hY
    exact ⟨B, hB, fun Φ hΦ hs => h12 Φ hΦ fun y hy => hk (hs y hy)⟩
  have k1 : ∀ X : Matrix (Fin n) (Fin d) k, (X * R).det ≠ 0 → ¬ (cl e false X ≠ 0 ∨ RI (mid e X)) →
      (R (e (.inr true)) ᵥ* (X * R)⁻¹) ⬝ᵥ cl e true X = 1 := fun X hd hX => by
    have := congrFun (key X hd hX) (e (.inr true))
    rwa [Pi.single_eq_same] at this
  refine fix_col hL hl hν h12 true (c := fun X => R (e (.inr true)) ᵥ* (X * R)⁻¹) ?_ (k1 _ (by simp [hR]) h0) (det_nhds hR)
    fun X hX => ?_
  · have c1 : ContinuousAt (fun X : Matrix (Fin n) (Fin d) k => (X * R)⁻¹) X₀ :=
      ContinuousAt.comp (f := fun X : Matrix (Fin n) (Fin d) k => X * R) (continuousAt_matrix_inv _ (by
        rw [hR, det_one, Ring.inverse_eq_inv']; exact continuousAt_inv₀ one_ne_zero))
        (continuous_id.matrix_mul continuous_const).continuousAt
    exact ContinuousAt.comp (f := fun X : Matrix (Fin n) (Fin d) k => (X * R)⁻¹)
      (continuous_const.matrix_vecMul continuous_id).continuousAt c1
  · by_cases h : cl e false X ≠ 0 ∨ RI (mid e X)
    · exact Or.inl h
    refine Or.inr ⟨k1 X hX h, ?_⟩
    rw [key X hX h]
    refine ⟨fun r hr => ?_, ?_, ?_, fun s s' => ?_, fun s => ?_⟩ <;> simp [idp, vecMulVec_apply, Matrix.one_apply, *]

end PositivityTheory.ThKG.LocalRamifiedLeviRestriction
end
end

section
noncomputable section

namespace PositivityTheory.ThKG.LocalRamifiedLeviRestriction

open GlobalTheory.WeilM Filter Topology ValuativeRel Matrix PositivityTheory.KCo GlobalTheory.SplitFlip

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [T2Space k]
  {n d d₁ : ℕ} (e : Fin d₁ ⊕ Bool ≃ Fin d) {W : Type} [AddCommGroup W] [Module ℂ W]

def tn (ψ : Matrix (Fin n) (Fin d₁) k → ℂ) (f f' : (Fin n → k) → ℂ) : Matrix (Fin n) (Fin d) k → ℂ :=
  fun Y => ψ (mid e Y) * f (cl e false Y) * f' (cl e true Y)

def tn₁ (f f' : (Fin n → k) → ℂ) : (Matrix (Fin n) (Fin d₁) k → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ) where
  toFun ψ := tn e ψ f f'
  map_add' _ _ := funext fun _ => by simp [tn, add_mul]
  map_smul' _ _ := funext fun _ => by simp [tn, mul_assoc]

def tn₃ (ψ : Matrix (Fin n) (Fin d₁) k → ℂ) (f : (Fin n → k) → ℂ) : ((Fin n → k) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ) where
  toFun f' := tn e ψ f f'
  map_add' _ _ := funext fun _ => by simp [tn, mul_add]
  map_smul' _ _ := funext fun _ => by simp [tn, mul_left_comm]

def one (n : ℕ) : (Fin n → k) → ℂ := cs (bx (Fin n) (1 : k)) 0

def blk (g : Matrix (Fin d₁) (Fin d₁) k) : Matrix (Fin d) (Fin d) k := reindex e e (fromBlocks g 0 0 1)

variable {e} {ν : kˣ →* ℂˣ} {L : (Matrix (Fin n) (Fin d) k → ℂ) →ₗ[ℂ] W}

theorem one_sb : (one n : (Fin n → k) → ℂ) ∈ SB (Fin n → k) := by
  unfold one
  exact cs_mem (V := Fin n → k) (H := bx (Fin n) (1 : k)) (bx_open (one_ne_zero' k)) (bx_compact (1 : k)) 0

theorem cm : Continuous (mid e : Matrix (Fin n) (Fin d) k → _) := continuous_id.matrix_submatrix _ _

theorem cc (t : Bool) : Continuous (cl e t : Matrix (Fin n) (Fin d) k → _) := continuous_pi fun i => continuous_id.matrix_elem i _

theorem tn_mem {ψ : Matrix (Fin n) (Fin d₁) k → ℂ} {f f' : (Fin n → k) → ℂ} (h : ψ ∈ SB _) (hf : f ∈ SB _) (hf' : f' ∈ SB _) :
    tn e ψ f f' ∈ SB _ := by
  refine ⟨((h.1.comp_continuous cm).mul (hf.1.comp_continuous (cc false))).mul (hf'.1.comp_continuous (cc true)), ?_⟩
  let a : Matrix (Fin n) (Fin d₁) k × (Fin n → k) × (Fin n → k) → Matrix (Fin n) (Fin d) k := fun x =>
    Matrix.of fun i j => Sum.elim (x.1 i) (fun t => cond t (x.2.2 i) (x.2.1 i)) (e.symm j)
  have ca : Continuous a := continuous_matrix fun i j => by
    simp only [a, Matrix.of_apply]
    rcases e.symm j with s | _ | _
    · exact continuous_fst.matrix_elem i s
    · exact (continuous_apply i).comp (continuous_fst.comp continuous_snd)
    · exact (continuous_apply i).comp (continuous_snd.comp continuous_snd)
  refine HasCompactSupport.intro ((h.2.isCompact.prod (hf.2.isCompact.prod hf'.2.isCompact)).image ca) fun Y hY => ?_
  by_contra h0
  refine hY ⟨(mid e Y, cl e false Y, cl e true Y), ⟨subset_tsupport _ (left_ne_zero_of_mul (left_ne_zero_of_mul h0)),
    subset_tsupport _ (right_ne_zero_of_mul (left_ne_zero_of_mul h0)), subset_tsupport _ (right_ne_zero_of_mul h0)⟩, ?_⟩
  ext i j
  obtain ⟨j, rfl⟩ := e.surjective j
  rcases j with s | _ | _ <;> simp [a, mid, cl]

theorem sum_e (a : Fin d → k) : ∑ j, a j = ∑ s, a (e (.inl s)) + (a (e (.inr true)) + a (e (.inr false))) := by
  rw [← e.sum_comp, Fintype.sum_sum_type, Fintype.sum_bool]

theorem trans_inv (hL : Inv e ν L) {ψ : Matrix (Fin n) (Fin d₁) k → ℂ} (h : Full ψ) {f f' : (Fin n → k) → ℂ} (hf : f ∈ SB _)
    (hf' : f' ∈ SB _) (v : Fin n → k) : L (tn e ψ f fun x => f' (x + v)) = L (tn e ψ f f') := by
  obtain ⟨U, hU, hi⟩ := exists_invar hf'
  have : Kil (LinearMap.ker (L ∘ₗ (tn₁ e f (fun x => f' (x + v)) - tn₁ e f f'))) {Z | RI Z} := by
    refine kil_loc hV_mat fun Z₀ ⟨R, hR⟩ => ⟨{Z | v - Z *ᵥ (R *ᵥ v) ∈ U}, ?_, fun φ hφ hs => ?_⟩
    · exact (continuous_const.sub (continuous_id.matrix_mulVec continuous_const)).continuousAt.preimage_mem_nhds (by
        simpa [mulVec_mulVec, hR] using hU)
    let w : Fin d → k := fun j => Sum.elim (R *ᵥ v) 0 (e.symm j)
    let g : Matrix (Fin d) (Fin d) k := 1 + vecMulVec w (Pi.single (e (.inr true)) 1)
    have hg : InP e g := by
      refine ⟨fun r hr => ?_, ?_, ?_, fun s s' => ?_, fun s => ?_⟩ <;> simp [g, w, vecMulVec_apply, Matrix.one_apply, *]
    have e1 := (hL.right g hg _ (tn_mem (e := e) hφ hf hf')).2
    rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.sub_apply, map_sub, sub_eq_zero]
    refine Eq.trans (congrArg L (funext fun Y => ?_)) e1
    have yw : Y *ᵥ w = mid e Y *ᵥ (R *ᵥ v) := funext fun i => by
      simp only [mulVec, dotProduct]; rw [sum_e (e := e)]; simp [w, mid, mulVec, dotProduct]
    have yg : Y * g = Y + vecMulVec (mid e Y *ᵥ (R *ᵥ v)) (Pi.single (e (.inr true)) 1) := by
      rw [Matrix.mul_add, Matrix.mul_one, mul_vecMulVec, yw]
    have m1 : mid e (Y * g) = mid e Y := by ext i s; rw [yg]; simp [mid, vecMulVec_apply]
    have m2 : cl e false (Y * g) = cl e false Y := by ext i; rw [yg]; simp [cl, vecMulVec_apply]
    have m3 : cl e true (Y * g) = cl e true Y + mid e Y *ᵥ (R *ᵥ v) := by ext i; rw [yg]; simp [cl, vecMulVec_apply]
    change φ _ * f _ * f' _ = φ _ * f _ * f' _
    rw [m1, m2, m3]
    by_cases h0 : φ (mid e Y) = 0
    · simp [h0]
    · rw [← hi _ (hs _ h0) (cl e true Y + mid e Y *ᵥ (R *ᵥ v))]
      congr 2
      abel
  have := this ψ h.1 fun Z hZ => ri_iff.2 (by by_contra h'; exact hZ (h.2 Z h'))
  rwa [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.sub_apply, map_sub, sub_eq_zero] at this

theorem comp_mem {f : (Fin n → k) → ℂ} (hf : f ∈ SB _) (g : GL (Fin n) k) : (fun x => f (g.val *ᵥ x)) ∈ SB (Fin n → k) := by
  let H : (Fin n → k) ≃ₜ (Fin n → k) :=
    { toFun := fun x => g.val *ᵥ x, invFun := fun x => (g⁻¹).val *ᵥ x, left_inv := fun x => by simp [mulVec_mulVec],
      right_inv := fun x => by simp [mulVec_mulVec], continuous_toFun := continuous_const.matrix_mulVec continuous_id,
      continuous_invFun := continuous_const.matrix_mulVec continuous_id }
  exact ⟨hf.1.comp_continuous H.continuous, hf.2.comp_homeomorph H⟩

theorem mod_inv (hL : Inv e ν L) {ψ : Matrix (Fin n) (Fin d₁) k → ℂ} (h : Full ψ) {f f' : (Fin n → k) → ℂ} (hf : f ∈ SB _)
    (hf' : f' ∈ SB _) (g : GL (Fin n) k) :
    ((GlobalTheory.SplitWeil.nabs k (GeneralLinearGroup.det g) : ℝ) : ℂ) • L (tn e ψ f fun x => f' (g.val *ᵥ x)) = L (tn e ψ f f') := by
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro m
  rw [map_sub, map_smul, sub_eq_zero]
  exact invariant_comp_mulVec (m ∘ₗ L ∘ₗ tn₃ e ψ f) (fun φ hφ a => congrArg m (trans_inv hL h hf hφ a)) g hf' (comp_mem hf' g)

theorem swap_mid (hL : Inv e ν L) {l : kˣ} (hl : valuation k (l : k) = 1) (hν : ν l ≠ 1) {ψ : Matrix (Fin n) (Fin d₁) k → ℂ}
    (h : ψ ∈ SB _) {f f₁ f' : (Fin n → k) → ℂ} (hf : f ∈ SB _) (hf₁ : f₁ ∈ SB _) (hf' : f' ∈ SB _) (c : ℂ) (h0 : f 0 = c * f₁ 0) :
    L (tn e ψ f f') = c • L (tn e ψ f₁ f') := by
  have := kil_one hL hl hν (tn e ψ f f' - c • tn e ψ f₁ f') (sub_mem (tn_mem h hf hf') ((SB _).smul_mem _ (tn_mem h hf₁ hf')))
    fun Y hY h1 => hY (by simp only [Pi.sub_apply, Pi.smul_apply, tn, h1, h0, smul_eq_mul]; ring)
  rwa [LinearMap.mem_ker, map_sub, map_smul, sub_eq_zero] at this

theorem one_zero : (one n : (Fin n → k) → ℂ) 0 = 1 := Set.indicator_of_mem (by simp [zero_mem]) _

theorem red (hL : Inv e ν L) (hu : USm ν) {l : kˣ} (hl : valuation k (l : k) = 1) (hν : ν l ≠ 1)
    (h : ∀ ψ, Full ψ → L (tn e ψ (one n) (one n)) = 0) : ∀ Φ ∈ SB (Matrix (Fin n) (Fin d) k), L Φ = 0 := by
  have h2 : Kil (LinearMap.ker L) {Y | RI (mid e Y)} := by
    refine kil_loc hV_mat fun X₀ ⟨R, hR⟩ => ?_
    obtain ⟨r, r0, hr⟩ := mb_small (nhds_sub (det_nhds hR))
    refine ⟨{Y | mid e Y - mid e X₀ ∈ mb _ _ r}, ((mb_open r0).preimage (cm.sub continuous_const)).mem_nhds (by simp [zero_mem]),
      fun Φ hΦ hs => ?_⟩
    obtain ⟨U, hU, hi⟩ := exists_invar hΦ
    obtain ⟨c, c0, hc⟩ := mb_small (inter_mem hU (cm (e := e).continuousAt.preimage_mem_nhds ((mb_open r0).mem_nhds (zero_mem _))))
    refine mem_of_cs (mb_open c0) hΦ (fun S hS => hi S (hc hS).1) _ fun y hy => ?_
    have e1 : cs (mb _ _ c) y = tn e (cs (mb _ _ c ⊓ mb _ _ r) (mid e y)) (cs (bx _ c) (cl e false y)) (cs (bx _ c) (cl e true y)) := by
      funext Y
      classical
      have : Y - y ∈ mb _ _ c ↔ (mid e Y - mid e y ∈ mb _ _ c ⊓ mb _ _ r ∧ cl e false Y - cl e false y ∈ bx _ c) ∧
          cl e true Y - cl e true y ∈ bx _ c := by
        refine ⟨fun h => ⟨⟨⟨fun i s => h i _, (hc h).2⟩, fun i => h i _⟩, fun i => h i _⟩, fun h i j => ?_⟩
        obtain ⟨j, rfl⟩ := e.surjective j
        rcases j with s | _ | _
        exacts [h.1.1.1 i s, h.1.2 i, h.2 i]
      simp only [tn, cs, Set.indicator_apply, Set.mem_setOf_eq, this, Pi.one_apply]
      split_ifs <;> simp_all
    have o : IsOpen ((mb (Fin n) (Fin d₁) c ⊓ mb _ _ r : AddSubgroup _) : Set (Matrix (Fin n) (Fin d₁) k)) := (mb_open c0).inter (mb_open r0)
    have fu : Full (cs (mb (Fin n) (Fin d₁) c ⊓ mb _ _ r) (mid e y)) := by
      refine ⟨cs_mem o ((mb_compact c).inter_right (AddSubgroup.isClosed_of_isOpen _ (mb_open r0))) _, fun Z hZ => ?_⟩
      by_contra h'
      have := hr (add_mem (cs_ne h').2 (hs y hy))
      exact hZ (ri_iff.1 (ri_of_det (R := R) (by simpa using this)))
    have s1 := fun x : Fin n → k => cs_mem (bx_open (S := Fin n) c0) (bx_compact c) x
    rw [LinearMap.mem_ker, e1, swap_mid hL hl hν fu.1 (s1 _) one_sb (s1 _) (cs (bx _ c) (cl e false y) 0) (by rw [one_zero, mul_one])]
    let g : GL (Fin n) k := GeneralLinearGroup.scalar _ (Units.mk0 c c0)⁻¹
    have e2 := mod_inv hL fu one_sb one_sb g
    have e3 : cs (bx _ c) (cl e true y) = fun x => (fun x => one n (g.val *ᵥ x)) (x + -cl e true y) := by
      funext x
      classical
      have : g.val *ᵥ (x + -cl e true y) - 0 ∈ bx (Fin n) (1 : k) ↔ x - cl e true y ∈ bx _ c := by
        refine forall_congr' fun i => ?_
        have : (g.val *ᵥ (x + -cl e true y) - 0) i = c⁻¹ * (x - cl e true y) i := by
          have gv : g.val = diagonal fun _ => c⁻¹ := by
            change Matrix.scalar _ ((Units.mk0 c c0)⁻¹).val = _
            simp [Matrix.scalar_apply]
          rw [gv]
          rw [sub_zero, mulVec_diagonal, sub_eq_add_neg]
        rw [this, map_mul, map_inv₀, map_one, inv_mul_le_iff₀ (zero_lt_iff.2 (by simpa using c0)), mul_one]
      simp only [one, cs, Set.indicator_apply, Set.mem_setOf_eq, this, Pi.one_apply]
    rw [h _ fu, smul_eq_zero] at e2
    rw [e3, trans_inv hL fu one_sb (comp_mem one_sb g), e2.resolve_left (by simpa [apow] using apow_ne_zero (GeneralLinearGroup.det g) 1), smul_zero]
  intro Φ hΦ
  obtain ⟨Φ₀, h0, ha⟩ := surjectivity_statement k n d ν 1 hu (fun h => hν (by simp [h])) Φ hΦ
  have h3 : aug n d ν 1 ≤ LinearMap.ker L := Submodule.span_le.2 (by
    rintro _ ⟨g, Ψ, hΨ, rfl⟩
    exact LinearMap.mem_ker.2 (by rw [map_sub, hL.left g Ψ hΨ, sub_self]))
  have h4 := kil_full hL hl hν h2 Φ₀ h0.1 fun Y hY => ri_iff.2 (by by_contra h'; exact hY (h0.2 Y h'))
  have := add_mem (h3 ha) h4
  rwa [sub_add_cancel] at this

theorem full_omB {m : ℕ} {ψ : Matrix (Fin n) (Fin m) k → ℂ} (h : Full ψ) (g : GL (Fin n) k) (g' : GL (Fin m) k) :
    Full fun Z : Matrix (Fin n) (Fin m) k => ψ (g.val * Z * g'.val) := by
  let H : Matrix (Fin n) (Fin m) k ≃ₜ Matrix (Fin n) (Fin m) k :=
    { toFun := fun x => g.val * x * g'.val, invFun := fun x => (g⁻¹).val * x * (g'⁻¹).val,
      left_inv := fun x => by simp [Matrix.mul_assoc], right_inv := fun x => by simp [Matrix.mul_assoc],
      continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const,
      continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const }
  refine ⟨⟨h.1.1.comp_continuous H.continuous, h.1.2.comp_homeomorph H⟩, fun Z hZ => h.2 _ fun h' => hZ ?_⟩
  obtain ⟨R, hR⟩ := ri_iff.2 h'
  refine ri_iff.1 ⟨g'.val * R * g.val, ?_⟩
  have := congrArg (fun A => (g⁻¹).val * A * g.val) hR
  simpa [Matrix.mul_assoc] using this

theorem aug_ker (hL : Inv e ν L) {l : kˣ} (hl : valuation k (l : k) = 1) (hν : ν l ≠ 1) :
    augF n d₁ ν 1 ≤ LinearMap.ker (L ∘ₗ tn₁ e (one n) (one n)) := Submodule.span_le.2 (by
  rintro _ ⟨g, ψ, h, rfl⟩
  have hd : (d : ℂ) = d₁ + 2 := by
    have := Fintype.card_congr e
    simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_bool] at this
    exact_mod_cast this.symm
  let g' := invT g⁻¹
  have hg : g'.val = g.valᵀ := by simp [g', invT]
  have dg : GeneralLinearGroup.det g' = gdet g := Units.ext (by simp [hg, gdet])
  have fu := full_omB h g' 1
  have e1 := hL.left g _ (tn_mem (e := e) h.1 one_sb one_sb)
  have e2 : omB ν 1 g 1 (tn e ψ (one n) (one n)) = ((ν (gdet g) : ℂ) * apow (gdet g) ((d : ℂ) / 2)) •
      tn e (fun Z : Matrix (Fin n) (Fin d₁) k => ψ (g'.val * Z * (1 : GL (Fin d₁) k).val)) (fun x => one n (g'.val *ᵥ x)) fun x => one n (g'.val *ᵥ x) := by
    funext Y
    have m1 : mid e (g.valᵀ * Y) = g.valᵀ * mid e Y := rfl
    have m2 : ∀ t, cl e t (g.valᵀ * Y) = g.valᵀ *ᵥ cl e t Y := fun t => rfl
    simp [omB, tn, hg, m1, m2]
  have e3 : omB ν 1 g 1 ψ = ((ν (gdet g) : ℂ) * apow (gdet g) ((d₁ : ℂ) / 2)) • fun Z : Matrix (Fin n) (Fin d₁) k => ψ (g'.val * Z * (1 : GL (Fin d₁) k).val) := by
    funext Y
    simp [omB, hg]
  have e4 := mod_inv hL fu one_sb one_sb g'
  rw [e2, map_smul, swap_mid hL hl hν fu.1 (comp_mem one_sb g') one_sb (comp_mem one_sb g') 1 (by simp)] at e1
  refine LinearMap.mem_ker.2 ?_
  rw [map_sub, e3, map_smul, sub_eq_zero]
  refine Eq.trans ?_ e1
  have e5 : (L ∘ₗ tn₁ e (one n) (one n)) (fun Z : Matrix (Fin n) (Fin d₁) k => ψ (g'.val * Z * (1 : GL (Fin d₁) k).val)) = _ := e4.symm
  rw [e5, dg, smul_smul, one_smul, hd, add_div, apow_add]
  congr 1
  simp [apow, mul_assoc])

theorem local_multiplicity_one_irreducible_GL (hB : GlobalTheory.Published.BernsteinUnitaryProductIrreducible) {L' : (Matrix (Fin n) (Fin d) k → ℂ) →ₗ[ℂ] W} (hL : Inv e ν L)
    (hL' : Inv e ν L') (hu : USm ν) {l : kˣ} (hl : valuation k (l : k) = 1) (hν : ν l ≠ 1) (hn : n ≤ d₁)
    (ρ : GL (Fin d₁) k → Module.End ℂ W) (hr : Module.rank ℂ W ≤ Cardinal.aleph0)
    (hi : ∀ N : Submodule ℂ W, (∀ g, ∀ x ∈ N, ρ g x ∈ N) → N = ⊥ ∨ N = ⊤)
    (hM : ∀ g, ∀ Φ ∈ SB (Matrix (Fin n) (Fin d) k), L (fun Y : Matrix (Fin n) (Fin d) k => Φ (Y * blk e g.val)) = ρ g (L Φ))
    (hM' : ∀ g, ∀ Φ ∈ SB (Matrix (Fin n) (Fin d) k), L' (fun Y : Matrix (Fin n) (Fin d) k => Φ (Y * blk e g.val)) = ρ g (L' Φ))
    (h0 : ∃ Φ ∈ SB (Matrix (Fin n) (Fin d) k), L Φ ≠ 0) : ∃ c : ℂ, ∀ Φ ∈ SB (Matrix (Fin n) (Fin d) k), L' Φ = c • L Φ := by
  let S : Submodule ℂ (Matrix (Fin n) (Fin d₁) k → ℂ) :=
    { carrier := {ψ | Full ψ}, add_mem' := fun ha hb => ⟨add_mem ha.1 hb.1, fun Y h => by simp [ha.2 Y h, hb.2 Y h]⟩,
      zero_mem' := ⟨zero_mem _, fun _ _ => rfl⟩, smul_mem' := fun c a ha => ⟨(SB _).smul_mem c ha.1, fun Y h => by simp [ha.2 Y h]⟩ }
  let j := tn₁ e (one n) (one n : (Fin n → k) → ℂ)
  let A : GL (Fin d₁) k → S → S := fun g ψ => ⟨_, full_omB ψ.2 1 g⟩
  have jA : ∀ (g : GL (Fin d₁) k) (ψ : Matrix (Fin n) (Fin d₁) k → ℂ), j (fun Z : Matrix (Fin n) (Fin d₁) k => ψ ((1 : GL (Fin n) k).val * Z * g.val)) =
      fun Y : Matrix (Fin n) (Fin d) k => j ψ (Y * blk e g.val) := fun (g : GL (Fin d₁) k) ψ => funext fun Y => by
    have m1 : mid e (Y * blk e g.val) = mid e Y * g.val := by
      ext i s; simp only [mid, submatrix_apply, Matrix.mul_apply, id]; rw [sum_e (e := e)]; simp [blk]
    have m2 : ∀ t, cl e t (Y * blk e g.val) = cl e t Y := fun t => by
      ext i; simp only [cl, Matrix.mul_apply]; rw [sum_e (e := e)]; cases t <;> simp [blk]
    simp [j, tn₁, tn, m1, m2]
  let μ := L ∘ₗ j ∘ₗ S.subtype
  let μ' := L' ∘ₗ j ∘ₗ S.subtype
  have eA : ∀ g ψ, μ (A g ψ) = ρ g (μ ψ) := fun g ψ => (congrArg L (jA g ψ)).trans (hM g _ (tn_mem ψ.2.1 one_sb one_sb))
  have eA' : ∀ g ψ, μ' (A g ψ) = ρ g (μ' ψ) := fun g ψ => (congrArg L' (jA g ψ)).trans (hM' g _ (tn_mem ψ.2.1 one_sb one_sb))
  have ne : ¬ ∀ ψ, Full ψ → L (tn e ψ (one n) (one n)) = 0 := fun h => let ⟨Φ, h1, h2⟩ := h0; h2 (red hL hu hl hν h Φ h1)
  have ker : ∀ ψ, μ ψ = 0 → μ' ψ = 0 := by
    rcases irrF' hB (α := 1) hn hu (LinearMap.ker (L ∘ₗ j) ⊓ S) (le_inf (aug_ker hL hl hν) (Submodule.span_le.2 (by
      rintro _ ⟨g, ψ, h, rfl⟩
      refine sub_mem ?_ h
      have := S.smul_mem ((ν (gdet g) : ℂ) * apow (gdet g) ((d₁ : ℂ) / 2)) (full_omB h (invT g⁻¹) 1)
      convert this using 1
      funext Y
      simp [omB, invT]))) (fun g ψ h _ => by
        have e1 : omB ν 1 1 g ψ = apow (gdet g) ((n : ℂ) / 2) • (A g ⟨ψ, h.2⟩).1 := by
          funext Y
          simp [omB, A]
        rw [e1]
        refine Submodule.smul_mem _ _ ⟨?_, (A g ⟨ψ, h.2⟩).2⟩
        have : μ ⟨ψ, h.2⟩ = 0 := h.1
        exact (eA g ⟨ψ, h.2⟩).trans (by rw [this, map_zero])) with h | h
    · exact absurd (fun ψ hψ => (h ψ hψ).1) ne
    · exact fun ψ hψ => aug_ker hL' hl hν (h ψ.1 ⟨hψ, ψ.2⟩ ψ.2)
  have top : LinearMap.range μ = ⊤ := (hi _ (by rintro g _ ⟨ψ, rfl⟩; exact ⟨A g ψ, eA g ψ⟩)).resolve_left fun h =>
    ne fun ψ hψ => by
      have : μ ⟨ψ, hψ⟩ ∈ LinearMap.range μ := ⟨_, rfl⟩
      rwa [h, Submodule.mem_bot] at this
  obtain ⟨s, hs⟩ := μ.exists_rightInverse_of_surjective top
  have th : ∀ ψ, (μ' ∘ₗ s) (μ ψ) = μ' ψ := fun ψ => by
    have := ker (s (μ ψ) - ψ) (by rw [map_sub, ← LinearMap.comp_apply μ s, hs, LinearMap.id_apply, sub_self])
    rwa [map_sub, sub_eq_zero] at this
  obtain ⟨c, hc⟩ := dixmier_commutant_scalar _ W ρ hr hi (μ' ∘ₗ s) fun g => LinearMap.ext fun x => by
    obtain ⟨ψ, rfl⟩ := LinearMap.range_eq_top.1 top x
    rw [Module.End.mul_apply, Module.End.mul_apply, ← eA, th, th, eA']
  refine ⟨c, fun Φ hΦ => sub_eq_zero.1 (red (L := L' - c • L) (e := e) ⟨fun g Ψ h => ?_, fun g hg Ψ h => ⟨(hL.right g hg Ψ h).1, ?_⟩⟩
    hu hl hν (fun ψ hψ => ?_) Φ hΦ)⟩
  · simp [hL.left g Ψ h, hL'.left g Ψ h]
  · simp only [LinearMap.sub_apply, LinearMap.smul_apply, (hL.right g hg Ψ h).2, (hL'.right g hg Ψ h).2]
  · have := th ⟨ψ, hψ⟩
    rw [hc] at this
    exact sub_eq_zero.2 this.symm

end PositivityTheory.ThKG.LocalRamifiedLeviRestriction
end
end
