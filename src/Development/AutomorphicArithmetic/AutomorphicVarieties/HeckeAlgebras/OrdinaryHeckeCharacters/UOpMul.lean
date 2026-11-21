import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.ContinuousTorusCharacter

section
open IsLocalRing Matrix UpperTheory.V.Hi

theorem UpperTheory.V.Hi.uOpSum :
    ∀ (G : Type) [Group G] (I : Iwa G) (A M : Type) [CommRing A] [AddCommGroup M] [Module A M] (π : Representation A G M) (a : G), a ∈ I.P → (∃ s : Finset G, (∀ u ∈ s, u ∈ I.N) ∧ ∀ x ∈ I.N, ∃! u, u ∈ s ∧ u⁻¹ * x ∈ I.Nconj a) ∧ ∀ s : Finset G, (∀ u ∈ s, u ∈ I.N) → (∀ x ∈ I.N, ∃! u, u ∈ s ∧ u⁻¹ * x ∈ I.Nconj a) → s.card = (I.Nconj a).relIndex I.N ∧ ∀ v ∈ fixd π I.N, I.uOp π a v = ∑ u ∈ s, π (u * a) v := by
  intro G _ I A M _ _ _ π a ha
  classical
  have hfin : Finite (I.N ⧸ (I.Nconj a).subgroupOf I.N) :=
    Nat.finite_of_card_ne_zero (I.fin_N a ha)
  letI : Fintype (I.N ⧸ (I.Nconj a).subgroupOf I.N) := Fintype.ofFinite _
  have key : ∀ x y : I.N, (QuotientGroup.mk x : I.N ⧸ (I.Nconj a).subgroupOf I.N) = QuotientGroup.mk y ↔
      (x : G)⁻¹ * y ∈ I.Nconj a := by
    intro x y
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simp
  refine ⟨⟨Finset.univ.image (fun q : I.N ⧸ (I.Nconj a).subgroupOf I.N => ((q.out : I.N) : G)), ?_, ?_⟩, ?_⟩
  · intro u hu
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hu
    exact q.out.2
  · intro x hx
    refine ⟨((QuotientGroup.mk (⟨x, hx⟩ : I.N) : I.N ⧸ (I.Nconj a).subgroupOf I.N).out : I.N),
      ⟨Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩, ?_⟩, ?_⟩
    · exact (key _ ⟨x, hx⟩).1 (QuotientGroup.out_eq' _)
    · rintro u ⟨hu, hux⟩
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hu
      have h := (key q.out ⟨x, hx⟩).2 hux
      rw [QuotientGroup.out_eq'] at h
      rw [h]
  · intro s hs hu
    let i : ∀ u ∈ s, I.N ⧸ (I.Nconj a).subgroupOf I.N := fun u h => QuotientGroup.mk ⟨u, hs u h⟩
    have inj : ∀ u₁ (h₁ : u₁ ∈ s) u₂ (h₂ : u₂ ∈ s), i u₁ h₁ = i u₂ h₂ → u₁ = u₂ := by
      intro u₁ h₁ u₂ h₂ h
      have h' := (key ⟨u₁, hs _ h₁⟩ ⟨u₂, hs _ h₂⟩).1 h
      exact (hu u₂ (hs _ h₂)).unique ⟨h₁, h'⟩ ⟨h₂, by simp⟩
    have surj : ∀ q ∈ (Finset.univ : Finset (I.N ⧸ (I.Nconj a).subgroupOf I.N)), ∃ u h, i u h = q := by
      intro q _
      obtain ⟨u, ⟨h, h'⟩, -⟩ := hu q.out q.out.2
      exact ⟨u, h, ((key ⟨u, hs u h⟩ q.out).2 h').trans (QuotientGroup.out_eq' q)⟩
    refine ⟨?_, ?_⟩
    · rw [Finset.card_bij i (fun _ _ => Finset.mem_univ _) inj surj, Subgroup.relIndex, Subgroup.index,
        Nat.card_eq_fintype_card, Finset.card_univ]
    · intro v hv
      rw [Iwa.uOp, finsum_eq_sum_of_fintype, LinearMap.sum_apply]
      refine (Finset.sum_bij i (fun _ _ => Finset.mem_univ _) inj surj ?_).symm
      intro u h
      have h' := (key ⟨u, hs u h⟩ (i u h).out).1 (QuotientGroup.out_eq' _).symm
      obtain ⟨n, hn, e⟩ := Subgroup.mem_map.1 h'
      have e' : (((i u h).out : I.N) : G) * a = u * a * n := by
        have e2 : a * n * a⁻¹ = u⁻¹ * (((i u h).out : I.N) : G) := e
        calc (((i u h).out : I.N) : G) * a = u * (u⁻¹ * (((i u h).out : I.N) : G)) * a := by group
          _ = u * a * n := by rw [← e2]; group
      rw [e', map_mul π (u * a) n, Module.End.mul_apply, hv n hn]
end

section
open IsLocalRing Matrix UpperTheory.V.Hi

private theorem UpperTheory.V.Hi.uOpMul_mem {G : Type} [Group G] (I : Iwa G) (a x : G) :
    x ∈ I.Nconj a ↔ a⁻¹ * x * a ∈ I.N := by
  constructor
  · intro h
    obtain ⟨n, hn, e⟩ := Subgroup.mem_map.1 h
    have e2 : a * n * a⁻¹ = x := e
    have : a⁻¹ * x * a = n := by rw [← e2]; group
    rwa [this]
  · intro h
    refine Subgroup.mem_map.2 ⟨_, h, ?_⟩
    show a * (a⁻¹ * x * a) * a⁻¹ = x
    group

private theorem UpperTheory.V.Hi.uOpMul_sum {G : Type} [Group G] (I : Iwa G) {A M : Type} [CommRing A] [AddCommGroup M]
    [Module A M] (π : Representation A G M) {a : G} (ha : a ∈ I.P) {ι : Type} (s : Finset ι) (f : ι → G)
    (hf : ∀ i ∈ s, f i ∈ I.N) (hu : ∀ x ∈ I.N, ∃! i, i ∈ s ∧ a⁻¹ * ((f i)⁻¹ * x) * a ∈ I.N)
    {v : M} (hv : v ∈ fixd π I.N) : I.uOp π a v = ∑ i ∈ s, π (f i * a) v := by
  classical
  have inj : Set.InjOn f s := by
    intro i hi j hj e
    exact (hu (f j) (hf j hj)).unique ⟨hi, by rw [e]; simp⟩ ⟨hj, by simp⟩
  rw [((uOpSum G I A M π a ha).2 (s.image f) ?_ ?_).2 v hv, Finset.sum_image inj]
  · intro u h
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 h
    exact hf i hi
  · intro x hx
    obtain ⟨i, ⟨hi, h⟩, hun⟩ := hu x hx
    refine ⟨f i, ⟨Finset.mem_image_of_mem f hi, (uOpMul_mem I a _).2 h⟩, ?_⟩
    rintro u ⟨h1, h2⟩
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 h1
    rw [hun j ⟨hj, (uOpMul_mem I a _).1 h2⟩]

private theorem UpperTheory.V.Hi.uOpMul_ex {G : Type} [Group G] (I : Iwa G) {a : G} (ha : a ∈ I.P) :
    ∃ s : Finset G, (∀ u ∈ s, u ∈ I.N) ∧ ∀ x ∈ I.N, ∃! u, u ∈ s ∧ a⁻¹ * (u⁻¹ * x) * a ∈ I.N := by
  obtain ⟨s, h1, h2⟩ := (uOpSum G I ℤ ℤ (Representation.trivial ℤ G ℤ) a ha).1
  refine ⟨s, h1, fun x hx => ?_⟩
  simpa only [uOpMul_mem] using h2 x hx

theorem UpperTheory.V.Hi.uOpMul :
    ∀ (G : Type) [Group G] (I : Iwa G) (A M : Type) [CommRing A] [AddCommGroup M] [Module A M] (π : Representation A G M) (a b : G), a ∈ I.P → b ∈ I.P → ∀ v ∈ fixd π I.N, I.uOp π a v ∈ fixd π I.N ∧ I.uOp π a (I.uOp π b v) = I.uOp π (a * b) v ∧ I.uOp π 1 v = v ∧ (∀ t ∈ I.T, π t (I.uOp π a v) = I.uOp π a (π t v)) ∧ (a⁻¹ ∈ I.P → I.uOp π a v = π a v) := by
  intro G _ I A M _ _ _ π a b ha hb v hv
  have mul : ∀ (g h : G) (w : M), π g (π h w) = π (g * h) w := fun g h w => by
    rw [map_mul π g h, Module.End.mul_apply]
  have fix : ∀ c ∈ I.P, I.uOp π c v ∈ fixd π I.N := by
    intro c hc n hn
    obtain ⟨s, hs, hu⟩ := uOpMul_ex I hc
    have e1 := uOpMul_sum I π hc s id hs hu hv
    have e2 := uOpMul_sum I π hc s (fun u => n * u) (fun u h => mul_mem hn (hs u h)) (fun x hx => by
      have := hu (n⁻¹ * x) (mul_mem (inv_mem hn) hx)
      simpa only [_root_.mul_inv_rev, mul_assoc] using this) hv
    conv_lhs => rw [e1]
    rw [e2, map_sum]
    simp only [mul, id, mul_assoc]
  have unit : ∀ c ∈ I.P, c⁻¹ ∈ I.P → I.uOp π c v = π c v := by
    intro c hc hc'
    rw [uOpMul_sum I π hc ({1} : Finset G) id (by simp) ?_ hv]
    · simp
    · intro x hx
      refine ⟨1, ⟨by simp, by simpa using I.P_N _ hc' x hx⟩, fun y hy => by simpa using hy.1⟩
  refine ⟨fix a ha, ?_, ?_, ?_, unit a ha⟩
  · obtain ⟨s, hs, hu⟩ := uOpMul_ex I ha
    obtain ⟨r, hr, hw⟩ := uOpMul_ex I hb
    rw [uOpMul_sum I π ha s id hs hu (fix b hb), uOpMul_sum I π hb r id hr hw hv,
      uOpMul_sum I π (mul_mem ha hb) (s ×ˢ r) (fun p => p.1 * (a * p.2 * a⁻¹)) ?_ ?_ hv, Finset.sum_product]
    · refine Finset.sum_congr rfl fun u _ => ?_
      rw [map_sum]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [mul]
      congr 2
      simp only [id]
      group
    · intro p hp
      rw [Finset.mem_product] at hp
      exact mul_mem (hs _ hp.1) (I.P_N a ha _ (hr _ hp.2))
    · intro x hx
      have e : ∀ u w : G, (a * b)⁻¹ * ((u * (a * w * a⁻¹))⁻¹ * x) * (a * b) =
          b⁻¹ * (w⁻¹ * (a⁻¹ * (u⁻¹ * x) * a)) * b := fun u w => by group
      obtain ⟨u, ⟨hus, hux⟩, hun⟩ := hu x hx
      obtain ⟨w, ⟨hwr, hwx⟩, hwn⟩ := hw _ hux
      refine ⟨(u, w), ⟨Finset.mem_product.2 ⟨hus, hwr⟩, by rw [e]; exact hwx⟩, ?_⟩
      rintro ⟨u', w'⟩ ⟨hp, h⟩
      rw [Finset.mem_product] at hp
      rw [e] at h
      have h1 : a⁻¹ * (u'⁻¹ * x) * a ∈ I.N := by
        have := mul_mem (hr _ hp.2) (I.P_N b hb _ h)
        convert this using 1
        group
      obtain rfl : u' = u := hun u' ⟨hp.1, h1⟩
      obtain rfl : w' = w := hwn w' ⟨hp.2, h⟩
      rfl
  · rw [unit 1 (one_mem _) (by simpa using one_mem I.P)]
    simp
  · intro t ht
    obtain ⟨s, hs, hu⟩ := uOpMul_ex I ha
    have hc : t * a = a * t := I.comm t (I.T_le ht) a (I.P_le a ha)
    have hN : ∀ x ∈ I.N, t⁻¹ * x * t ∈ I.N := fun x hx => by simpa using I.T_N _ (inv_mem ht) x hx
    have htv : π t v ∈ fixd π I.N := by
      intro n hn
      have : n * t = t * (t⁻¹ * n * t) := by group
      rw [mul, this, ← mul, hv _ (hN n hn)]
    rw [uOpMul_sum I π ha s id hs hu hv,
      uOpMul_sum I π ha s (fun u => t * u * t⁻¹) (fun u h => I.T_N t ht u (hs u h)) ?_ htv, map_sum]
    · refine Finset.sum_congr rfl fun u _ => ?_
      rw [mul, mul, mul_assoc _ a t, ← hc]
      congr 2
      simp only [id]
      group
    · intro x hx
      have e : ∀ u : G, a⁻¹ * ((t * u * t⁻¹)⁻¹ * x) * a = t * (a⁻¹ * (u⁻¹ * (t⁻¹ * x * t)) * a) * t⁻¹ := by
        intro u
        have h1 : a⁻¹ * t = t * a⁻¹ := (Commute.inv_left (show Commute a t from hc.symm)).eq
        have h2 : a = t * a * t⁻¹ := by rw [hc]; group
        calc a⁻¹ * ((t * u * t⁻¹)⁻¹ * x) * a = (a⁻¹ * t) * (u⁻¹ * t⁻¹ * x) * a := by group
          _ = (t * a⁻¹) * (u⁻¹ * t⁻¹ * x) * (t * a * t⁻¹) := by rw [h1, ← h2]
          _ = _ := by group
      have e' : ∀ y : G, t * y * t⁻¹ ∈ I.N ↔ y ∈ I.N := fun y =>
        ⟨fun h => by simpa [mul_assoc] using hN _ h, I.T_N t ht y⟩
      simpa only [e, e'] using hu _ (hN x hx)
end
