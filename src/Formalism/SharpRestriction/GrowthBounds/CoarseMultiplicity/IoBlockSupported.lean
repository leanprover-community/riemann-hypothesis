import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.FTDefs
import Formalism.SharpRestriction.GrowthBounds.RootWeights.ExponentFactorialAddSingleOne
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.OtherStart

section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G Formalism.MainNotions.G.GLWeightTheory MvPolynomial

theorem ft_fock_zero_left {K : Type} [CommSemiring K] {σ : Type} (G : MvPolynomial σ K) :
    fock (0 : MvPolynomial σ K) G = 0 := by
  simp [fock]

theorem fock_add_left {K : Type} [Field K] {σ : Type} (F F' G : MvPolynomial σ K) :
    fock (F + F') G = fock F G + fock F' G := by
  classical
  have key : ∀ (H : MvPolynomial σ K) (s : Finset (σ →₀ ℕ)), H.support ⊆ s →
      fock H G = ∑ m ∈ s, H.coeff m * G.coeff m * (expFact m : K) := by
    intro H s hs
    unfold fock
    refine Finset.sum_subset hs fun m _ hm => ?_
    rw [MvPolynomial.notMem_support_iff.1 hm, zero_mul, zero_mul]
  have hsub : (F + F').support ⊆ F.support ∪ F'.support := MvPolynomial.support_add
  rw [key _ _ hsub, key F (F.support ∪ F'.support) Finset.subset_union_left,
    key F' (F.support ∪ F'.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_add]
  ring

theorem prod_add_mul {O ι : Type} [CommRing O] (s : Finset ι) (a x : ι → O) (t : O) :
    ∃ Y : O, ∏ i ∈ s, (a i + t * x i) = ∏ i ∈ s, a i + t * Y := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert j s hj ih =>
    obtain ⟨Y, hY⟩ := ih
    refine ⟨x j * ∏ i ∈ s, a i + a j * Y + t * x j * Y, ?_⟩
    rw [Finset.prod_insert hj, Finset.prod_insert hj, hY]
    ring

theorem segForm_single {O : Type} [CommRing O] [IsDomain O] (p r : ℕ) {s : ℕ} (S : SegData s)
    (u u' : SegVs O r s S.t) (b0 : SegBlock s r) (h : ∀ b, b ≠ b0 → u b = 0) :
    segForm O p r S u u' = ((specConst p S b0 : ℕ) : KK O) * fock (u b0) (u' b0) := by
  unfold segForm
  rw [finsum_eq_single _ b0]
  intro b hb
  rw [h b hb, ft_fock_zero_left, mul_zero]

theorem vLEO_mono {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {p : ℕ} {x : O} {D D' : ℝ}
    (h : vLEO p x D) (hD : D ≤ D') : vLEO p x D' := by
  obtain ⟨q, hq, hqD⟩ := h
  exact ⟨q, hq, hqD.trans hD⟩

theorem vLEO_one {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {p : ℕ} {w : O} (hw : Irreducible w)
    (h2 : w ^ 2 = (p : O)) {D : ℝ} (hD : 0 ≤ D) : vLEO p (1 : O) D := by
  refine ⟨0, ?_, by simpa using hD⟩
  unfold vO vK ordW
  rw [map_one, if_neg one_ne_zero]
  have hspec := Classical.choose_spec (IsLocalization.surj (nonZeroDivisors O) (1 : KK O))
  rw [one_mul] at hspec
  have heq : ((Classical.choose (IsLocalization.surj (nonZeroDivisors O) (1 : KK O))).2 : O) =
      (Classical.choose (IsLocalization.surj (nonZeroDivisors O) (1 : KK O))).1 :=
    IsFractionRing.injective O (KK O) hspec
  dsimp only
  rw [heq, sub_self]
  simp

theorem famOK_mem {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {C0 CE1 CE2 Cm : ℝ} {X : Loc}
    [NeZero X.m] {β : GlobalTheory X} {u : Vecs O C0 CE1 CE2 X} (hβ : KeptAll C0 CE1 CE2 X β) (hu : FamOK O C0 CE1 CE2 Cm X β u)
    (j : Fin (numSeg X.TT)) :
    u j (β j) ∈ blockLat O X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) (X.m0 Cm) (β j) := by
  have h := (Submodule.mem_pi.1 (hu j).1) (β j) (Set.mem_univ _)
  rwa [if_pos (hβ j)] at h

theorem formAt_of {C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc : ℝ}
    (hstd : ∀ X : Loc, D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X → Std C0 Cde CE1 CE2 1 X)
    (hB : BlockFormAt C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc) (h1 : OrthAt C0 CE1 CE2) (h2 : ProdAt C0 CE1 CE2)
    (h3 : SymPolAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc) (h4 : IntAt) (h5 : NumAt C0 Cde CE1 CE2) (h6 : ZProdAt) :
    FormAt C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc := by
  classical
  intro X _ W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ jO w hS hH hc hc1
  have hD1 : D1num X := ⟨hS.1.prime, hS.1.five_le, hS.1.two_le, hS.1.even⟩
  have St := hstd X hD1 hH hc
  have hw : Irreducible w := hS.2.1
  have hw2 : w ^ 2 = (X.p : O) := hS.1.w_sq
  have hBX := hB X W Qq O Kf ι σ jO w hS hH hc hc1
  have hex : ∀ (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m),
      ∃ (κ : O) (s s' : MvPolynomial (BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t) (KK O) →
          MvPolynomial (BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t) (KK O)),
        κ ≠ 0 ∧ vLEO X.p κ (((X.m + 2) * lgSeg X j : ℕ) : ℝ) ∧
        (Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b →
        (∀ u ∈ blockLat O X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) (X.m0 Cm) b,
          s u ∈ (blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) (X.m0 13) b).SSZ O
            (r := X.m) ∧
          s' u ∈ (blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) (X.m0 13) b).SSZ O
            (r := X.m)) ∧
        ∀ u ∈ blockLat O X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) (X.m0 Cm) b,
        ∀ u' ∈ blockLat O X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) (X.m0 Cm) b,
        ∀ a : O, ((specConst X.p (X.seg C0 CE1 CE2 j) b : ℕ) : KK O) * fock u u' = algebraMap O (KK O) a →
          ∃ x : O, zSeg (KK O) X j * fock (ioBlock (KK O) X.p C0 CE1 CE2 X j b (s u))
              (ioBlock (KK O) X.p C0 CE1 CE2 X j b (s' u')) = algebraMap O (KK O) (κ * (a + w ^ X.c * x))) := by
    intro j b
    by_cases hk : Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b
    · obtain ⟨κ, s, s', a1, a2, a3, a4⟩ := hBX j b hk
      exact ⟨κ, s, s', a1, a2, fun _ => ⟨a3, a4⟩⟩
    · exact ⟨1, id, id, one_ne_zero, vLEO_one hw hw2 (Nat.cast_nonneg _), fun h => absurd h hk⟩
  choose κb sb sb' hκ0 hκv hK using hex
  refine ⟨fun β => ∏ j, κb j (β j), fun β u j => sb j (β j) (u j (β j)), fun β u j => sb' j (β j) (u j (β j)),
    ?_, ?_, ?_⟩
  · intro β
    have hp := vLEO_prod hw hw2 Finset.univ (fun j => κb j (β j)) (fun j => (((X.m + 2) * lgSeg X j : ℕ) : ℝ))
      fun j _ => ⟨hκ0 j (β j), hκv j (β j)⟩
    exact ⟨hp.1, vLEO_mono hp.2 (h5 X St)⟩
  · intro β u hβ hu
    exact ⟨fun j => ((hK j (β j) (hβ j)).1 _ (famOK_mem hβ hu j)).1,
      fun j => ((hK j (β j) (hβ j)).1 _ (famOK_mem hβ hu j)).2⟩
  · intro β u β' u' hβ hβ' hu hu' a ha P hP Q hQ hPc hQc
    have hs1 : InSSZ O C0 CE1 CE2 (X.m0 13) X β (fun j => sb j (β j) (u j (β j))) :=
      fun j => ((hK j (β j) (hβ j)).1 _ (famOK_mem hβ hu j)).1
    have hs2 : InSSZ O C0 CE1 CE2 (X.m0 13) X β' (fun j => sb' j (β' j) (u' j (β' j))) :=
      fun j => ((hK j (β' j) (hβ' j)).1 _ (famOK_mem hβ' hu' j)).2
    set σ₁ := symFam (KK O) X.p C0 CE1 CE2 X β (fun j => sb j (β j) (u j (β j))) with hσ₁
    set σ₂ := symFam (KK O) X.p C0 CE1 CE2 X β' (fun j => sb' j (β' j) (u' j (β' j))) with hσ₂
    have hσ1P := h3 X O hD1 hH hc _ β hβ _ hs1
    have hσ2P := h3 X O hD1 hH hc _ β' hβ' _ hs2
    have hσ1I : InA (O := O) σ₁ := symIntAt C0 CE1 CE2 X O _ β _ hs1
    have hσ2I : InA (O := O) σ₂ := symIntAt C0 CE1 CE2 X O _ β' _ hs2
    have hPI : InA (O := O) P := by
      intro mm
      obtain ⟨c1, e1⟩ := hσ1I mm
      obtain ⟨c2, e2⟩ := hPc mm
      refine ⟨c1 + w ^ X.c * c2, ?_⟩
      rw [map_add, ← e1, ← e2, coeff_sub]
      ring
    obtain ⟨y1, hy1⟩ := h4 X.p O hS.1.prime (dvrOfStd hS) w X.n' X.m X.TT X.aT X.bT (P - σ₁)
      (Submodule.sub_mem _ hP hσ1P) σ₂ X.c hPc hσ2I
    obtain ⟨y2, hy2⟩ := h4 X.p O hS.1.prime (dvrOfStd hS) w X.n' X.m X.TT X.aT X.bT (Q - σ₂)
      (Submodule.sub_mem _ hQ hσ2P) P X.c hQc hPI
    have hdec : fock P Q = fock σ₁ σ₂ + fock (P - σ₁) σ₂ + fock (Q - σ₂) P := by
      have e1 : fock P Q = fock P σ₂ + fock P (Q - σ₂) := by
        rw [← fock_form_add_right]
        congr 1
        ring
      have e2 : fock P σ₂ = fock σ₁ σ₂ + fock (P - σ₁) σ₂ := by
        rw [← fock_add_left]
        congr 1
        ring
      rw [e1, e2, fock_form_symm P (Q - σ₂)]
    have hmain : ∃ ν0 : O, zTen (KK O) X.p X.m X.TT X.aT X.bT * fock σ₁ σ₂ =
        algebraMap O (KK O) ((if β = β' then (∏ j, κb j (β j)) * ∏ j, a j else 0) + w ^ X.c * ν0) := by
      rw [hσ₁, hσ₂, h2 X (KK O) St.seg2 β β' _ _, h6 X (KK O) St.seg2, ← Finset.prod_mul_distrib]
      by_cases hββ : β = β'
      · subst hββ
        have hx : ∀ j, ∃ x : O, zSeg (KK O) X j * fock (ioBlock (KK O) X.p C0 CE1 CE2 X j (β j) (sb j (β j) (u j (β j))))
            (ioBlock (KK O) X.p C0 CE1 CE2 X j (β j) (sb' j (β j) (u' j (β j)))) =
            algebraMap O (KK O) (κb j (β j) * (a j + w ^ X.c * x)) := fun j =>
          (hK j (β j) (hβ j)).2 _ (famOK_mem hβ hu j) _ (famOK_mem hβ hu' j) (a j) (by
            rw [← ha j, segForm_single X.p X.m (X.seg C0 CE1 CE2 j) (u j) (u' j) (β j) (hu j).2])
        choose x hx using hx
        obtain ⟨Y, hY⟩ := prod_add_mul Finset.univ a x (w ^ X.c)
        refine ⟨(∏ j, κb j (β j)) * Y, ?_⟩
        rw [Finset.prod_congr rfl (fun j _ => hx j), ← map_prod, Finset.prod_mul_distrib, hY, if_pos rfl]
        congr 1
        ring
      · obtain ⟨j0, hj0⟩ := Function.ne_iff.mp hββ
        refine ⟨0, ?_⟩
        rw [Finset.prod_eq_zero (Finset.mem_univ j0) (by
          rw [h1 X O _ hD1 j0 _ _ (hβ j0) (hβ' j0) hj0 _ (hs1 j0) _ (hs2 j0), mul_zero]), if_neg hββ]
        simp
    obtain ⟨ν0, h0⟩ := hmain
    refine ⟨ν0 + y1 + y2, ?_⟩
    rw [hdec, mul_add, mul_add, h0, hy1, hy2, ← map_add, ← map_add]
    congr 1
    ring

def RestSymPol : Prop := TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => SymPolAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc

theorem restForm_of' (hB : RestBlockForm) (h1 : ∀ C0 CE1 CE2, OrthAt C0 CE1 CE2) (h2 : ∀ C0 CE1 CE2, ProdAt C0 CE1 CE2)
    (h3 : RestSymPol) (h4 : IntAt) (h5 : ∀ C0 Cde CE1 CE2, NumAt C0 Cde CE1 CE2) (h6 : ZProdAt) : RestForm := by
  intro Cc hCc
  obtain ⟨A0, hA0, hA⟩ := thr_std Cc hCc
  obtain ⟨B0, hB0, hBB⟩ := hB Cc hCc
  obtain ⟨S0, hS0, hS⟩ := h3 Cc hCc
  refine ⟨max A0 (max B0 S0), lt_max_of_lt_left hA0, fun C0 hC0 => ?_⟩
  obtain ⟨A1, hA1, hA'⟩ := hA C0 ((le_max_left _ _).trans hC0)
  obtain ⟨B1, hB1, hBB'⟩ := hBB C0 (((le_max_left _ _).trans (le_max_right _ _)).trans hC0)
  obtain ⟨S1, hS1, hS'⟩ := hS C0 (((le_max_right _ _).trans (le_max_right _ _)).trans hC0)
  refine ⟨max A1 (max B1 S1), lt_max_of_lt_left hA1, fun CE1 CE2 Cm hE1 hE2 hm => ?_⟩
  have l1 : A1 ≤ max A1 (max B1 S1) := le_max_left _ _
  have l2 : B1 ≤ max A1 (max B1 S1) := (le_max_left _ _).trans (le_max_right _ _)
  have l3 : S1 ≤ max A1 (max B1 S1) := (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨A2, hA2, hA''⟩ := hA' CE1 CE2 Cm (l1.trans hE1) (l1.trans hE2) (l1.trans hm)
  obtain ⟨B2, hB2, hBB''⟩ := hBB' CE1 CE2 Cm (l2.trans hE1) (l2.trans hE2) (l2.trans hm)
  obtain ⟨S2, hS2, hS''⟩ := hS' CE1 CE2 Cm (l3.trans hE1) (l3.trans hE2) (l3.trans hm)
  refine ⟨max A2 (max B2 S2), lt_max_of_lt_left hA2, fun CYb Cde Ck CD Cb h₁ h₂ h₃ h₄ h₅ => ?_⟩
  have m1 : A2 ≤ max A2 (max B2 S2) := le_max_left _ _
  have m2 : B2 ≤ max A2 (max B2 S2) := (le_max_left _ _).trans (le_max_right _ _)
  have m3 : S2 ≤ max A2 (max B2 S2) := (le_max_right _ _).trans (le_max_right _ _)
  have hstd := (hA'' CYb Cde Ck CD Cb (m1.trans h₁) (m1.trans h₂) (m1.trans h₃) (m1.trans h₄) (m1.trans h₅)).2
  have hblk := hBB'' CYb Cde Ck CD Cb (m2.trans h₁) (m2.trans h₂) (m2.trans h₃) (m2.trans h₄) (m2.trans h₅)
  have hsym := hS'' CYb Cde Ck CD Cb (m3.trans h₁) (m3.trans h₂) (m3.trans h₃) (m3.trans h₄) (m3.trans h₅)
  exact formAt_of hstd hblk (h1 C0 CE1 CE2) (h2 C0 CE1 CE2) hsym h4 (h5 C0 Cde CE1 CE2) h6

end Formalism.MainNotions.ColumnSystems.Pf
end
end

section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G Formalism.MainNotions.G.GLWeightTheory MvPolynomial

section Gen

variable {K : Type} [Field K] {σ : Type}

theorem fock_sum_left {ι : Type} (s : Finset ι) (f : ι → MvPolynomial σ K) (G : MvPolynomial σ K) :
    fock (∑ i ∈ s, f i) G = ∑ i ∈ s, fock (f i) G := by
  classical
  have hS : ∀ (F : MvPolynomial σ K) (T : Finset (σ →₀ ℕ)), F.support ⊆ T →
      fock F G = ∑ m ∈ T, F.coeff m * G.coeff m * (expFact m : K) := by
    intro F T hT
    unfold fock
    refine Finset.sum_subset hT fun m _ hm => ?_
    have h0 : F.coeff m = 0 := by simpa [mem_support_iff] using hm
    rw [h0, zero_mul, zero_mul]
  rw [hS _ (s.biUnion fun i => (f i).support) support_sum]
  simp only [coeff_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i hi => ?_
  exact (hS (f i) _ (Finset.subset_biUnion_of_mem (fun i => (f i).support) hi)).symm

theorem fock_sum_right {ι : Type} (s : Finset ι) (F : MvPolynomial σ K) (g : ι → MvPolynomial σ K) :
    fock F (∑ i ∈ s, g i) = ∑ i ∈ s, fock F (g i) := by
  unfold fock
  simp only [coeff_sum, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem supp_of_supported {A : Set σ} {F : MvPolynomial σ K} (hF : F ∈ supported K A) {a : σ →₀ ℕ}
    (ha : a ∈ F.support) : (a.support : Set σ) ⊆ A := by
  intro x hx
  rw [mem_supported] at hF
  exact hF ((mem_vars x).mpr ⟨a, ha, hx⟩)

theorem add_eq_add_disj {A B : Set σ} (hAB : Disjoint A B) {a a' b b' : σ →₀ ℕ} (ha : (a.support : Set σ) ⊆ A)
    (ha' : (a'.support : Set σ) ⊆ A) (hb : (b.support : Set σ) ⊆ B) (hb' : (b'.support : Set σ) ⊆ B) :
    a' + b' = a + b ↔ a' = a ∧ b' = b := by
  have zA : ∀ (c : σ →₀ ℕ), (c.support : Set σ) ⊆ A → ∀ x, x ∉ A → c x = 0 := by
    intro c hc x hx
    by_contra hne
    exact hx (hc (Finset.mem_coe.mpr (Finsupp.mem_support_iff.mpr hne)))
  have zB : ∀ (c : σ →₀ ℕ), (c.support : Set σ) ⊆ B → ∀ x, x ∈ A → c x = 0 := by
    intro c hc x hx
    by_contra hne
    exact Set.disjoint_left.mp hAB hx (hc (Finset.mem_coe.mpr (Finsupp.mem_support_iff.mpr hne)))
  constructor
  · intro h
    have hx : ∀ x, a' x + b' x = a x + b x := fun x => by
      have h1 := congrArg (fun f : σ →₀ ℕ => f x) h
      simpa using h1
    refine ⟨Finsupp.ext fun x => ?_, Finsupp.ext fun x => ?_⟩
    · by_cases hxA : x ∈ A
      · have := hx x
        rw [zB b hb x hxA, zB b' hb' x hxA] at this
        omega
      · rw [zA a ha x hxA, zA a' ha' x hxA]
    · by_cases hxA : x ∈ A
      · rw [zB b hb x hxA, zB b' hb' x hxA]
      · have := hx x
        rw [zA a ha x hxA, zA a' ha' x hxA] at this
        omega
  · rintro ⟨rfl, rfl⟩
    rfl

theorem expFact_add_disj {A B : Set σ} (hAB : Disjoint A B) {a b : σ →₀ ℕ} (ha : (a.support : Set σ) ⊆ A)
    (hb : (b.support : Set σ) ⊆ B) : expFact (a + b) = expFact a * expFact b := by
  unfold expFact
  apply Finsupp.prod_add_index_of_disjoint
  rw [Finset.disjoint_left]
  intro x hxa hxb
  exact Set.disjoint_left.mp hAB (ha hxa) (hb hxb)

theorem fock_mono_disj {A B : Set σ} (hAB : Disjoint A B) {a a' b b' : σ →₀ ℕ} (ha : (a.support : Set σ) ⊆ A)
    (ha' : (a'.support : Set σ) ⊆ A) (hb : (b.support : Set σ) ⊆ B) (hb' : (b'.support : Set σ) ⊆ B)
    (c1 c2 c3 c4 : K) :
    fock (monomial a c1 * monomial b c2) (monomial a' c3 * monomial b' c4) =
      fock (monomial a c1) (monomial a' c3) * fock (monomial b c2) (monomial b' c4) := by
  classical
  have hmono : ∀ (u v : σ →₀ ℕ) (x y : K),
      fock (monomial u x) (monomial v y) = if u = v then x * y * (expFact u : K) else 0 := by
    intro u v x y
    by_cases hx : x = 0
    · subst hx
      rw [monomial_zero]
      unfold fock
      rw [support_zero, Finset.sum_empty]
      split_ifs <;> simp
    · unfold fock
      rw [support_monomial, if_neg hx, Finset.sum_singleton, coeff_monomial, coeff_monomial, if_pos rfl]
      by_cases huv : u = v
      · subst huv
        rw [if_pos rfl, if_pos rfl]
      · rw [if_neg (Ne.symm huv), if_neg huv, mul_zero, zero_mul]
  rw [monomial_mul, monomial_mul, hmono, hmono, hmono]
  have hiff : a + b = a' + b' ↔ a = a' ∧ b = b' := by
    rw [eq_comm, add_eq_add_disj hAB ha ha' hb hb', eq_comm, @eq_comm _ b']
  by_cases h1 : a = a' <;> by_cases h2 : b = b'
  · rw [if_pos (hiff.mpr ⟨h1, h2⟩), if_pos h1, if_pos h2, expFact_add_disj hAB ha hb]
    push_cast
    ring
  · rw [if_neg (fun h => h2 (hiff.mp h).2), if_neg h2, mul_zero]
  · rw [if_neg (fun h => h1 (hiff.mp h).1), if_neg h1, zero_mul]
  · rw [if_neg (fun h => h1 (hiff.mp h).1), if_neg h1, zero_mul]

theorem fock_mul_disj {A B : Set σ} (hAB : Disjoint A B) {F1 G1 F2 G2 : MvPolynomial σ K}
    (hF1 : F1 ∈ supported K A) (hG1 : G1 ∈ supported K A) (hF2 : F2 ∈ supported K B) (hG2 : G2 ∈ supported K B) :
    fock (F1 * F2) (G1 * G2) = fock F1 G1 * fock F2 G2 := by
  classical
  have e : ∀ (F G : MvPolynomial σ K), fock F G =
      ∑ a ∈ F.support, ∑ a' ∈ G.support, fock (monomial a (F.coeff a)) (monomial a' (G.coeff a')) := by
    intro F G
    conv_lhs => rw [F.as_sum, G.as_sum]
    rw [fock_sum_left]
    exact Finset.sum_congr rfl fun a _ => fock_sum_right _ _ _
  have hprod : ∀ (P Q : MvPolynomial σ K), P * Q =
      ∑ a ∈ P.support, ∑ b ∈ Q.support, monomial a (P.coeff a) * monomial b (Q.coeff b) := by
    intro P Q
    conv_lhs => rw [P.as_sum, Q.as_sum]
    rw [Finset.sum_mul_sum]
  calc fock (F1 * F2) (G1 * G2)
      = ∑ a ∈ F1.support, ∑ b ∈ F2.support, ∑ a' ∈ G1.support, ∑ b' ∈ G2.support,
          fock (monomial a (F1.coeff a) * monomial b (F2.coeff b))
            (monomial a' (G1.coeff a') * monomial b' (G2.coeff b')) := by
        rw [hprod F1 F2, hprod G1 G2, fock_sum_left]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [fock_sum_left]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [fock_sum_right]
        exact Finset.sum_congr rfl fun a' _ => fock_sum_right _ _ _
    _ = ∑ a ∈ F1.support, ∑ a' ∈ G1.support, ∑ b ∈ F2.support, ∑ b' ∈ G2.support,
          fock (monomial a (F1.coeff a)) (monomial a' (G1.coeff a')) *
            fock (monomial b (F2.coeff b)) (monomial b' (G2.coeff b')) := by
        refine Finset.sum_congr rfl fun a ha => ?_
        rw [Finset.sum_comm (s := F2.support) (t := G1.support)]
        refine Finset.sum_congr rfl fun a' ha' => Finset.sum_congr rfl fun b hb =>
          Finset.sum_congr rfl fun b' hb' => ?_
        exact fock_mono_disj hAB (supp_of_supported hF1 ha) (supp_of_supported hG1 ha')
          (supp_of_supported hF2 hb) (supp_of_supported hG2 hb') _ _ _ _
    _ = fock F1 G1 * fock F2 G2 := by
        rw [e F1 G1, e F2 G2, Finset.sum_mul]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun a' _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.mul_sum]

theorem fock_one_one : fock (1 : MvPolynomial σ K) 1 = 1 := by
  classical
  unfold fock
  rw [← C_1, support_C, if_neg one_ne_zero, Finset.sum_singleton, coeff_C, if_pos rfl]
  simp [expFact]

theorem fock_prod_disj {J : Type} (A : J → Set σ) (hA : ∀ j j', j ≠ j' → Disjoint (A j) (A j')) (s : Finset J)
    (F G : J → MvPolynomial σ K) (hF : ∀ j, F j ∈ supported K (A j)) (hG : ∀ j, G j ∈ supported K (A j)) :
    fock (∏ j ∈ s, F j) (∏ j ∈ s, G j) = ∏ j ∈ s, fock (F j) (G j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [fock_one_one]
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj, Finset.prod_insert hj, ← ih]
    have hsupp : ∀ H : J → MvPolynomial σ K, (∀ j, H j ∈ supported K (A j)) →
        (∏ j' ∈ s, H j') ∈ supported K (⋃ j' ∈ s, A j') := by
      intro H hH
      exact Subalgebra.prod_mem _ fun j' hj' => supported_mono (Set.subset_biUnion_of_mem hj') (hH j')
    have hdisj : Disjoint (A j) (⋃ j' ∈ s, A j') := by
      rw [Set.disjoint_iUnion₂_right]
      intro j' hj'
      exact hA j j' (fun h => hj (h ▸ hj'))
    exact fock_mul_disj hdisj (hF j) (hG j) (hsupp F hF) (hsupp G hG)

theorem aeval_mem_sub {τ : Type} (S : Subalgebra K (MvPolynomial σ K)) (f : τ → MvPolynomial σ K) (hf : ∀ v, f v ∈ S)
    (u : MvPolynomial τ K) : aeval f u ∈ S := by
  have h1 : aeval f u ∈ Algebra.adjoin K (Set.range f) := by
    rw [← MvPolynomial.aeval_range]
    exact AlgHom.mem_range_self _ u
  exact Algebra.adjoin_le (Set.range_subset_iff.mpr hf) h1

end Gen

def segVars (X : Loc) (j : Fin (numSeg X.TT)) : Set ((X.TT × Bool) × Fin (X.m + 1)) :=
  {v | v.1.1 = topEnd X j ∨ ∃ i, v.1.1 = topOdd X j i}

private theorem cdist_eq_ite {n' : ℕ} (u v : Fin n') :
    cdist u v = if u.val ≤ v.val then v.val - u.val else v.val + n' - u.val := by
  unfold cdist
  have hu := u.isLt
  have hv := v.isLt
  split_ifs with h
  · rw [show v.val + n' - u.val = (v.val - u.val) + n' by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · exact Nat.mod_eq_of_lt (by omega)

private theorem false_of_cdist_between_both_ways {n' : ℕ} (a b x : Fin n') (h1 : 0 < cdist a x) (h2 : cdist a x < cdist a b)
    (h3 : 0 < cdist b x) (h4 : cdist b x < cdist b a) : False := by
  have ha := a.isLt
  have hb := b.isLt
  have hx := x.isLt
  rw [cdist_eq_ite] at h1 h3
  rw [cdist_eq_ite, cdist_eq_ite] at h2 h4
  split_ifs at h1 h2 h3 h4 <;> omega

private theorem posAdd_cdist_eq_self' {n' : ℕ} (a s : Fin n') : posAdd a (cdist a s) = s := by
  apply Fin.ext
  have ha := a.isLt
  have hs := s.isLt
  show (a.val + cdist a s) % n' = s.val
  rw [cdist_eq_ite]
  split_ifs with h
  · rw [show a.val + (s.val - a.val) = s.val by omega, Nat.mod_eq_of_lt hs]
  · rw [show a.val + (s.val + n' - a.val) = s.val + n' by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hs]

theorem segVars_disj (X : Loc) (j j' : Fin (numSeg X.TT)) (h : j ≠ j') : Disjoint (segVars X j) (segVars X j') := by
  classical
  have hnodup : (evenTops X.TT).Nodup := Finset.sort_nodup _ _
  have hN : 2 ≤ numSeg X.TT := by
    by_contra hlt
    push_neg at hlt
    have := j.isLt
    have := j'.isLt
    exact h (Fin.ext (by omega))
  have hEnd : ∀ a b : Fin (numSeg X.TT), topEnd X a = topEnd X b → a = b := by
    intro a b hab
    have h1 : segNext X.TT a = segNext X.TT b := congrArg Subtype.val hab
    unfold segNext at h1
    have h2 := congrArg Fin.val ((List.Nodup.get_inj_iff hnodup).1 h1)
    simp only at h2
    have ha := a.isLt
    have hb := b.isLt
    apply Fin.ext
    by_cases ha1 : a.val + 1 < numSeg X.TT <;> by_cases hb1 : b.val + 1 < numSeg X.TT
    · rw [Nat.mod_eq_of_lt ha1, Nat.mod_eq_of_lt hb1] at h2
      omega
    · rw [Nat.mod_eq_of_lt ha1, show b.val + 1 = numSeg X.TT by omega, Nat.mod_self] at h2
      omega
    · rw [show a.val + 1 = numSeg X.TT by omega, Nat.mod_self, Nat.mod_eq_of_lt hb1] at h2
      omega
    · omega
  have hpar : ∀ a (i : Fin (segS X.TT a)) b, topOdd X a i ≠ topEnd X b := by
    intro a i b heq
    have hv : segPos X.TT a i = segNext X.TT b := congrArg Subtype.val heq
    have h1 := (pos_mem X.TT a i).2
    rw [hv] at h1
    exact h1 (next_mem X.TT b).2
  have hseg : ∀ a (i : Fin (segS X.TT a)), 0 < cdist (segStart X.TT a) (segPos X.TT a i) ∧
      cdist (segStart X.TT a) (segPos X.TT a i) < segG X.TT a := by
    intro a i
    set d := (segDists X.TT a).get i with hdd
    have hd : d ∈ segDists X.TT a := List.get_mem _ _
    unfold segDists at hd
    rw [Finset.mem_sort, Finset.mem_image] at hd
    obtain ⟨s, hs, hsd⟩ := hd
    have hps : segPos X.TT a i = s := by
      show posAdd (segStart X.TT a) d = s
      rw [← hsd, posAdd_cdist_eq_self']
    rw [hps]
    exact ⟨(Finset.mem_filter.1 hs).2.2.1, (Finset.mem_filter.1 hs).2.2.2⟩
  have hsm : ∀ c : Fin (numSeg X.TT), segStart X.TT c ∈ X.TT ∧ Even (segStart X.TT c).val := by
    intro c
    have hm : segStart X.TT c ∈ evenTops X.TT := List.get_mem _ _
    rw [evenTops, Finset.mem_sort, Finset.mem_filter] at hm
    exact hm
  have hodd : ∀ a b (i : Fin (segS X.TT a)) (i' : Fin (segS X.TT b)), topOdd X a i = topOdd X b i' → a = b := by
    intro a b i i' heq
    by_contra hab
    have hx : segPos X.TT a i = segPos X.TT b i' := congrArg Subtype.val heq
    have hsa := hseg a i
    have hsb := hseg b i'
    rw [hx] at hsa
    have hstart : segStart X.TT a ≠ segStart X.TT b := by
      intro hs
      exact hab ((List.Nodup.get_inj_iff hnodup).1 hs)
    have hna := next_min X.TT a (segStart X.TT b) (hsm b).1 (hsm b).2 (Ne.symm hstart)
    have hnb := next_min X.TT b (segStart X.TT a) (hsm a).1 (hsm a).2 hstart
    have hga := (segG_eq X.TT hN a).1
    have hgb := (segG_eq X.TT hN b).1
    exact false_of_cdist_between_both_ways (segStart X.TT a) (segStart X.TT b) (segPos X.TT b i') hsa.1 (by omega) hsb.1 (by omega)
  rw [Set.disjoint_left]
  rintro ⟨⟨v, bb⟩, cc⟩ hv hv'
  simp only [segVars, Set.mem_setOf_eq] at hv hv'
  rcases hv with hv | ⟨i, hv⟩ <;> rcases hv' with hv' | ⟨i', hv'⟩
  · exact h (hEnd j j' (hv.symm.trans hv'))
  · exact hpar j' i' j (hv'.symm.trans hv)
  · exact hpar j i j' (hv.symm.trans hv')
  · exact h (hodd j j' i i' (hv.symm.trans hv'))

theorem symVar_mem (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT))
    (v : BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t) : symVar C0 CE1 CE2 X j v ∈ segVars X j := by
  rcases v with ⟨a, c⟩ | ⟨l, b⟩
  · dsimp only [symVar]
    split_ifs with h
    · exact Or.inr ⟨_, rfl⟩
    · exact Or.inl rfl
  · dsimp only [symVar]
    split_ifs with h
    · exact Or.inr ⟨_, rfl⟩
    · exact Or.inl rfl

theorem ioBlock_supported (K : Type) [Field K] (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT))
    (b : SegBlock (segS X.TT j) X.m) (u : MvPolynomial (BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t) K) :
    ioBlock K X.p C0 CE1 CE2 X j b u ∈ supported K (segVars X j) := by
  have hX : ∀ v, v ∈ segVars X j →
      (MvPolynomial.X v : MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) K) ∈ supported K (segVars X j) :=
    fun v hv => X_mem_supported.mpr hv
  have hodd : ∀ i (β : Bool) c, ((topOdd X j i, β), c) ∈ segVars X j := fun i β c => Or.inr ⟨i, rfl⟩
  unfold ioBlock digitMon sTopMon
  refine Subalgebra.mul_mem _ (Subalgebra.mul_mem _ ?_ ?_) ?_
  · exact Subalgebra.prod_mem _ fun i _ => Subalgebra.prod_mem _ fun c _ =>
      Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (hX _ (hodd i true c)) _)
        (Subalgebra.pow_mem _ (hX _ (hodd i false c)) _)
  · refine Subalgebra.prod_mem _ fun i _ => ?_
    split_ifs
    · exact Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (hX _ (hodd i true 0)) _)
        (Subalgebra.pow_mem _ (hX _ (hodd i false 0)) _)
    · exact Subalgebra.one_mem _
  · exact aeval_mem_sub _ _ (fun v => Subalgebra.pow_mem _ (hX _ (symVar_mem C0 CE1 CE2 X j v)) _) u

theorem prodAt (C0 CE1 CE2 : ℝ) : ProdAt C0 CE1 CE2 := by
  intro X K _ hseg β β' s s'
  unfold symFam
  exact fock_prod_disj (segVars X) (segVars_disj X) Finset.univ _ _
    (fun j => ioBlock_supported K C0 CE1 CE2 X j (β j) (s j))
    (fun j => ioBlock_supported K C0 CE1 CE2 X j (β' j) (s' j))

end Formalism.MainNotions.ColumnSystems.Pf
end
end
