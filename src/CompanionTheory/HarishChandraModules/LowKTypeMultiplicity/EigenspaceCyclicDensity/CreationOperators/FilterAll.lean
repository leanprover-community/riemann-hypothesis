import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.DifferentialBoundedSupport
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.KTypeCount
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOnePOf
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SchwartzBilinear.DoubleSumReduceSecond

section
open Finset

noncomputable section

namespace CompanionTheory.D.LK

open Car Formalism.REAL
open CompanionTheory.D.DSIC (KRel)

variable {n : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def al (i : Pos n) (c : Fin n) : ℝ := (if i.1.1 = c then 1 else 0) - (if i.1.2 = c then 1 else 0)

theorem wt_insert {i : Pos n} {A : Finset (Pos n)} (h : i ∉ A) (c : Fin n) : wt (insert i A) c = wt A c + al i c := by
  simp only [wt, al, filter_insert]
  have h1 : ∀ p : Pos n → Prop, ∀ [DecidablePred p], i ∉ A.filter p := fun p _ hh => h (mem_filter.1 hh).1
  split_ifs <;> (try simp only [card_insert_of_notMem (h1 _)]) <;> push_cast <;> ring

theorem Ft_apply (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (c : Fin n) (x : Cn n V)
    (A : Finset (Pos n)) : Ft ε E c x A = E c c (x A) + (wt (A.filter (cpt ε)) c : ℂ) • x A := rfl

theorem Ft_ann {ε : Fin n → Bool} (E : Fin n → Fin n → Module.End ℂ V) (c : Fin n) {i : Pos n} (hi : cpt ε i)
    (x : Cn n V) : Ft ε E c (ann i x) = ann i (Ft ε E c x) - (al i c : ℂ) • ann i x := by
  funext A
  simp only [Ft_apply, ann_apply, Pi.sub_apply, Pi.smul_apply]
  by_cases h : i ∈ A
  · simp [h]
  · rw [if_neg h, if_neg h, filter_insert, if_pos hi, wt_insert (fun hh => h (mem_filter.1 hh).1), map_smul]
    push_cast
    module

theorem Ft_cre {ε : Fin n → Bool} (E : Fin n → Fin n → Module.End ℂ V) (c : Fin n) {i : Pos n} (hi : cpt ε i)
    (x : Cn n V) : Ft ε E c (cre i x) = cre i (Ft ε E c x) + (al i c : ℂ) • cre i x := by
  funext A
  simp only [Ft_apply, cre_apply, Pi.add_apply, Pi.smul_apply]
  by_cases h : i ∈ A
  · have e : A.filter (cpt ε) = insert i ((A.erase i).filter (cpt ε)) := by
      conv_lhs => rw [← insert_erase h, filter_insert, if_pos hi]
    rw [if_pos h, if_pos h, e, wt_insert (fun hh => notMem_erase i A (mem_filter.1 hh).1), map_smul]
    push_cast
    module
  · simp [h]

theorem differential_commutes_weight_operator : ∀ (n : ℕ) (ε₀ ε : Fin n → Bool) (V : Type) [AddCommGroup V] [Module ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V), (∀ a b, ε a = ε b → ε₀ a = ε₀ b) → KRel ε E →
    ∀ c, Commute (Ft ε₀ E c) (bd ε E) := by
  intro n ε₀ ε V _ _ E h0 hE c
  refine Commute.add_right (Commute.sum_right _ _ _ fun i _ => ?_) (Commute.sum_right _ _ _ fun i _ =>
    Commute.sum_right _ _ _ fun j _ => Commute.sum_right _ _ _ fun k _ => ?_)
  · split_ifs with hi
    · refine LinearMap.ext fun x => ?_
      have e : ∀ y : Cn n V, Ft ε₀ E c (lift n (E i.1.1 i.1.2) y) =
          lift n (E i.1.1 i.1.2) (Ft ε₀ E c y) + (al i c : ℂ) • lift n (E i.1.1 i.1.2) y := by
        intro y
        funext A
        have := congrArg (fun T : Module.End ℂ V => T (y A)) (hE c c i.1.1 i.1.2 rfl hi)
        simp only [LinearMap.sub_apply, Module.End.mul_apply] at this
        simp only [Ft_apply, lift_apply, Pi.add_apply, Pi.smul_apply, map_add, map_smul, sub_eq_iff_eq_add.1 this, al]
        have hne := i.2.ne
        by_cases h1 : c = i.1.1
        · subst h1; simp [hne.symm]; module
        · by_cases h2 : i.1.2 = c
          · subst h2; simp [hne, hne.symm]; module
          · simp [h1, h2, Ne.symm h1]
      simp only [Module.End.mul_apply]
      rw [e, Ft_ann E c (h0 _ _ hi), map_sub, map_smul, sub_add_cancel]
    · exact Commute.zero_right _
  · split_ifs with ht
    · refine LinearMap.ext fun x => ?_
      have hk := Tri.cptk (ε := ε) ht
      simp only [Module.End.mul_apply]
      rw [Ft_cre E c (h0 _ _ hk), Ft_ann E c (h0 _ _ ht.2.1), Ft_ann E c (h0 _ _ ht.1)]
      have : (al k c : ℂ) = al i c + al j c := by
        rw [← Complex.ofReal_add]; simp only [al, ht.2.2.1, ht.2.2.2.1, ht.2.2.2.2]; congr 1; ring
      simp only [map_sub, map_smul, this]
      module
    · exact Commute.zero_right _

theorem free_inter {ι : Type} (φ : V →ₗ[ℂ] W) (S : ι → Module.End ℂ V) (T : ι → Module.End ℂ W)
    (h : ∀ i x, φ (S i x) = T i (φ x)) (a : FreeAlgebra ℂ ι) :
    ∀ x, φ (FreeAlgebra.lift ℂ S a x) = FreeAlgebra.lift ℂ T a (φ x) := by
  induction a using FreeAlgebra.induction with
  | grade0 r => intro x; simp [Module.algebraMap_end_apply]
  | grade1 c => intro x; simp [h]
  | mul a b ha hb => intro x; simp only [map_mul, Module.End.mul_apply, ha, hb]
  | add a b ha hb => intro x; simp only [map_add, LinearMap.add_apply, ha, hb]

theorem evK_inter {ε : Fin n → Bool} (φ : V →ₗ[ℂ] W) (E : Fin n → Fin n → Module.End ℂ V)
    (F : Fin n → Fin n → Module.End ℂ W) (h : ∀ a b x, φ (E a b x) = F a b (φ x)) (a : FreeAlgebra ℂ (Fin n × Fin n))
    (x : V) : φ (evK ε E a x) = evK ε F a (φ x) :=
  free_inter φ _ _ (fun p x => by split_ifs <;> simp [h]) a x

theorem evd_Ft_apply (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (b : FreeAlgebra ℂ (Fin n))
    (x : Cn n V) (A : Finset (Pos n)) :
    evd (Ft ε E) b x A = evd (fun c => E c c + (wt (A.filter (cpt ε)) c : ℂ) • 1) b (x A) :=
  free_inter (LinearMap.proj (R := ℂ) (φ := fun _ => V) A) _ _ (fun _ _ => rfl) b x

theorem lift_evd {ε : Fin n → Bool} (φ : V →ₗ[ℂ] W) (E : Fin n → Fin n → Module.End ℂ V)
    (F : Fin n → Fin n → Module.End ℂ W) (h : ∀ a b x, φ (E a b x) = F a b (φ x)) (b : FreeAlgebra ℂ (Fin n))
    (x : Cn n V) : lift n φ (evd (Ft ε E) b x) = evd (Ft ε F) b (lift n φ x) :=
  free_inter (lift n φ) _ _ (fun c y => by funext A; simp [Ft_apply, h]) b x

theorem sup_of_supp {ε : Fin n → Bool} {B : Finset (Pos n)} {j : ℕ} {x : Cn n V} {y : Cn n W} (hx : Sup ε B j x)
    (h : ∀ A, x A = 0 → y A = 0) : Sup ε B j y := fun A hA => hx A fun h0 => hA (h A h0)

theorem Sup.sub {ε : Fin n → Bool} {B : Finset (Pos n)} {j : ℕ} {x y : Cn n V} (hx : Sup ε B j x) (hy : Sup ε B j y) :
    Sup ε B j (x - y) := fun A hA => by
  by_cases h : x A = 0
  · exact hy A fun h' => hA (by simp [h, h'])
  · exact hx A h

theorem genCO_of (hS : BdSq) (hC : Cover2) : GenCO := by
  intro n ε₀ ε a b h0 hab V _ _ E hE B j
  induction j generalizing V with
  | zero =>
    intro x hx _ _
    obtain ⟨w, hw⟩ := (hab V E hE).2 (x B)
    have hxB : ∀ A, A ≠ B → x A = 0 := fun A hA => by
      by_contra h
      obtain ⟨e1, e2⟩ := hx A h
      refine hA (e1 ▸ (filter_true_of_mem fun i hi hc => ?_).symm)
      exact notMem_empty i (card_eq_zero.1 e2 ▸ mem_filter.2 ⟨hi, hc⟩)
    by_cases hB : x B = 0
    · have : x = 0 := funext fun A => by
        by_cases h : A = B
        · rw [h, hB]; rfl
        · exact hxB A h
      subst this
      exact ⟨0, fun A hA => absurd rfl hA, by simp⟩
    have hBn : ∀ i ∈ B, ¬cpt ε₀ i := fun i hi => (mem_filter.1 ((hx B hB).1.symm ▸ hi :)).2
    have hBc : B.filter (cpt ε₀) = ∅ := filter_false_of_mem hBn
    let w' : Cn n V := fun A => ∑ i : Pos n, if cpt ε₀ i ∧ A = insert i B then sg i B • w i else 0
    have hw' : Sup ε₀ B (0 + 1) w' := by
      intro A hA
      obtain ⟨i, -, hi⟩ := exists_ne_zero_of_sum_ne_zero hA
      obtain ⟨h1, rfl⟩ : cpt ε₀ i ∧ A = insert i B := by by_contra h; exact hi (if_neg h)
      rw [filter_insert, if_neg (not_not.2 h1), filter_true_of_mem hBn, filter_insert, if_pos h1, hBc]
      simp
    refine ⟨w', hw', funext fun A => ?_⟩
    by_cases hA : A = B
    · subst hA
      rw [Pi.sub_apply, lift_apply, evd_Ft_apply, hBc]
      have e : (fun c => E c c + (wt (∅ : Finset (Pos n)) c : ℂ) • (1 : Module.End ℂ V)) = fun c => E c c := by
        funext c; simp [wt]
      rw [e, hw, bd_apply, Finset.sum_eq_zero (s := univ) (f := fun i => ∑ j : Pos n, ∑ k : Pos n,
        if Tri ε₀ i j k then cre k (ann j (ann i w')) A else 0), add_zero]
      · refine Finset.sum_congr rfl fun i _ => ?_
        split_ifs with hi
        · have hiA : i ∉ A := fun h => hBn i h hi
          rw [ann_apply, if_neg hiA]
          congr 1
          simp only [w']
          rw [Finset.sum_eq_single i, if_pos ⟨hi, rfl⟩, smul_smul, sg_mul_self, one_smul]
          · intro k _ hk
            refine if_neg fun h => ?_
            rcases mem_insert.1 (h.2 ▸ mem_insert_self i A) with h' | h'
            · exact hk h'.symm
            · exact hiA h'
          · simp
        · rfl
      · refine fun i _ => Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => ?_
        split_ifs with ht
        · by_contra h
          exact hBn k (tri_ne h).1 ht.cptk
        · rfl
    · rw [Pi.sub_apply, lift_apply, evd_Ft_apply, hxB A hA, map_zero, map_zero, sub_zero]
      by_contra h
      obtain ⟨e1, e2⟩ := sup_bd E hw' (Ne.symm h)
      refine hA (e1 ▸ (filter_true_of_mem fun i hi hc => ?_).symm)
      exact notMem_empty i (card_eq_zero.1 (by omega : (A.filter (cpt ε₀)).card = 0) ▸ mem_filter.2 ⟨hi, hc⟩)
  | succ j ih =>
    intro x hx hr hbx
    obtain ⟨Y, _, _, EY, π, hY, hs, hπ, hac⟩ := hC n ε₀ V E hE
    have hK : ∀ a b, ∀ y ∈ LinearMap.ker π, EY a b y ∈ LinearMap.ker π := by
      intro a b y hy
      rw [LinearMap.mem_ker] at hy ⊢
      rw [hπ, hy, map_zero]
    let EK : Fin n → Fin n → Module.End ℂ (LinearMap.ker π) := fun a b => (EY a b).restrict (hK a b)
    have hι : ∀ a b y, (LinearMap.ker π).subtype (EK a b y) = EY a b ((LinearMap.ker π).subtype y) :=
      fun _ _ _ => rfl
    have hEK : KRel ε₀ EK := by
      intro a b c d h1 h2
      ext y
      have := LinearMap.congr_fun (hY a b c d h1 h2) (y : Y)
      split_ifs at this ⊢ <;> simpa [EK] using this
    classical
    let x' : Cn n Y := fun A => if x A = 0 then 0 else (hs (x A)).choose
    have hz : ∀ A, x A = 0 → x' A = 0 := fun A h => if_pos h
    have hx' : Sup ε₀ B (j + 1) x' := sup_of_supp hx hz
    have hr' : Ref ε₀ ε x' := fun A hA => hr A fun h => hA (hz A h)
    have hπx : lift n π x' = x := by
      funext A
      by_cases hA : x A = 0
      · simp [x', hA]
      · simp only [lift_apply, x', if_neg hA]
        exact (hs (x A)).choose_spec
    have hy : ∀ A, bd ε₀ EY x' A ∈ LinearMap.ker π := by
      intro A
      have := congrFun (lift_bd (ε := ε₀) π EY E (fun i _ => hπ _ _) x') A
      rw [hπx, hbx] at this
      exact this
    obtain ⟨s1, -, s3, -⟩ := differential_bounded_support n ε₀ Y EY
    obtain ⟨-, -, s3', -⟩ := differential_bounded_support n ε Y EY
    let y : Cn n (LinearMap.ker π) := fun A => ⟨_, hy A⟩
    have hιy : lift n (LinearMap.ker π).subtype y = bd ε₀ EY x' := rfl
    have hyd : Sup ε₀ B j y := sup_of_supp (s1 B j x' hx') fun A hA => Subtype.ext hA
    have hyr : Ref ε₀ ε y := fun A hA =>
      (s3' ε₀ x' h0 hr').2 A fun h => hA (Subtype.ext (by rw [← (s3' ε₀ x' h0 hr').1] at h; exact h))
    have hyb : bd ε₀ EK y = 0 := by
      have := lift_bd (ε := ε₀) _ EK EY (fun i _ => hι _ _) y
      rw [hιy, show bd ε₀ EY (bd ε₀ EY x') = 0 from LinearMap.congr_fun (hS n ε₀ Y EY hY) x'] at this
      funext A
      exact Subtype.ext (congrFun this A)
    obtain ⟨w, hw, hDw⟩ := ih _ EK hEK y hyd hyr hyb
    have hpush := congrArg (lift n (LinearMap.ker π).subtype) hDw
    have hl : ∀ {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (φ : V →ₗ[ℂ] W)
        (E : Fin n → Fin n → Module.End ℂ V) (F : Fin n → Fin n → Module.End ℂ W),
        (∀ a b x, φ (E a b x) = F a b (φ x)) → ∀ z : Cn n V,
        lift n φ (lift n (evK ε₀ E a) z) = lift n (evK ε₀ F a) (lift n φ z) :=
      fun φ E F h z => funext fun A => evK_inter φ E F h a _
    rw [map_sub, hl _ EK EY hι, lift_evd _ EK EY hι, lift_bd (ε := ε₀) _ EK EY (fun i _ => hι _ _), hιy] at hpush
    have c1 : bd ε₀ EY (lift n (evK ε₀ EY a) x') = lift n (evK ε₀ EY a) (bd ε₀ EY x') := by
      rw [(s3' ε₀ x' h0 hr').1, (s3' ε₀ _ h0 fun A hA => hr' A fun h => hA (by simp [h])).1]
      exact (lift_bd _ EY EY (fun i hi z => (LinearMap.congr_fun ((hab Y EY hY).1 i hi).eq z).symm) x').symm
    have c2 : bd ε₀ EY (evd (Ft ε₀ EY) b x') = evd (Ft ε₀ EY) b (bd ε₀ EY x') :=
      free_inter (bd ε₀ EY) _ _
        (fun c z => (LinearMap.congr_fun (differential_commutes_weight_operator n ε₀ ε₀ Y EY (fun _ _ h => h) hY c).eq z).symm) b x'
    obtain ⟨t, ht, hbt⟩ := hac B j
      (lift n (evK ε₀ EY a) x' - evd (Ft ε₀ EY) b x' - lift n (LinearMap.ker π).subtype w)
      (((sup_of_supp hx' fun A h => by simp [h]).sub
        (sup_of_supp hx' fun A h => by rw [evd_Ft_apply, h, map_zero])).sub (sup_of_supp hw fun A h => by simp [h]))
      (by rw [map_sub, map_sub, c1, c2, hpush, sub_self])
    refine ⟨lift n π t, sup_of_supp ht fun A h => by simp [h], ?_⟩
    have h2 : lift n π (lift n (LinearMap.ker π).subtype w) = 0 := by
      funext A
      exact (w A).2
    rw [← lift_bd π EY E (fun i _ => hπ _ _), hbt, map_sub, map_sub, h2, hl π EY E hπ, lift_evd π EY E hπ, hπx,
      sub_zero]

end CompanionTheory.D.LK
end
end

section
open Finset
open scoped InnerProductSpace

noncomputable section

namespace CompanionTheory.D.LK

open Car
open Formalism.REAL (GlRel KHighest IsWeight CasK)
open PI.UpqRep (rhoC nsq lowK)
open CompanionTheory.D.DSIC (KRel KUnit KStab)

variable {n : ℕ} {ε : Fin n → Bool}

section

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem casK_comm {E : Fin n → Fin n → Module.End ℂ V} (hE : KRel ε E) {c d : Fin n} (h : ε c = ε d) :
    Commute (E c d) (CasK ε E) :=
  _root_.UpperTheory.Reformulated.B.P6.r26a.PositivityTheory.D.LK.casK_comm hE h

theorem sum_pos {M : Type} [AddCommMonoid M] (f : Fin n → Fin n → M) :
    ∑ a, ∑ b, f a b = ∑ a, f a a + ∑ i : Pos n, (f i.1.1 i.1.2 + f i.1.2 i.1.1) := by
  have h : ∀ g : Fin n → Fin n → M, ∑ i : Pos n, g i.1.1 i.1.2 = ∑ a, ∑ b, if a < b then g a b else 0 := fun g => by
    rw [← Finset.sum_subtype (univ.filter fun p : Fin n × Fin n => p.1 < p.2) (by simp) fun p => g p.1 p.2,
      Finset.sum_filter, Fintype.sum_prod_type]
  rw [Finset.sum_add_distrib, h f, h fun a b => f b a, Finset.sum_comm (f := fun a b => if a < b then f b a else 0),
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib, show f a a = ∑ b, if a = b then f a b else 0 by simp, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rcases lt_trichotomy a b with h | h | h
  · simp [h, h.ne, h.not_gt]
  · simp [h]
  · simp [h, h.ne', h.not_gt]

theorem wt_sum (A : Finset (Pos n)) (c : Fin n) : wt A c = ∑ i ∈ A, al i c := by
  simp only [wt, al, Finset.sum_sub_distrib, card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

theorem casK_inN {E : Fin n → Fin n → Module.End ℂ V} (hE : KRel ε E) (x : V) :
    InN ε E (CasK ε E x - (∑ c, E c c (E c c x) - ∑ c, ((2 * rhoC ε c : ℝ) : ℂ) • E c c x)) := by
  refine ⟨fun i => (2 : ℂ) • E i.1.2 i.1.1 x, ?_⟩
  have e : ∑ c, ((2 * rhoC ε c : ℝ) : ℂ) • E c c x =
      ∑ i : Pos n, if cpt ε i then E i.1.1 i.1.1 x - E i.1.2 i.1.2 x else 0 := by
    have : ∀ c, 2 * rhoC ε c = ∑ i ∈ om ε, al i c := fun c => by rw [← wt_sum, wt_om]; rfl
    simp only [this, Complex.ofReal_sum, Finset.sum_smul]
    rw [Finset.sum_comm, ← Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [al, sub_smul, apply_ite ((↑) : ℝ → ℂ), ite_smul]
  rw [e, CasK, sum_pos]
  simp only [if_true, LinearMap.add_apply, LinearMap.sum_apply, Module.End.mul_apply]
  rw [add_sub_sub_cancel, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : cpt ε i
  · have := LinearMap.congr_fun (hE i.1.1 i.1.2 i.1.2 i.1.1 hi (Eq.symm hi)) x
    simp only [if_true, LinearMap.sub_apply, Module.End.mul_apply] at this
    rw [if_pos hi, if_pos hi, if_pos hi, if_pos (Eq.symm hi), ← this, map_smul, two_smul]
    simp only [Module.End.mul_apply]
    abel
  · rw [if_neg hi, if_neg hi, if_neg hi, if_neg fun h => hi h.symm]
    simp

theorem cok_of (hG : GenCO) : COK := by
  intro n ε V _ _ E hE B j τ x hx hτ hb
  let a : FreeAlgebra ℂ (Fin n × Fin n) :=
    ∑ c, ∑ d, if ε c = ε d then FreeAlgebra.ι ℂ (c, d) * FreeAlgebra.ι ℂ (d, c) else 0
  let b : FreeAlgebra ℂ (Fin n) :=
    ∑ c, FreeAlgebra.ι ℂ c * FreeAlgebra.ι ℂ c - ∑ c, ((2 * rhoC ε c : ℝ) : ℂ) • FreeAlgebra.ι ℂ c
  have ha : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V),
      evK ε E a = CasK ε E := fun V _ _ E => by
    simp only [a, CasK, map_sum]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    split_ifs with h
    · simp [evK, h]
    · exact map_zero _
  obtain ⟨w, hw, e⟩ := hG n ε ε a b (fun _ _ h => h) (fun V _ _ E hE => by
    rw [ha]
    refine ⟨fun i hi => casK_comm hE hi, fun x => ?_⟩
    simpa [b, evd, LinearMap.sum_apply] using casK_inN hE x) V E hE B j x hx (fun _ _ _ _ h => h) hb
  refine ⟨w, hw, ?_⟩
  rw [← e, ha, evd_eig _ _ _ hτ]
  congr 2
  simp only [b, map_sub, map_sum, map_mul, map_smul, FreeAlgebra.lift_ι_apply, smul_eq_mul, nsq, PI.UpqRep.dot,
    Pi.sub_apply, ← Finset.sum_sub_distrib]
  push_cast
  exact Finset.sum_congr rfl fun c _ => by ring

theorem wt_split (A : Finset (Pos n)) (c : Fin n) :
    wt A c = wt (A.filter (cpt ε)) c + wt (A.filter fun i => ¬cpt ε i) c := by
  rw [wt_sum, wt_sum, wt_sum, Finset.sum_filter_add_sum_filter_not]

theorem filter_all (A : Finset (Pos n)) : A.filter (cpt (allT n)) = A := filter_true_of_mem fun _ _ => rfl

end

theorem exists_poly {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (T : Module.End ℂ V)
    (hT : ∀ x y, ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ) (W : Submodule ℂ V) [FiniteDimensional ℂ W] (hW : ∀ x ∈ W, T x ∈ W) (s : ℝ) :
    ∃ q : Polynomial ℂ, ∀ x ∈ W, ∀ y, y = x + Polynomial.aeval T q (T x - (s : ℂ) • x) → T y = (s : ℂ) • y := by
  classical
  have hs : (T.restrict hW).IsSymmetric := fun x y => hT x y
  let ev := hs.eigenvalues rfl
  let p : Polynomial ℂ := Lagrange.basis (insert (s : ℂ) (univ.image fun i => (ev i : ℂ))) id (s : ℂ)
  have hp1 : p.eval (s : ℂ) = 1 := Lagrange.eval_basis_self (v := id) (Set.injOn_id _) (mem_insert_self _ _)
  obtain ⟨q, hq⟩ : Polynomial.X - Polynomial.C (s : ℂ) ∣ p - 1 := Polynomial.dvd_iff_isRoot.2 (by simp [hp1])
  refine ⟨q, fun x hx y hy => ?_⟩
  have e : y = Polynomial.aeval T p x := by
    rw [hy, eq_add_of_sub_eq' hq, mul_comm]
    simp [Module.algebraMap_end_apply]
  rw [e, show x = ∑ i, (hs.eigenvectorBasis rfl).repr ⟨x, hx⟩ i • (hs.eigenvectorBasis rfl i : V) by
    simpa using (congrArg Subtype.val ((hs.eigenvectorBasis rfl).sum_repr ⟨x, hx⟩)).symm]
  simp only [map_sum, map_smul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : T (hs.eigenvectorBasis rfl i : V) = (ev i : ℂ) • (hs.eigenvectorBasis rfl i : V) :=
    congrArg Subtype.val (hs.apply_eigenvectorBasis rfl i)
  rw [Module.End.aeval_apply_of_mem_apply_eq_smul h1, map_smul, h1]
  by_cases h : (ev i : ℂ) = s
  · rw [h]; module
  · have : p.eval (ev i : ℂ) = 0 := Lagrange.eval_basis_of_ne (v := id) (Ne.symm h)
      (mem_insert_of_mem (mem_image_of_mem _ (mem_univ i)))
    simp [this]

theorem vanK_of (hC : COK) (hP : WtProj) (hM : WtMajor) : VanK := by
  intro n ε lam V _ _ E hl hE hU hF hmin B j z hB hz hwt hb
  set τ := lowK ε lam + (2 : ℝ) • rhoC ε with hτ
  have hzw : ∀ A, IsWeight E (τ - wt A) (z A) := fun A c => by
    have := congrFun (hwt c) A
    rw [Ft_apply, filter_all, Pi.smul_apply] at this
    rw [eq_sub_of_add_eq this, Pi.sub_apply, Complex.ofReal_sub, sub_smul]
  obtain ⟨w, hw, e⟩ := hC n ε V E hE B j (τ - wt B) z hz (fun c => funext fun A => by
    by_cases h : z A = 0
    · simp [Ft_apply, h]
    · rw [Ft_apply, hzw A c, Pi.smul_apply, ← add_smul, Pi.sub_apply, Pi.sub_apply, wt_split (ε := ε) A, (hz A h).1]
      congr 1; push_cast; ring) hb
  choose S hS hSt hmem using hF
  let W : Submodule ℂ V := ⨆ A, S (z A)
  haveI : ∀ A, FiniteDimensional ℂ (S (z A)) := fun A => hS _
  have hWs : KStab ε E W := fun a b h v hv =>
    (iSup_le fun A y hy => Submodule.mem_iSup_of_mem A (hSt _ a b h y hy) : W ≤ W.comap (E a b)) hv
  obtain ⟨q, hq⟩ := exists_poly (CasK ε E) (fun x y => by
      simp only [CasK, LinearMap.sum_apply, sum_inner, inner_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      split_ifs with h
      · rw [Module.End.mul_apply, Module.End.mul_apply, hU a b h, hU b a h.symm]
      · simp) W (fun x hx => by
      simp only [CasK, LinearMap.sum_apply]
      refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => ?_
      split_ifs with h
      · exact hWs a b h _ (hWs b a h.symm _ hx)
      · simp) (nsq (τ - wt B - rhoC ε) - nsq (rhoC ε))
  have hcq : ∀ c d, ε c = ε d → ∀ x, Polynomial.aeval (CasK ε E) q (E c d x) = E c d (Polynomial.aeval (CasK ε E) q x) :=
    fun c d h x => by
      have : Commute (E c d) (Polynomial.aeval (CasK ε E) q) := by
        rw [Polynomial.aeval_eq_sum_range]
        exact Commute.sum_right _ _ _ fun k _ => ((casK_comm hE h).pow_right k).smul_right _
      exact (LinearMap.congr_fun this.eq x).symm
  have h0 : z + lift n (Polynomial.aeval (CasK ε E) q) (bd ε E w) = 0 := by
    funext A
    by_contra hne
    rw [← e] at hne
    have hA : z A ≠ 0 := fun h => hne (by simp [h])
    obtain ⟨ν, y, hy0, hy, hs, hd, hc⟩ := hM n ε V E hE hU (fun x => ⟨S x, hS x, hSt x, hmem x⟩) (τ - wt A) _ _ hne
      (fun c => by
        simp only [Pi.add_apply, lift_apply, Pi.sub_apply, Pi.smul_apply]
        rw [map_add, ← hcq c c rfl, map_sub, map_smul, ← Module.End.mul_apply, (casK_comm hE rfl).eq,
          Module.End.mul_apply, hzw A c]
        simp only [map_smul, map_sub, smul_add, smul_sub, Pi.sub_apply, smul_comm ((τ c - wt A c : ℝ) : ℂ)])
      (hq (z A) (Submodule.mem_iSup_of_mem A (hmem _)) _ rfl)
    have hA1 := (hz A hA).1
    refine absurd (hmin ν y hy0 hy) (not_le.2 (K_type_count n ε lam ν B (A.filter (cpt ε)) hl hB
      (fun i hi => (mem_filter.1 (hA1.symm ▸ hi :)).2) (fun i hi => (mem_filter.1 hi).2) hd (fun w hw' => ?_) ?_))
    · convert hc w hw' using 2
      funext c
      simp only [Pi.sub_apply, wt_split (ε := ε) A, hA1, hτ]
      ring
    · have h1 : nsq (τ - wt B - rhoC ε) = nsq (ν + rhoC ε) := by
        have := Complex.ofReal_injective hs
        linarith
      rw [← h1]
      congr 1
      rw [hτ, two_smul]
      abel
  have h1 : bd ε E (-lift n (Polynomial.aeval (CasK ε E) q) w) = z := by
    rw [map_neg, ← lift_bd _ E E fun i hi x => hcq _ _ hi x]
    exact (eq_neg_of_add_eq_zero_left h0).symm
  obtain ⟨t, ht1, ht2, ht3⟩ := hP n (allT n) ε V E hE hU (fun x => ⟨S x, hS x, hSt x, hmem x⟩) (bd ε E)
    (differential_commutes_weight_operator n _ ε V E (fun _ _ _ => rfl) hE) τ _ (h1.symm ▸ hwt)
  exact ⟨t, sup_of_supp hw fun A h => ht3 A (by simp [h]), ht1, ht2.trans h1⟩

theorem inj_of (hV : VanK) (hP : WtProj) (hS : BdSq) : Inj := by
  intro n ε lam V _ _ E hl hgl hU hF hmin u y hu hy hb
  have hE : KRel ε E := fun a b c d _ _ => hgl a b c d
  have hA : KRel (allT n) E := fun a b c d _ _ => hgl a b c d
  set τ := lowK ε lam + (2 : ℝ) • rhoC ε with hτ
  have hc := differential_commutes_weight_operator n _ (allT n) V E (fun _ _ h => h) hA
  obtain ⟨-, -, -, s4⟩ := differential_bounded_support n ε V E
  have main : ∀ N (y : Cn n V), (∀ A, y A ≠ 0 → A.card = (om ε).card + 1 ∧ pot (A.filter fun i => ¬cpt ε i) < N) →
      Wt (allT n) E τ y → bd (allT n) E y = Pi.single (om ε) u → u = 0 := by
    intro N
    induction N with
    | zero =>
      intro y h _ hb
      obtain rfl : y = 0 := funext fun A => by by_contra h'; exact Nat.not_lt_zero _ (h A h').2
      simpa using (congrFun hb (om ε)).symm
    | succ N ih =>
      intro y h hw hb
      let r : Finset (Pos n) → Cn n V := fun B A => if (A.filter fun i => ¬cpt ε i) = B then y A else 0
      have hr : ∀ B, Sup ε B ((om ε).card + 1 - B.card) (r B) := fun B A hA => by
        obtain ⟨h1, h2⟩ : (A.filter fun i => ¬cpt ε i) = B ∧ y A ≠ 0 := by
          simp only [r] at hA
          split_ifs at hA with h1
          · exact ⟨h1, hA⟩
          · exact absurd rfl hA
        have := card_filter_add_card_filter_not (s := A) (cpt ε)
        have := (h A h2).1
        exact ⟨h1, by rw [← h1]; omega⟩
      have hsum : y = ∑ B, r B := funext fun A => by simp [r, Finset.sum_apply]
      have hrne : ∀ B A, r B A ≠ 0 → pot B < N + 1 ∧ B.Nonempty ∧ B.card ≤ (om ε).card + 1 := fun B A hA => by
        have h2 : y A ≠ 0 := fun h' => hA (by simp [r, h'])
        have h3 := (hr B A hA).1
        have h4 := h A h2
        refine ⟨h3 ▸ h4.2, nonempty_iff_ne_empty.2 fun hB => ?_, h4.1 ▸ h3 ▸ card_filter_le _ _⟩
        have : A ⊆ om ε := fun i hi => mem_filter.2 ⟨mem_univ _, by
          by_contra hc; exact notMem_empty i (hB ▸ h3 ▸ mem_filter.2 ⟨hi, hc⟩)⟩
        have := card_le_card this
        omega
      have hex : ∀ B, ∃ t : Cn n V, Wt (allT n) E τ t ∧ (pot B = N → bd ε E t = r B) ∧ (pot B ≠ N → t = 0) ∧
          (t = 0 ∨ (B.card ≤ (om ε).card + 1 ∧ Sup ε B ((om ε).card + 1 - B.card + 1) t)) := by
        intro B
        by_cases h0 : pot B = N ∧ r B ≠ 0
        · obtain ⟨A₀, hA₀⟩ := Function.ne_iff.1 h0.2
          obtain ⟨-, hBn, hBc⟩ := hrne B A₀ hA₀
          obtain ⟨t, t1, t2, t3⟩ := hV n ε lam V E hl hE hU hF hmin B _ (r B) hBn (hr B) (fun c => funext fun A => by
              have := congrFun (hw c) A
              simp only [Ft_apply, Pi.smul_apply, r] at this ⊢
              split_ifs
              · exact this
              · simp) (funext fun A => by
              by_contra hne
              have hAB := (sup_bd E (hr B) hne).1
              have e := congrFun hb A
              have hAo : A ≠ om ε := by
                rintro rfl
                obtain ⟨i, hi⟩ := hBn
                rw [← hAB] at hi
                exact (mem_filter.1 hi).2 (mem_filter.1 (mem_filter.1 hi).1).2
              rw [Pi.single_eq_of_ne hAo, hsum, map_sum, Finset.sum_apply, Finset.sum_eq_single B] at e
              · apply hne
                by_contra h'
                have := (s4 B _ _ (hr B) A (by rw [Pi.sub_apply, e, zero_sub]; exact neg_ne_zero.2 hne)).1
                rw [hAB] at this
                exact lt_irrefl _ this
              · intro B' _ hB'
                by_cases h1 : r B' = 0
                · simp [h1]
                obtain ⟨A₁, hA₁⟩ := Function.ne_iff.1 h1
                have h2 := (hrne B' A₁ hA₁).1
                have h3 : bd ε E (r B') A = 0 := by
                  by_contra h3; exact hB' ((sup_bd E (hr B') h3).1.symm.trans hAB)
                by_contra h4
                have := (s4 B' _ _ (hr B') A (by rw [Pi.sub_apply, h3, sub_zero]; exact h4)).1
                rw [hAB] at this
                omega
              · simp)
          exact ⟨t, t2, fun _ => t3, fun h => absurd h0.1 h, Or.inr ⟨hBc, t1⟩⟩
        · refine ⟨0, fun c => by simp, fun h => ?_, fun _ => rfl, Or.inl rfl⟩
          rw [map_zero]
          by_contra h'
          exact h0 ⟨h, Ne.symm h'⟩
      choose t t1 t2 t3 t4 using hex
      refine ih (y - ∑ B, bd (allT n) E (t B)) (fun A hA => ?_) (fun c => ?_) ?_
      · have e : (y - ∑ B, bd (allT n) E (t B)) A =
            ∑ B, ((if pot B = N then 0 else r B A) - (bd (allT n) E (t B) - bd ε E (t B)) A) := by
          rw [Pi.sub_apply, congrFun hsum A, Finset.sum_apply, Finset.sum_apply, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun B _ => ?_
          split_ifs with h1
          · rw [Pi.sub_apply, t2 B h1]; abel
          · simp [t3 B h1]
        rw [e] at hA
        obtain ⟨B, -, hB⟩ := exists_ne_zero_of_sum_ne_zero hA
        by_cases h1 : pot B = N
        · rw [if_pos h1, zero_sub, neg_ne_zero] at hB
          rcases t4 B with h2 | h2
          · simp [h2] at hB
          · have := s4 B _ _ h2.2 A hB
            have := h2.1
            omega
        · rw [if_neg h1, t3 B h1] at hB
          have hB' : r B A ≠ 0 := by simpa using hB
          have h2 := (hrne B A hB').1
          have h3 := (hr B A hB').1
          exact ⟨(h A fun h' => hB' (by simp [r, h'])).1, by rw [h3]; omega⟩
      · rw [map_sub, map_sum, hw c, smul_sub, Finset.smul_sum]
        congr 1
        refine Finset.sum_congr rfl fun B _ => ?_
        rw [← Module.End.mul_apply, (hc c).eq, Module.End.mul_apply, t1 B c, map_smul]
      · rw [map_sub, map_sum, hb, Finset.sum_eq_zero, sub_zero]
        exact fun B _ => LinearMap.congr_fun (hS n _ V E hA) _
  obtain ⟨y', y1, y2, y3⟩ := hP n (allT n) ε V E hE hU hF _ hc τ y (fun c => funext fun A => by
    rw [hb, Ft_apply, filter_all]
    by_cases e : A = om ε
    · subst e
      rw [Pi.smul_apply, Pi.single_eq_same, hu c, wt_om, ← add_smul, hτ]
      simp
    · simp [Pi.single_eq_of_ne e])
  refine main ((univ.sup fun A : Finset (Pos n) => pot A) + 1) y' (fun A hA => ⟨?_, ?_⟩) y1 (y2.trans hb)
  · have := (hy A fun h => hA (y3 A h)).2
    rwa [filter_all] at this
  · exact Nat.lt_succ_of_le (Finset.le_sup (f := fun A : Finset (Pos n) => pot A) (mem_univ _))

end CompanionTheory.D.LK
end
end
