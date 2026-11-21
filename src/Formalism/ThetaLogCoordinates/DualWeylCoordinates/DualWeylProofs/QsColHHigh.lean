import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QsMnTranspose
import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.BCoreT

section
noncomputable section

open Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

variable {n : ℕ}

def qs_rem (D : Finset ℤ) (K : ℤ → Finset (Fin n)) (m : ↥D → Fin n) : ℤ → Finset (Fin n) :=
  fun c => if h : c ∈ D then (K c).erase (m ⟨c, h⟩) else K c

def qs_add (D : Finset ℤ) (J : ℤ → Finset (Fin n)) (a : ↥D → Fin n) : ℤ → Finset (Fin n) :=
  fun c => if h : c ∈ D then insert (a ⟨c, h⟩) (J c) else J c

lemma qs_rem_mem (D : Finset ℤ) (K : ℤ → Finset (Fin n)) (m : ↥D → Fin n) (c : ↥D) :
    qs_rem D K m c.1 = (K c.1).erase (m c) := by simp [qs_rem, c.2]

lemma qs_rem_not (D : Finset ℤ) (K : ℤ → Finset (Fin n)) (m : ↥D → Fin n) {c : ℤ} (hc : c ∉ D) :
    qs_rem D K m c = K c := by simp [qs_rem, hc]

lemma qs_add_mem (D : Finset ℤ) (K : ℤ → Finset (Fin n)) (m : ↥D → Fin n) (c : ↥D) :
    qs_add D K m c.1 = insert (m c) (K c.1) := by simp [qs_add, c.2]

lemma qs_add_not (D : Finset ℤ) (K : ℤ → Finset (Fin n)) (m : ↥D → Fin n) {c : ℤ} (hc : c ∉ D) :
    qs_add D K m c = K c := by simp [qs_add, hc]

lemma qs_rem_iff_add (D : Finset ℤ) (J K : ℤ → Finset (Fin n)) (m : ↥D → Fin n) :
    ((∀ c : ↥D, m c ∈ K c.1) ∧ J = qs_rem D K m) ↔ ((∀ c : ↥D, m c ∉ J c.1) ∧ K = qs_add D J m) := by
  constructor
  · rintro ⟨h1, rfl⟩
    refine ⟨fun c => by rw [qs_rem_mem]; simp, ?_⟩
    funext c
    by_cases hc : c ∈ D
    · have := qs_add_mem D (qs_rem D K m) m ⟨c, hc⟩
      have h2 := qs_rem_mem D K m ⟨c, hc⟩
      simp only at this h2
      rw [this, h2, Finset.insert_erase (h1 ⟨c, hc⟩)]
    · rw [qs_add_not _ _ _ hc, qs_rem_not _ _ _ hc]
  · rintro ⟨h1, rfl⟩
    refine ⟨fun c => by rw [qs_add_mem]; simp, ?_⟩
    funext c
    by_cases hc : c ∈ D
    · have := qs_rem_mem D (qs_add D J m) m ⟨c, hc⟩
      have h2 := qs_add_mem D J m ⟨c, hc⟩
      simp only at this h2
      rw [this, h2, Finset.erase_insert (h1 ⟨c, hc⟩)]
    · rw [qs_rem_not _ _ _ hc, qs_add_not _ _ _ hc]

variable {R : Type*} [CommRing R]

lemma qs_prod_split (S D : Finset ℤ) (hD : D ⊆ S) (F : ℤ → R) :
    ∏ c ∈ S, F c = (∏ c ∈ S \ D, F c) * ∏ c : ↥D, F c.1 := by
  rw [← Finset.prod_sdiff hD, Finset.prod_coe_sort]

lemma qs_sum_choices (S D : Finset ℤ) (hD : D ⊆ S) (u : ℤ → R) (p : ↥D → Fin n → Prop) [∀ c x, Decidable (p c x)]
    (s w : ↥D → Fin n → R) (F : (↥D → Fin n) → ℤ → R)
    (hF1 : ∀ m, ∀ c ∈ S \ D, F m c = u c) (hF2 : ∀ m (c : ↥D), F m c.1 = w c (m c))
    (v : ↥D → Fin n → R) :
    ∑ m : ↥D → Fin n, (if ∀ c, p c (m c) then (∏ c, s c (m c)) * (∏ c ∈ S, F m c) * ∏ c, v c (m c) else 0) =
      (∏ c ∈ S \ D, u c) * ∏ c : ↥D, ∑ x, if p c x then s c x * w c x * v c x else 0 := by
  rw [Fintype.prod_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Fintype.prod_ite_zero]
  split_ifs with h
  · rw [qs_prod_split S D hD, Finset.prod_congr rfl (hF1 m), Finset.prod_congr rfl (fun c _ => hF2 m c),
      Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    ring
  · rw [mul_zero]

variable (g : Matrix (Fin n) (Fin n) R)

theorem qs_core (S D : Finset ℤ) (hD : D ⊆ S) (J K : ℤ → Finset (Fin n)) (a : ↥D → Fin n) :
    ∑ m : ↥D → Fin n, (if ∀ c : ↥D, m c ∈ K c.1 then
        (∏ c : ↥D, ((qs_sg ((K c.1).erase (m c)) (m c) : ℤ) : R)) * (∏ c ∈ S, qs_mn g (J c) (qs_rem D K m c)) *
          ∏ c : ↥D, g (a c) (m c) else 0) =
      if ∀ c : ↥D, a c ∉ J c.1 then
        (∏ c : ↥D, ((qs_sg (J c.1) (a c) : ℤ) : R)) * ∏ c ∈ S, qs_mn g (qs_add D J a c) (K c) else 0 := by
  rw [qs_sum_choices S D hD (fun c => qs_mn g (J c) (K c)) (fun c x => x ∈ K c.1)
    (fun c x => ((qs_sg ((K c.1).erase x) x : ℤ) : R)) (fun c x => qs_mn g (J c.1) ((K c.1).erase x))
    (fun m c => qs_mn g (J c) (qs_rem D K m c))
    (fun m c hc => by rw [qs_rem_not _ _ _ (Finset.mem_sdiff.1 hc).2]) (fun m c => by rw [qs_rem_mem])]
  have h1 : ∀ c : ↥D, (∑ x, if x ∈ K c.1 then ((qs_sg ((K c.1).erase x) x : ℤ) : R) *
      qs_mn g (J c.1) ((K c.1).erase x) * g (a c) x else 0) =
      if a c ∉ J c.1 then ((qs_sg (J c.1) (a c) : ℤ) : R) * qs_mn g (insert (a c) (J c.1)) (K c.1) else 0 := by
    intro c
    rw [Finset.sum_ite_mem, Finset.univ_inter, qs_laplace, ite_not]
  rw [Finset.prod_congr rfl (fun c _ => h1 c), Fintype.prod_ite_zero]
  split_ifs with h
  · have e1 : ∏ c ∈ S \ D, qs_mn g (qs_add D J a c) (K c) = ∏ c ∈ S \ D, qs_mn g (J c) (K c) :=
      Finset.prod_congr rfl (fun c hc => by rw [qs_add_not _ _ _ (Finset.mem_sdiff.1 hc).2])
    have e2 : ∏ c : ↥D, qs_mn g (qs_add D J a c.1) (K c.1) = ∏ c : ↥D, qs_mn g (insert (a c) (J c.1)) (K c.1) :=
      Finset.prod_congr rfl (fun c _ => by rw [qs_add_mem])
    rw [qs_prod_split S D hD (fun c => qs_mn g (qs_add D J a c) (K c)), e1, e2, Finset.prod_mul_distrib]
    ring
  · rw [mul_zero]

theorem qs_laplace_inv (g' : Matrix (Fin n) (Fin n) R) (hg : g * g' = 1) (J K : Finset (Fin n)) (a : Fin n) :
    ∑ m, (if m ∉ K then ((qs_sg K m : ℤ) : R) * qs_mn g J (insert m K) * g' m a else 0) =
      if a ∈ J then ((qs_sg (J.erase a) a : ℤ) : R) * qs_mn g (J.erase a) K else 0 := by
  have h1 : ∀ m, (if m ∉ K then ((qs_sg K m : ℤ) : R) * qs_mn g J (insert m K) * g' m a else 0) =
      ∑ k ∈ J, ((qs_sg (J.erase k) k : ℤ) : R) * qs_mn g (J.erase k) K * (g k m * g' m a) := by
    intro m
    have := qs_laplace_col g J K m
    rw [← ite_not] at this
    calc _ = (if m ∉ K then ((qs_sg K m : ℤ) : R) * qs_mn g J (insert m K) else 0) * g' m a := by
          split_ifs <;> simp
      _ = _ := by rw [← this, Finset.sum_mul]; exact Finset.sum_congr rfl fun k _ => by ring
  rw [Finset.sum_congr rfl (fun m _ => h1 m), Finset.sum_comm]
  have h2 : ∀ k, ∑ m, g k m * g' m a = if k = a then 1 else 0 := by
    intro k
    have := congrFun (congrFun hg k) a
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    exact this
  simp_rw [← Finset.mul_sum, h2]
  simp [Finset.sum_ite_eq']

theorem qs_core_inv (g' : Matrix (Fin n) (Fin n) R) (hg : g * g' = 1) (S D : Finset ℤ) (hD : D ⊆ S)
    (J K : ℤ → Finset (Fin n)) (a : ↥D → Fin n) :
    ∑ m : ↥D → Fin n, (if ∀ c : ↥D, m c ∉ K c.1 then
        (∏ c : ↥D, ((qs_sg (K c.1) (m c) : ℤ) : R)) * (∏ c ∈ S, qs_mn g (J c) (qs_add D K m c)) *
          ∏ c : ↥D, g' (m c) (a c) else 0) =
      if ∀ c : ↥D, a c ∈ J c.1 then
        (∏ c : ↥D, ((qs_sg ((J c.1).erase (a c)) (a c) : ℤ) : R)) * ∏ c ∈ S, qs_mn g (qs_rem D J a c) (K c)
      else 0 := by
  rw [qs_sum_choices S D hD (fun c => qs_mn g (J c) (K c)) (fun c x => x ∉ K c.1)
    (fun c x => ((qs_sg (K c.1) x : ℤ) : R)) (fun c x => qs_mn g (J c.1) (insert x (K c.1)))
    (fun m c => qs_mn g (J c) (qs_add D K m c))
    (fun m c hc => by rw [qs_add_not _ _ _ (Finset.mem_sdiff.1 hc).2]) (fun m c => by rw [qs_add_mem])
    (fun c x => g' x (a c))]
  rw [Finset.prod_congr rfl (fun c _ => qs_laplace_inv g g' hg (J c.1) (K c.1) (a c)), Fintype.prod_ite_zero]
  split_ifs with h
  · have e1 : ∏ c ∈ S \ D, qs_mn g (qs_rem D J a c) (K c) = ∏ c ∈ S \ D, qs_mn g (J c) (K c) :=
      Finset.prod_congr rfl (fun c hc => by rw [qs_rem_not _ _ _ (Finset.mem_sdiff.1 hc).2])
    have e2 : ∏ c : ↥D, qs_mn g (qs_rem D J a c.1) (K c.1) = ∏ c : ↥D, qs_mn g ((J c.1).erase (a c)) (K c.1) :=
      Finset.prod_congr rfl (fun c _ => by rw [qs_rem_mem])
    rw [qs_prod_split S D hD (fun c => qs_mn g (qs_rem D J a c) (K c)), e1, e2, Finset.prod_mul_distrib]
    ring
  · rw [mul_zero]

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end

section
noncomputable section

open MvPolynomial Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

variable {n : ℕ}

def qs_cnt {ι : Type*} [Fintype ι] (a : ι → Fin n) (x : Fin n) : ℕ := (univ.filter fun c => a c = x).card

def qs_SM {A : Type*} [CommRing A] (G : Matrix (Fin n) (Fin n) A) (b : ℕ) : Matrix (SymIdx n b) (SymIdx n b) A :=
  fun α β => MvPolynomial.coeff (symMono α) (∏ m : Fin n, (∑ a : Fin n, MvPolynomial.C (G a m) * X a) ^ (β.1 m : ℕ))

lemma qs_sum_cnt {ι : Type*} [Fintype ι] (a : ι → Fin n) : ∑ x, qs_cnt a x = Fintype.card ι := by
  classical
  simp only [qs_cnt]
  rw [← Finset.card_eq_sum_card_fiberwise (f := a) (s := univ) (t := univ) (fun _ _ => by simp)]
  simp

lemma qs_sym_mul {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Type*} [CommRing A] (G : Matrix (Fin n) (Fin n) A)
    (m : ι → Fin n) (β : Fin n → ℕ) (hβ : ∀ x, qs_cnt m x = β x) (α : Fin n →₀ ℕ) :
    MvPolynomial.coeff α (∏ x : Fin n, (∑ a : Fin n, MvPolynomial.C (G a x) * X a) ^ (β x)) =
      ∑ a : ι → Fin n, if (∀ x, qs_cnt a x = α x) then ∏ c, G (a c) (m c) else 0 := by
  classical
  have h1 : (∏ x : Fin n, (∑ a : Fin n, (MvPolynomial.C (G a x) * X a : MvPolynomial (Fin n) A)) ^ (β x)) =
      ∏ c : ι, ∑ a : Fin n, MvPolynomial.C (G a (m c)) * X a := by
    rw [← Finset.prod_fiberwise (s := univ) (g := m)]
    refine Finset.prod_congr rfl fun x _ => ?_
    rw [Finset.prod_congr rfl (g := fun _ => ∑ a : Fin n, (MvPolynomial.C (G a x) * X a : MvPolynomial (Fin n) A))
      (fun c hc => by rw [(Finset.mem_filter.1 hc).2]), Finset.prod_const, ← hβ x]
    rfl
  rw [h1, Fintype.prod_sum, MvPolynomial.coeff_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have h2 : (∏ c : ι, (MvPolynomial.C (G (a c) (m c)) * X (a c) : MvPolynomial (Fin n) A)) =
      MvPolynomial.monomial (∑ c : ι, Finsupp.single (a c) 1) (∏ c, G (a c) (m c)) := by
    rw [MvPolynomial.monomial_sum_prod]
    refine Finset.prod_congr rfl fun c _ => ?_
    rw [MvPolynomial.C_mul_X_eq_monomial]
  rw [h2, MvPolynomial.coeff_monomial]
  have h3 : (∑ c : ι, Finsupp.single (a c) 1 = α) ↔ ∀ x, qs_cnt a x = α x := by
    rw [Finsupp.ext_iff]
    refine forall_congr' fun x => ?_
    rw [Finsupp.finsetSum_apply, qs_cnt, Finset.card_filter]
    simp only [Finsupp.single_apply]
  simp only [h3]

def qs_mon {ι : Type*} [Fintype ι] {b : ℕ} (hb : Fintype.card ι = b) (m : ι → Fin n) : SymIdx n b :=
  ⟨fun x => ⟨qs_cnt m x, by
    have := qs_sum_cnt m
    have h2 : qs_cnt m x ≤ ∑ x, qs_cnt m x := Finset.single_le_sum (f := qs_cnt m) (fun _ _ => Nat.zero_le _) (Finset.mem_univ x)
    omega⟩, by simpa using (qs_sum_cnt m).trans hb⟩

theorem qs_sum_sym {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Type*} [CommRing A] (G : Matrix (Fin n) (Fin n) A) {b : ℕ}
    (hb : Fintype.card ι = b) (m : ι → Fin n) (α : SymIdx n b) (r : A) :
    ∑ β : SymIdx n b, qs_SM G b α β * (if (∀ x, qs_cnt m x = (β.1 x : ℕ)) then r else 0) =
      (∑ a : ι → Fin n, if (∀ x, qs_cnt a x = (α.1 x : ℕ)) then ∏ c, G (a c) (m c) else 0) * r := by
  classical
  rw [Finset.sum_eq_single (qs_mon hb m)]
  · have h0 : ∀ x, qs_cnt m x = ((qs_mon hb m).1 x : ℕ) := fun x => rfl
    rw [if_pos h0]
    congr 1
    exact qs_sym_mul G m _ h0 (symMono α)
  · intro β _ hβ
    rw [if_neg, mul_zero]
    intro h
    exact hβ (Subtype.ext (funext fun x => Fin.ext (h x).symm))
  · intro h; exact absurd (Finset.mem_univ _) h

def qs_gC (n : ℕ) : Matrix (Fin n) (Fin n) (GLCoord ℤ n) :=
  Matrix.of fun a b => algebraMap _ (GLCoord ℤ n) (genMat ℤ n a b)

def qs_gI (n : ℕ) : Matrix (Fin n) (Fin n) (GLCoord ℤ n) := Matrix.of fun a b => ginvC n a b

lemma qs_SymMat_eq (n b : ℕ) : SymMat n b = qs_SM (qs_gC n) b := rfl

lemma qs_SymDMat_eq (n b : ℕ) : SymDMat n b = qs_SM (qs_gI n).transpose b := rfl

lemma qs_gC_mul_gI (n : ℕ) : qs_gC n * qs_gI n = 1 := by
  have h1 : qs_gC n = (genMat ℤ n).map (algebraMap _ (GLCoord ℤ n)) := rfl
  have h2 : qs_gI n = (((detU n)⁻¹ : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) •
      ((genMat ℤ n).adjugate).map (algebraMap _ (GLCoord ℤ n)) := by
    ext a b; simp [qs_gI, ginvC]
  rw [h1, h2, Matrix.mul_smul, ← Matrix.map_mul, Matrix.mul_adjugate]
  ext a b
  by_cases hab : a = b
  · subst hab
    simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    exact (detU n).inv_mul
  · simp [Matrix.one_apply_ne hab]

lemma qs_SM_diag {A : Type*} [CommRing A] (d : Fin n → A) (b : ℕ) (α β : SymIdx n b) :
    qs_SM (Matrix.diagonal d) b α β = if α = β then ∏ x, d x ^ (β.1 x : ℕ) else 0 := by
  classical
  have h1 : ∀ x : Fin n, (∑ a : Fin n, (MvPolynomial.C (Matrix.diagonal d a x) * X a : MvPolynomial (Fin n) A)) =
      MvPolynomial.monomial (Finsupp.single x 1) (d x) := by
    intro x
    rw [Finset.sum_eq_single x]
    · rw [Matrix.diagonal_apply_eq, MvPolynomial.C_mul_X_eq_monomial]
    · intro a _ ha; rw [Matrix.diagonal_apply_ne _ ha]; simp
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [qs_SM]
  simp_rw [h1, MvPolynomial.monomial_pow]
  rw [← MvPolynomial.monomial_sum_prod, MvPolynomial.coeff_monomial]
  have h3 : (∑ x : Fin n, (β.1 x : ℕ) • Finsupp.single x 1 = symMono α) ↔ α = β := by
    rw [Finsupp.ext_iff]
    constructor
    · intro h
      refine Subtype.ext (funext fun x => Fin.ext ?_)
      have := h x
      rw [Finsupp.finsetSum_apply] at this
      simp only [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
      exact this.symm
    · rintro rfl x
      rw [Finsupp.finsetSum_apply]
      simp only [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rfl
  simp only [h3]

lemma qs_SM_map {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (G : Matrix (Fin n) (Fin n) A) (b : ℕ)
    (α β : SymIdx n b) : f (qs_SM G b α β) = qs_SM (G.map f) b α β := by
  rw [qs_SM, qs_SM, ← MvPolynomial.coeff_map]
  simp [map_prod, map_pow, map_sum]

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end

section
noncomputable section

open Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

variable {n : ℕ} [NeZero n]

def qs_ext (mu : Fin n → ℤ) (I : TIdx mu) : ℤ → Finset (Fin n) :=
  fun c => if h : c ∈ TCols mu then (I ⟨c, h⟩).1 else if c ≤ mu (lastIdx n) then univ else ∅

lemma qs_ext_mem (mu : Fin n → ℤ) (I : TIdx mu) (c : ↥(TCols mu)) : qs_ext mu I c.1 = (I c).1 := by
  simp [qs_ext, c.2]

lemma qs_colH_low {mu : Fin n → ℤ} (hmu : Dominant mu) {c : ℤ} (hc : c ≤ mu (lastIdx n)) : colH mu c = n := by
  unfold colH
  rw [Finset.filter_true_of_mem (fun m _ => hc.trans (hmu (qb_le_lastIdx m)))]; simp

lemma qs_colH_high {mu : Fin n → ℤ} (hmu : Dominant mu) {c : ℤ} (hc : mu 0 < c) : colH mu c = 0 := by
  unfold colH
  rw [Finset.filter_false_of_mem (fun m _ => by have := hmu (Fin.zero_le m); omega)]; simp

lemma qs_ext_card {mu : Fin n → ℤ} (hmu : Dominant mu) (I : TIdx mu) (c : ℤ) :
    (qs_ext mu I c).card = colH mu c := by
  unfold qs_ext
  split_ifs with h1 h2
  · exact (I ⟨c, h1⟩).2
  · rw [qs_colH_low hmu h2]; simp
  · rw [qs_colH_high hmu (by simp only [TCols, mem_Ioc] at h1; omega)]; simp

def qs_res (mu : Fin n → ℤ) (F : ℤ → Finset (Fin n)) (hF : ∀ c, (F c).card = colH mu c) : TIdx mu :=
  fun c => ⟨F c.1, hF c.1⟩

lemma qs_ext_res {mu : Fin n → ℤ} (hmu : Dominant mu) (F : ℤ → Finset (Fin n))
    (hF : ∀ c, (F c).card = colH mu c) : qs_ext mu (qs_res mu F hF) = F := by
  funext c
  unfold qs_ext
  split_ifs with h1 h2
  · rfl
  · symm; apply Finset.eq_univ_of_card; rw [hF, qs_colH_low hmu h2]; simp
  · symm; rw [← Finset.card_eq_zero, hF, qs_colH_high hmu (by simp only [TCols, mem_Ioc] at h1; omega)]

lemma qs_ext_inj (mu : Fin n → ℤ) : Function.Injective (qs_ext mu) := by
  intro I I' h
  funext c
  apply Subtype.ext
  rw [← qs_ext_mem, ← qs_ext_mem, h]

lemma qs_collapse {M : Type*} [AddCommMonoid M] {mu : Fin n → ℤ} (hmu : Dominant mu) (P : Prop) [Decidable P]
    (F : ℤ → Finset (Fin n)) (hF : P → ∀ c, (F c).card = colH mu c) (f : (ℤ → Finset (Fin n)) → M)
    [∀ I : TIdx mu, Decidable (P ∧ qs_ext mu I = F)] :
    ∑ I : TIdx mu, (if P ∧ qs_ext mu I = F then f (qs_ext mu I) else 0) = if P then f F else 0 := by
  classical
  split_ifs with hP
  · rw [Finset.sum_eq_single (qs_res mu F (hF hP))]
    · rw [if_pos ⟨hP, qs_ext_res hmu F (hF hP)⟩, qs_ext_res hmu]
    · intro I _ hI
      rw [if_neg]
      rintro ⟨_, h⟩
      exact hI (qs_ext_inj mu (by rw [h, qs_ext_res hmu]))
    · intro h; exact absurd (Finset.mem_univ _) h
  · exact Finset.sum_eq_zero fun I _ => if_neg fun h => hP h.1

def qs_ini (h : ℕ) : Finset (Fin n) := univ.filter fun x => x.1 < h

lemma qs_ext_can {mu : Fin n → ℤ} (hmu : Dominant mu) (c : ℤ) : qs_ext mu (canT mu) c = qs_ini (colH mu c) := by
  unfold qs_ext
  split_ifs with h1 h2
  · ext b; rw [qb_mem_canT]; simp [qs_ini]
  · rw [qs_colH_low hmu h2]; ext b; simp [qs_ini]
  · rw [qs_colH_high hmu (by simp only [TCols, mem_Ioc] at h1; omega)]; simp [qs_ini]

omit [NeZero n] in
lemma qs_minorC_eq {h : ℕ} (J I : Finset (Fin n)) (hJ : J.card = h) (hI : I.card = h) :
    minorC J I hJ hI = qs_mn (qs_gC n) J I := by
  rw [qs_mn_eq _ J I hJ hI, minorC, RingHom.map_det]
  rfl

omit [NeZero n] in
lemma qs_mn_univ : qs_mn (qs_gC n) univ univ = ((detU n : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) := by
  have hc : (univ : Finset (Fin n)).card = n := by simp
  rw [qs_mn_eq _ _ _ hc hc]
  have h1 : ∀ a, (univ : Finset (Fin n)).orderEmbOfFin hc a = a := fun a =>
    (congrFun (Finset.orderEmbOfFin_unique hc (f := id) (fun _ => mem_univ _) strictMono_id) a).symm
  simp only [h1]
  show _ = algebraMap _ _ (genMat ℤ n).det
  rw [RingHom.map_det]; rfl

omit [NeZero n] in
lemma qs_mn_empty {R : Type*} [CommRing R] (g : Matrix (Fin n) (Fin n) R) : qs_mn g ∅ ∅ = 1 := by
  rw [qs_mn_eq g ∅ ∅ (h := 0) rfl rfl]; simp

def qs_TM (lo : ℤ) (S : Finset ℤ) (J I : ℤ → Finset (Fin n)) : GLCoord ℤ n :=
  ((detU n ^ lo : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) * ∏ c ∈ S, qs_mn (qs_gC n) (J c) (I c)

theorem qs_TMat_eq {mu : Fin n → ℤ} (hmu : Dominant mu) (lo hi : ℤ) (h1 : lo ≤ mu (lastIdx n)) (h2 : mu 0 ≤ hi)
    (J I : TIdx mu) : TMat mu J I = qs_TM lo (Finset.Ioc lo hi) (qs_ext mu J) (qs_ext mu I) := by
  have h0 : mu (lastIdx n) ≤ mu 0 := hmu (Fin.zero_le _)
  have hS : Finset.Ioc lo hi = Finset.Ioc lo (mu (lastIdx n)) ∪ (TCols mu ∪ Finset.Ioc (mu 0) hi) := by
    rw [TCols, Finset.Ioc_union_Ioc_eq_Ioc h0 h2, Finset.Ioc_union_Ioc_eq_Ioc h1 (h0.trans h2)]
  have hA : ∏ c ∈ Finset.Ioc lo (mu (lastIdx n)), qs_mn (qs_gC n) (qs_ext mu J c) (qs_ext mu I c) =
      ((detU n : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) ^ (mu (lastIdx n) - lo).toNat := by
    rw [← Int.card_Ioc, ← Finset.prod_const]
    refine Finset.prod_congr rfl fun c hc => ?_
    have hc2 : c ≤ mu (lastIdx n) := (Finset.mem_Ioc.1 hc).2
    have hc1 : c ∉ TCols mu := by simp only [TCols, mem_Ioc]; omega
    simp only [qs_ext, dif_neg hc1, if_pos hc2, qs_mn_univ]
  have hB : ∏ c ∈ TCols mu, qs_mn (qs_gC n) (qs_ext mu J c) (qs_ext mu I c) =
      ∏ c : ↥(TCols mu), minorC (J c).1 (I c).1 (J c).2 (I c).2 := by
    rw [← Finset.prod_coe_sort]
    refine Finset.prod_congr rfl fun c _ => ?_
    rw [qs_ext_mem, qs_ext_mem, qs_minorC_eq]
  have hC : ∏ c ∈ Finset.Ioc (mu 0) hi, qs_mn (qs_gC n) (qs_ext mu J c) (qs_ext mu I c) = 1 := by
    refine Finset.prod_eq_one fun c hc => ?_
    have hc2 : mu 0 < c := (Finset.mem_Ioc.1 hc).1
    have hc1 : c ∉ TCols mu := by simp only [TCols, mem_Ioc]; omega
    have hc3 : ¬ c ≤ mu (lastIdx n) := by omega
    simp only [qs_ext, dif_neg hc1, if_neg hc3, qs_mn_empty]
  have hU : detU n ^ mu (lastIdx n) = detU n ^ lo * detU n ^ (mu (lastIdx n) - lo).toNat := by
    rw [← zpow_natCast, ← zpow_add, Int.toNat_of_nonneg (by omega)]; congr 1; omega
  rw [qs_TM, hS, Finset.prod_union, Finset.prod_union, hA, hB, hC, TMat, hU, Units.val_mul, Units.val_pow_eq_pow_val]
  · ring
  · refine Finset.disjoint_left.2 fun x hx hx' => ?_
    simp only [TCols, mem_Ioc] at hx hx'; omega
  · refine Finset.disjoint_left.2 fun x hx hx' => ?_
    simp only [TCols, mem_Ioc, mem_union] at hx hx'; omega

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end
