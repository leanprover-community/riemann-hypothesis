import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ParahoricIndexCount.Development

section
noncomputable section

open Matrix

namespace PI.ParahoricIdxZ.W

section A

variable {F : Type} [Field F] (O : Subring F) (ϖ : F)

theorem reindex_apply' {a t : ℕ} {R : Type} (A : Matrix (Fin (a + t)) (Fin (a + t)) R)
    (x y : Fin a ⊕ Fin t) :
    Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm A x y =
      A (finSumFinEquiv x) (finSumFinEquiv y) := by
  rfl

def theta {a t : ℕ} {R : Type} (A : Matrix (Fin a) (Fin a) R) (B : Matrix (Fin a) (Fin t) R)
    (C : Matrix (Fin t) (Fin a) R) (D : Matrix (Fin t) (Fin t) R) :
    Matrix (Fin (a + t)) (Fin (a + t)) R :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A B C D)

theorem reindex_theta {a t : ℕ} {R : Type} (A : Matrix (Fin a) (Fin a) R)
    (B : Matrix (Fin a) (Fin t) R) (C : Matrix (Fin t) (Fin a) R) (D : Matrix (Fin t) (Fin t) R) :
    Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm (theta A B C D) =
      Matrix.fromBlocks A B C D := by
  ext x y
  simp [theta, Matrix.reindex_apply]

theorem theta_apply {a t : ℕ} {R : Type} (A : Matrix (Fin a) (Fin a) R)
    (B : Matrix (Fin a) (Fin t) R) (C : Matrix (Fin t) (Fin a) R) (D : Matrix (Fin t) (Fin t) R)
    (x y : Fin a ⊕ Fin t) :
    theta A B C D (finSumFinEquiv x) (finSumFinEquiv y) = Matrix.fromBlocks A B C D x y := by
  simp [theta, Matrix.reindex_apply]

theorem theta_injective {a t : ℕ} {R : Type} {A A' : Matrix (Fin a) (Fin a) R}
    {B B' : Matrix (Fin a) (Fin t) R} {C C' : Matrix (Fin t) (Fin a) R}
    {D D' : Matrix (Fin t) (Fin t) R} (h : theta A B C D = theta A' B' C' D') :
    A = A' ∧ B = B' ∧ C = C' ∧ D = D' := by
  have h2 := congrArg (Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm) h
  rw [reindex_theta, reindex_theta] at h2
  exact Matrix.fromBlocks_inj.mp h2

theorem theta_mul {a t : ℕ} {R : Type} [CommRing R] (A A' : Matrix (Fin a) (Fin a) R)
    (B B' : Matrix (Fin a) (Fin t) R) (C C' : Matrix (Fin t) (Fin a) R)
    (D D' : Matrix (Fin t) (Fin t) R) :
    theta A B C D * theta A' B' C' D' =
      theta (A * A' + B * C') (A * B' + B * D') (C * A' + D * C') (C * B' + D * D') := by
  simp only [theta, Matrix.reindex_apply]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem theta_one {a t : ℕ} {R : Type} [CommRing R] :
    theta (1 : Matrix (Fin a) (Fin a) R) 0 0 (1 : Matrix (Fin t) (Fin t) R) = 1 := by
  simp [theta, Matrix.reindex_apply]

theorem intProd {l m n : Type} [Fintype m] {X : Matrix l m F} {Y : Matrix m n F}
    (hX : ∀ i j, X i j ∈ O) (hY : ∀ i j, Y i j ∈ O) : ∀ i j, (X * Y) i j ∈ O := by
  intro i j
  rw [Matrix.mul_apply]
  exact O.sum_mem fun k _ => O.mul_mem (hX i k) (hY k j)

theorem theta_int {a t : ℕ} {A : Matrix (Fin a) (Fin a) F} {B : Matrix (Fin a) (Fin t) F}
    {C : Matrix (Fin t) (Fin a) F} {D : Matrix (Fin t) (Fin t) F}
    (hA : ∀ i j, A i j ∈ O) (hB : ∀ i j, B i j ∈ O) (hC : ∀ i j, C i j ∈ O)
    (hD : ∀ i j, D i j ∈ O) : Formalism.DoubleCosetMeasures.IsInt O (theta A B C D) := by
  unfold Formalism.DoubleCosetMeasures.IsInt
  intro i j
  obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨y, rfl⟩ := finSumFinEquiv.surjective j
  rw [theta_apply]
  rcases x with x | x <;> rcases y with y | y <;> simp [hA, hB, hC, hD]

variable {ϖ}

private theorem exists_GLint_eq_one_add_smul (hϖ : ϖ ∈ O) (hloc : Formalism.DoubleCosetMeasures.IsLocalAt O ϖ) {n : ℕ}
    (X : Matrix (Fin n) (Fin n) F) (hX : ∀ i j, X i j ∈ O) :
    ∃ k ∈ Formalism.DoubleCosetMeasures.GLint O n, (k : Matrix (Fin n) (Fin n) F) = 1 + ϖ • X := by
  let w : O := ⟨ϖ, hϖ⟩
  let Y : Matrix (Fin n) (Fin n) O := fun i j => ⟨X i j, hX i j⟩
  obtain ⟨c, hc⟩ : ∃ c : O, (1 + w • Y).det = 1 + c * w := by
    have h0 : Ideal.Quotient.mk (Ideal.span {w}) w = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self w)
    have h1 : (Ideal.Quotient.mk (Ideal.span {w})).mapMatrix (1 + w • Y) = 1 := by
      ext i j
      by_cases h : i = j
      · subst h; simp [h0]
      · simp [h0, Matrix.one_apply_ne h]
    have h2 : (1 + w • Y).det - 1 ∈ Ideal.span {w} := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, RingHom.map_det, h1, Matrix.det_one, map_one,
        sub_self]
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp h2
    exact ⟨c, by rw [hc]; ring⟩
  have key : ∀ o ∈ O, ((1 + c * w : O) : F) ≠ ϖ * o := by
    intro o ho h
    apply hloc.1
    have h' : ϖ * (o - c) = 1 := by
      have h3 : (1 : F) + (c : F) * ϖ = ϖ * o := by simpa [w] using h
      linear_combination -h3
    rw [inv_eq_of_mul_eq_one_right h']
    exact O.sub_mem ho c.2
  have hz : ((1 + c * w : O) : F) ≠ 0 := fun h0 => key 0 O.zero_mem (by rw [h0, mul_zero])
  have hu : IsUnit (1 + w • Y).det := by
    rw [hc]
    refine isUnit_iff_exists_inv.mpr ⟨⟨((1 + c * w : O) : F)⁻¹, hloc.2 _ (1 + c * w).2 key⟩, ?_⟩
    apply Subtype.ext
    show ((1 + c * w : O) : F) * ((1 + c * w : O) : F)⁻¹ = 1
    exact mul_inv_cancel₀ hz
  refine ⟨Units.map (RingHom.mapMatrix O.subtype).toMonoidHom (Matrix.nonsingInvUnit _ hu), ?_, ?_⟩
  · exact ⟨fun i j => SetLike.coe_mem _, fun i j => SetLike.coe_mem _⟩
  · ext i j
    by_cases h : i = j
    · subst h; simp [Matrix.nonsingInvUnit, Y, w]; rfl
    · simp [Matrix.nonsingInvUnit, Y, w, Matrix.one_apply_ne h]; rfl

theorem cong_blockCond (hϖ : ϖ ∈ O) (hϖ0 : ϖ ≠ 0) (hloc : Formalism.DoubleCosetMeasures.IsLocalAt O ϖ) {a t : ℕ}
    {J' : Subgroup (GL (Fin a) F)} (hKJ : Formalism.DoubleCosetMeasures.congSub O ϖ a ≤ J')
    {g : GL (Fin (a + t)) F} (hg : g ∈ Formalism.DoubleCosetMeasures.congSub O ϖ (a + t)) : blockCond O ϖ J' g := by
  obtain ⟨-, hgX⟩ := hg
  have hXO : ∀ u v, ϖ⁻¹ * ((g : Matrix (Fin (a + t)) (Fin (a + t)) F) u v -
      (1 : Matrix (Fin (a + t)) (Fin (a + t)) F) u v) ∈ O := by
    intro u v
    have h := hgX u v
    rwa [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul] at h
  have hone : ∀ x y : Fin a ⊕ Fin t, (1 : Matrix (Fin (a + t)) (Fin (a + t)) F)
      (finSumFinEquiv x) (finSumFinEquiv y) = (1 : Matrix (Fin a ⊕ Fin t) (Fin a ⊕ Fin t) F) x y := by
    intro x y
    by_cases h : x = y
    · subst h; simp
    · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne (fun h' => h (finSumFinEquiv.injective h'))]
  have hG : ∀ x y : Fin a ⊕ Fin t,
      (g : Matrix (Fin (a + t)) (Fin (a + t)) F) (finSumFinEquiv x) (finSumFinEquiv y) =
      (1 : Matrix (Fin a ⊕ Fin t) (Fin a ⊕ Fin t) F) x y +
        ϖ * (ϖ⁻¹ * ((g : Matrix (Fin (a + t)) (Fin (a + t)) F) (finSumFinEquiv x) (finSumFinEquiv y) -
          (1 : Matrix (Fin (a + t)) (Fin (a + t)) F) (finSumFinEquiv x) (finSumFinEquiv y))) := by
    intro x y
    rw [mul_inv_cancel_left₀ hϖ0, hone]
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨k, hk, hkeq⟩ := exists_GLint_eq_one_add_smul O hϖ hloc
      (fun i j : Fin a => ϖ⁻¹ * ((g : Matrix (Fin (a + t)) (Fin (a + t)) F) (finSumFinEquiv (Sum.inl i))
        (finSumFinEquiv (Sum.inl j)) - (1 : Matrix (Fin (a + t)) (Fin (a + t)) F)
          (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j)))) (fun i j => hXO _ _)
    refine ⟨k, hKJ ⟨hk, ?_⟩, ?_⟩
    · intro i j
      rw [Matrix.smul_apply, Matrix.sub_apply, hkeq]
      show ϖ⁻¹ * ((1 : Matrix (Fin a) (Fin a) F) i j + ϖ * (ϖ⁻¹ * (_ - _)) -
        (1 : Matrix (Fin a) (Fin a) F) i j) ∈ O
      rw [add_sub_cancel_left, inv_mul_cancel_left₀ hϖ0]
      exact hXO _ _
    · rw [hkeq]
      ext i j
      show (1 : Matrix (Fin a) (Fin a) F) i j + ϖ * (ϖ⁻¹ * (_ - _)) =
        (g : Matrix (Fin (a + t)) (Fin (a + t)) F) (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j))
      rw [mul_inv_cancel_left₀ hϖ0, hone]
      simp [Matrix.one_apply]
  · intro i j
    show (g : Matrix (Fin (a + t)) (Fin (a + t)) F) (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inr j)) ∈ O
    rw [hG]
    exact O.add_mem (by simp [Matrix.one_apply, O.zero_mem]) (O.mul_mem hϖ (hXO _ _))
  · simp only [Formalism.DoubleCosetMeasures.IIset, Set.mem_setOf_eq]
    intro i j
    refine ⟨_, hXO (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl j)), ?_⟩
    show (g : Matrix (Fin (a + t)) (Fin (a + t)) F) (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl j)) = _
    conv_lhs => rw [hG]
    simp [Matrix.one_apply]
  · obtain ⟨k, hk, hkeq⟩ := exists_GLint_eq_one_add_smul O hϖ hloc
      (fun i j : Fin t => ϖ⁻¹ * ((g : Matrix (Fin (a + t)) (Fin (a + t)) F) (finSumFinEquiv (Sum.inr i))
        (finSumFinEquiv (Sum.inr j)) - (1 : Matrix (Fin (a + t)) (Fin (a + t)) F)
          (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inr j)))) (fun i j => hXO _ _)
    refine ⟨k, hk, ?_⟩
    rw [hkeq]
    ext i j
    show (1 : Matrix (Fin t) (Fin t) F) i j + ϖ * (ϖ⁻¹ * (_ - _)) =
      (g : Matrix (Fin (a + t)) (Fin (a + t)) F) (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inr j))
    rw [mul_inv_cancel_left₀ hϖ0, hone]
    simp [Matrix.one_apply]

end A

end PI.ParahoricIdxZ.W
end
end

section
noncomputable section

open Matrix Formalism.DoubleCosetMeasures.P.GLRed

namespace PI.ParahoricIdxZ.W

section B

variable {F : Type} [Field F] (O : Subring F) (ϖ : F) (hϖ : ϖ ∈ O)

def redJ {a : ℕ} (J' : Subgroup (GL (Fin a) F)) (hJ : J' ≤ Formalism.DoubleCosetMeasures.GLint O a) :
    J' →* GL (Fin a) (Formalism.DoubleCosetMeasures.kF O ϖ hϖ) :=
  (red O a ϖ hϖ).comp (Subgroup.inclusion hJ)

theorem card_range_redJ (hϖ0 : ϖ ≠ 0) {a : ℕ} (J' : Subgroup (GL (Fin a) F))
    (hJ : J' ≤ Formalism.DoubleCosetMeasures.GLint O a) :
    Nat.card (redJ O ϖ hϖ J' hJ).range = Nat.card (J' ⧸ (Formalism.DoubleCosetMeasures.congSub O ϖ a).subgroupOf J') := by
  have hk : (redJ O ϖ hϖ J' hJ).ker = (Formalism.DoubleCosetMeasures.congSub O ϖ a).subgroupOf J' := by
    ext k
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    change red O a ϖ hϖ (Subgroup.inclusion hJ k) = 1 ↔ _
    rw [← MonoidHom.mem_ker, ker_red O ϖ hϖ hϖ0, Subgroup.mem_subgroupOf]
    rfl
  rw [← hk]
  exact (Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv).symm

theorem mk_congr {u v : F} (hu : u ∈ O) (hv : v ∈ O) (h : u = v) :
    Ideal.Quotient.mk (Ideal.span {(⟨ϖ, hϖ⟩ : O)}) (⟨u, hu⟩ : O) =
      Ideal.Quotient.mk (Ideal.span {(⟨ϖ, hϖ⟩ : O)}) (⟨v, hv⟩ : O) := by
  subst h; rfl

theorem mk_eq_zero {u : F} (hu : u ∈ O) (o : F) (ho : o ∈ O) (h : u = ϖ * o) :
    Ideal.Quotient.mk (Ideal.span {(⟨ϖ, hϖ⟩ : O)}) (⟨u, hu⟩ : O) = 0 := by
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
  exact ⟨⟨o, ho⟩, Subtype.ext (by simp [h, mul_comm])⟩

theorem red_eq_theta {a t : ℕ} (h : Formalism.DoubleCosetMeasures.GLint O (a + t))
    (A : Matrix (Fin a) (Fin a) (Formalism.DoubleCosetMeasures.kF O ϖ hϖ)) (B : Matrix (Fin a) (Fin t) (Formalism.DoubleCosetMeasures.kF O ϖ hϖ))
    (C : Matrix (Fin t) (Fin a) (Formalism.DoubleCosetMeasures.kF O ϖ hϖ)) (D : Matrix (Fin t) (Fin t) (Formalism.DoubleCosetMeasures.kF O ϖ hϖ))
    (H : ∀ x y, Ideal.Quotient.mk _ (⟨((h : GL (Fin (a + t)) F) : Matrix _ _ F)
      (finSumFinEquiv x) (finSumFinEquiv y), h.2.1 _ _⟩ : O) = Matrix.fromBlocks A B C D x y) :
    ((red O (a + t) ϖ hϖ h : GL (Fin (a + t)) _) : Matrix _ _ _) = theta A B C D := by
  ext i j
  obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨y, rfl⟩ := finSumFinEquiv.surjective j
  rw [red_val, theta_apply]
  exact H x y

theorem mk_entry {a t : ℕ} (g : Formalism.DoubleCosetMeasures.GLint O (a + t)) {A : Matrix (Fin a) (Fin a) F}
    {B : Matrix (Fin a) (Fin t) F} {C : Matrix (Fin t) (Fin a) F} {D : Matrix (Fin t) (Fin t) F}
    (hg : ((g : GL (Fin (a + t)) F) : Matrix _ _ F) = theta A B C D) (x y : Fin a ⊕ Fin t)
    (hv : Matrix.fromBlocks A B C D x y ∈ O) :
    Ideal.Quotient.mk (Ideal.span {(⟨ϖ, hϖ⟩ : O)}) (⟨((g : GL (Fin (a + t)) F) : Matrix _ _ F)
      (finSumFinEquiv x) (finSumFinEquiv y), g.2.1 _ _⟩ : O) =
      Ideal.Quotient.mk (Ideal.span {(⟨ϖ, hϖ⟩ : O)}) (⟨Matrix.fromBlocks A B C D x y, hv⟩ : O) :=
  mk_congr O ϖ hϖ _ _ (by rw [hg, theta_apply])

end B

end PI.ParahoricIdxZ.W
end
end

section
noncomputable section

open Matrix Formalism.DoubleCosetMeasures.P.GLRed

namespace PI.ParahoricIdxZ.W

section C

variable {F : Type} [Field F] (O : Subring F) {ϖ : F} (hϖ : ϖ ∈ O)

def param {a t : ℕ} (J' : Subgroup (GL (Fin a) F)) (hJ : J' ≤ Formalism.DoubleCosetMeasures.GLint O a)
    (p : (redJ O ϖ hϖ J' hJ).range × Matrix (Fin a) (Fin t) (Formalism.DoubleCosetMeasures.kF O ϖ hϖ) ×
      GL (Fin t) (Formalism.DoubleCosetMeasures.kF O ϖ hϖ)) :
    Matrix (Fin (a + t)) (Fin (a + t)) (Formalism.DoubleCosetMeasures.kF O ϖ hϖ) :=
  theta ((p.1 : GL (Fin a) (Formalism.DoubleCosetMeasures.kF O ϖ hϖ)) : Matrix _ _ _) p.2.1 0
    ((p.2.2 : GL (Fin t) (Formalism.DoubleCosetMeasures.kF O ϖ hϖ)) : Matrix _ _ _)

theorem param_injective {a t : ℕ} (J' : Subgroup (GL (Fin a) F)) (hJ : J' ≤ Formalism.DoubleCosetMeasures.GLint O a) :
    Function.Injective (param (t := t) O hϖ J' hJ) := by
  rintro ⟨x, B, D⟩ ⟨x', B', D'⟩ h
  obtain ⟨h1, h2, -, h4⟩ := theta_injective h
  have hx : x = x' := Subtype.ext (Units.ext h1)
  have hD : D = D' := Units.ext h4
  subst hx hD h2
  rfl

theorem image_eq (hϖ0 : ϖ ≠ 0) (hloc : Formalism.DoubleCosetMeasures.IsLocalAt O ϖ) {a t : ℕ}
    (J' : Subgroup (GL (Fin a) F)) (hJint : J' ≤ Formalism.DoubleCosetMeasures.GLint O a)
    (J : Subgroup (GL (Fin (a + t)) F)) (hJ : ∀ A, A ∈ J ↔ blockCond O ϖ J' A) :
    (fun g : GL (Fin (a + t)) (Formalism.DoubleCosetMeasures.kF O ϖ hϖ) =>
      (g : Matrix (Fin (a + t)) (Fin (a + t)) (Formalism.DoubleCosetMeasures.kF O ϖ hϖ))) ''
      (((J.subgroupOf (Formalism.DoubleCosetMeasures.GLint O (a + t))).map (red O (a + t) ϖ hϖ) : Subgroup _) : Set _) =
      Set.range (param O hϖ J' hJint) := by
  ext M
  constructor
  · rintro ⟨g, hg, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_map] at hg
    obtain ⟨h, hH, rfl⟩ := hg
    rw [Subgroup.mem_subgroupOf, hJ] at hH
    simp only [blockCond] at hH
    obtain ⟨⟨k, hk, hkv⟩, hB, hC, ⟨D, hD, hDv⟩⟩ := hH
    refine ⟨⟨⟨redJ O ϖ hϖ J' hJint ⟨k, hk⟩, MonoidHom.mem_range.mpr ⟨_, rfl⟩⟩,
      fun i j => Ideal.Quotient.mk _ ⟨_, hB i j⟩, red O t ϖ hϖ ⟨D, hD⟩⟩, ?_⟩
    symm
    apply red_eq_theta
    rintro (x | x) (y | y)
    · exact (mk_congr O ϖ hϖ _ ((hJint hk).1 x y)
        (by rw [hkv]; simp [Matrix.toBlocks₁₁, reindex_apply'])).trans rfl
    · exact (mk_congr O ϖ hϖ _ (hB x y) (by simp [Matrix.toBlocks₁₂, reindex_apply'])).trans rfl
    · obtain ⟨o, ho, he⟩ := hC x y
      exact (mk_eq_zero O ϖ hϖ _ o ho
        (by rw [← he]; simp [Matrix.toBlocks₂₁, reindex_apply'])).trans rfl
    · exact (mk_congr O ϖ hϖ _ (hD.1 x y)
        (by rw [hDv]; simp [Matrix.toBlocks₂₂, reindex_apply'])).trans rfl
  · rintro ⟨⟨⟨xb, hxb⟩, Bb, Db⟩, rfl⟩
    obtain ⟨k, rfl⟩ := MonoidHom.mem_range.mp hxb
    obtain ⟨D, rfl⟩ := red_surj O t ϖ hϖ hloc Db
    choose Bl hBl using fun i j =>
      Ideal.Quotient.mk_surjective (I := Ideal.span {(⟨ϖ, hϖ⟩ : O)}) (Bb i j)
    have hk := hJint k.2
    set BF : Matrix (Fin a) (Fin t) F := fun i j => (Bl i j : F) with hBF
    have hBFi : ∀ i j, BF i j ∈ O := fun i j => (Bl i j).2
    set kM : Matrix (Fin a) (Fin a) F := ((k : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) with hkM
    set kI : Matrix (Fin a) (Fin a) F := (((k : GL (Fin a) F)⁻¹ : GL (Fin a) F) : Matrix (Fin a) (Fin a) F)
      with hkI
    set DM : Matrix (Fin t) (Fin t) F := (((D : GL (Fin t) F)) : Matrix (Fin t) (Fin t) F) with hDM
    set DI : Matrix (Fin t) (Fin t) F := (((D : GL (Fin t) F)⁻¹ : GL (Fin t) F) : Matrix (Fin t) (Fin t) F)
      with hDI
    have hkk : kM * kI = 1 := Units.mul_inv _
    have hkk' : kI * kM = 1 := Units.inv_mul _
    have hDD : DM * DI = 1 := Units.mul_inv _
    have hDD' : DI * DM = 1 := Units.inv_mul _
    have h1 : theta kM BF 0 DM * theta kI (-(kI * BF * DI)) 0 DI = 1 := by
      rw [theta_mul]
      simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_neg,
        ← Matrix.mul_assoc, hkk, hDD, Matrix.one_mul, neg_add_cancel, neg_zero, zero_add, theta_one]
    have h2 : theta kI (-(kI * BF * DI)) 0 DI * theta kM BF 0 DM = 1 := by
      rw [theta_mul]
      simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.neg_mul,
        Matrix.mul_assoc, hkk', hDD', Matrix.mul_one, add_neg_cancel, neg_zero, zero_add, theta_one]
    obtain ⟨hF, hFv, hFi⟩ : ∃ g : GL (Fin (a + t)) F, (g : Matrix (Fin (a + t)) (Fin (a + t)) F) = theta kM BF 0 DM ∧
        ((g⁻¹ : GL (Fin (a + t)) F) : Matrix (Fin (a + t)) (Fin (a + t)) F) = theta kI (-(kI * BF * DI)) 0 DI :=
      ⟨⟨_, _, h1, h2⟩, rfl, rfl⟩
    have hmem : hF ∈ Formalism.DoubleCosetMeasures.GLint O (a + t) := by
      refine ⟨?_, ?_⟩
      · rw [hFv]
        exact theta_int O hk.1 hBFi (fun _ _ => O.zero_mem) D.2.1
      · rw [hFi]
        refine theta_int O hk.2 (fun i j => ?_) (fun _ _ => O.zero_mem) D.2.2
        rw [Matrix.neg_apply]
        exact O.neg_mem (intProd O (intProd O hk.2 hBFi) D.2.2 i j)
    have hbc : blockCond O ϖ J' hF := by
      simp only [blockCond]
      rw [hFv, reindex_theta]
      refine ⟨⟨k, k.2, ?_⟩, fun i j => ?_, fun i j => ⟨0, O.zero_mem, ?_⟩, ⟨D, D.2, ?_⟩⟩
      · simp [hkM]
      · simpa using hBFi i j
      · simp
      · simp [hDM]
    refine ⟨red O (a + t) ϖ hϖ ⟨hF, hmem⟩, ?_, ?_⟩
    · rw [SetLike.mem_coe, Subgroup.mem_map]
      exact ⟨⟨hF, hmem⟩, by rw [Subgroup.mem_subgroupOf, hJ]; exact hbc, rfl⟩
    · apply red_eq_theta
      rintro (x | x) (y | y)
      · refine (mk_entry O ϖ hϖ ⟨hF, hmem⟩ hFv _ _ ?_).trans ?_
        · exact hk.1 x y
        · rfl
      · refine (mk_entry O ϖ hϖ ⟨hF, hmem⟩ hFv _ _ ?_).trans ?_
        · exact hBFi x y
        · exact hBl x y
      · refine (mk_entry O ϖ hϖ ⟨hF, hmem⟩ hFv _ _ ?_).trans ?_
        · exact O.zero_mem
        · exact map_zero _
      · refine (mk_entry O ϖ hϖ ⟨hF, hmem⟩ hFv _ _ ?_).trans ?_
        · exact D.2.1 x y
        · rfl

end C

end PI.ParahoricIdxZ.W
end
end

section
noncomputable section

open Matrix Formalism.DoubleCosetMeasures.P.GLRed

namespace PI.ParahoricIdxZ.W

theorem idxStep : IdxStep := by
  intro F _ O ϖ hϖ hϖ0 hloc hfin a t J' hKJ hJint J hJ
  have := hfin
  set H := J.subgroupOf (Formalism.DoubleCosetMeasures.GLint O (a + t)) with hH
  have hker : (red O (a + t) ϖ hϖ).ker ≤ H := by
    rw [ker_red O ϖ hϖ hϖ0]
    intro g hg
    rw [Subgroup.mem_subgroupOf] at hg ⊢
    exact (hJ _).2 (cong_blockCond O hϖ hϖ0 hloc hKJ hg)
  have hidx := Subgroup.index_map_eq H (red_surj O (a + t) ϖ hϖ hloc) hker
  have hcm := Subgroup.card_mul_index (H.map (red O (a + t) ϖ hϖ))
  have hcard : Nat.card (H.map (red O (a + t) ϖ hϖ)) =
      Nat.card (J' ⧸ (Formalism.DoubleCosetMeasures.congSub O ϖ a).subgroupOf J') *
        (Nat.card (Formalism.DoubleCosetMeasures.kF O ϖ hϖ) ^ (a * t) * Nat.card (GL (Fin t) (Formalism.DoubleCosetMeasures.kF O ϖ hϖ))) := by
    have e1 : Nat.card (H.map (red O (a + t) ϖ hϖ)) =
        Nat.card ((fun g : GL (Fin (a + t)) (Formalism.DoubleCosetMeasures.kF O ϖ hϖ) =>
          (g : Matrix (Fin (a + t)) (Fin (a + t)) (Formalism.DoubleCosetMeasures.kF O ϖ hϖ))) ''
            ((H.map (red O (a + t) ϖ hϖ) : Subgroup _) : Set _)) :=
      (Nat.card_image_of_injective Units.val_injective _).symm
    have e2 : Nat.card (Matrix (Fin a) (Fin t) (Formalism.DoubleCosetMeasures.kF O ϖ hϖ)) =
        Nat.card (Formalism.DoubleCosetMeasures.kF O ϖ hϖ) ^ (a * t) := by
      show Nat.card (Fin a → Fin t → Formalism.DoubleCosetMeasures.kF O ϖ hϖ) = _
      rw [Nat.card_fun, Nat.card_fun, Nat.card_fin, Nat.card_fin, ← pow_mul, mul_comm]
    rw [e1, image_eq O hϖ hϖ0 hloc J' hJint J hJ,
      Nat.card_range_of_injective (param_injective (t := t) O hϖ J' hJint),
      Nat.card_prod, Nat.card_prod, card_range_redJ O ϖ hϖ hϖ0 J' hJint, e2]
  rw [← hcm, ← hidx, hcard]
  ring

end PI.ParahoricIdxZ.W
end
end
