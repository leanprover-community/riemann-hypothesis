import Formalism.HermitianCurvature.MemParahoricTimesPrincipalCongruenceIff

namespace Formalism.FourierDecayAlt.P.S3x2

open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.S3

section Generic

variable {ι : Type} [Fintype ι] [DecidableEq ι] {A : Type} [CommRing A]

def IsUc (c : ι → ℕ) (x : Matrix ι ι A) : Prop :=
  ∀ i j, c j ≤ c i → x i j = (1 : Matrix ι ι A) i j

def IsLc (c : ι → ℕ) (x : Matrix ι ι A) : Prop := ∀ i j, c i ≠ c j → x i j = 0

variable {c : ι → ℕ} {x y : Matrix ι ι A}

theorem isUc_one : IsUc c (1 : Matrix ι ι A) := fun _ _ _ => rfl

theorem IsUc.mul (hx : IsUc c x) (hy : IsUc c y) : IsUc c (x * y) := by
  intro i j hij
  rw [Matrix.mul_apply]
  have key : ∀ l ∈ Finset.univ, x i l * y l j = (1 : Matrix ι ι A) i l * y l j := by
    intro l _
    by_cases hl : c l ≤ c i
    · rw [hx i l hl]
    · have h1 : c j ≤ c l := by omega
      have hne : l ≠ j := by rintro rfl; omega
      rw [hy l j h1, Matrix.one_apply_ne hne, mul_zero, mul_zero]
  rw [Finset.sum_congr rfl key, ← Matrix.mul_apply, Matrix.one_mul, hy i j hij]

theorem IsUc.blockTriangular (hx : IsUc c x) : BlockTriangular x c := by
  intro i j h
  have hne : i ≠ j := by rintro rfl; omega
  rw [hx i j h.le, Matrix.one_apply_ne hne]

theorem IsUc.det (hx : IsUc c x) : x.det = 1 := by
  rw [hx.blockTriangular.det]
  apply Finset.prod_eq_one
  intro a _
  have h1 : x.toSquareBlock c a = 1 := by
    ext ⟨i, hi⟩ ⟨j, hj⟩
    simp [Matrix.toSquareBlock_def, hx i j (by omega), Matrix.one_apply, Subtype.ext_iff]
  rw [h1, Matrix.det_one]

theorem IsUc.inv (hx : IsUc c x) : IsUc c x⁻¹ := by
  have hdet := hx.det
  let _ : Invertible x := Matrix.invertibleOfIsUnitDet x (by simp [hdet])
  have hT : BlockTriangular x⁻¹ c := Matrix.blockTriangular_inv_of_blockTriangular hx.blockTriangular
  intro i j hij
  have h1 : (x⁻¹ * x) i j = (1 : Matrix ι ι A) i j := by
    rw [Matrix.nonsing_inv_mul x (by simp [hdet])]
  rw [Matrix.mul_apply] at h1
  have key : ∀ l ∈ Finset.univ, x⁻¹ i l * x l j = x⁻¹ i l * (1 : Matrix ι ι A) l j := by
    intro l _
    by_cases hl : c j ≤ c l
    · rw [hx l j hl]
    · have h2 : c l < c i := by omega
      rw [hT h2, zero_mul, zero_mul]
  rw [Finset.sum_congr rfl key, ← Matrix.mul_apply, Matrix.mul_one] at h1
  exact h1

theorem IsUc.conj {l l' n : Matrix ι ι A} (hl : IsLc c l) (hl' : IsLc c l') (h : l * l' = 1)
    (hn : IsUc c n) : IsUc c (l * n * l') := by
  intro i j hij
  have key : (l * (n - 1) * l') i j = 0 := by
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro b _
    by_cases hb : c b = c j
    · rw [Matrix.mul_apply, Finset.sum_eq_zero, zero_mul]
      intro a _
      by_cases ha : c i = c a
      · rw [Matrix.sub_apply, hn a b (by omega), sub_self, mul_zero]
      · rw [hl i a ha, zero_mul]
    · rw [hl' b j hb, mul_zero]
  have h2 : l * n * l' = l * (n - 1) * l' + 1 := by
    rw [mul_sub, sub_mul, mul_one, h]; abel
  rw [h2, Matrix.add_apply, key, zero_add]

theorem IsUc.map {B : Type} [CommRing B] (f : A →+* B) (hx : IsUc c x) : IsUc c (x.map f) := by
  intro i j hij
  rw [Matrix.map_apply, hx i j hij]
  by_cases h : i = j
  · subst h; simp
  · simp [Matrix.one_apply_ne h]

variable (A) (c) in

def UcG : Subgroup (GL ι A) where
  carrier := {g | IsUc c (g : Matrix ι ι A)}
  one_mem' := by simpa using isUc_one
  mul_mem' := by intro a b ha hb; simpa using IsUc.mul ha hb
  inv_mem' := by intro a ha; simpa [Matrix.coe_units_inv] using IsUc.inv ha

noncomputable def toGL (x : Matrix ι ι A) (h : IsUnit x.det) : GL ι A := Matrix.nonsingInvUnit x h

@[simp] theorem coe_toGL (x : Matrix ι ι A) (h : IsUnit x.det) : (toGL x h : Matrix ι ι A) = x := rfl

theorem card_of_subgroupSet (P : Matrix ι ι A → Prop) (B : Subgroup (GL ι A))
    (h : ∀ x, P x ↔ ∃ g ∈ B, (g : Matrix ι ι A) = x) : Nat.card {x // P x} = Nat.card B := by
  symm
  apply Nat.card_congr
  refine Equiv.ofBijective (fun g : B => ⟨((g : GL ι A) : Matrix ι ι A), (h _).2 ⟨g, g.2, rfl⟩⟩) ⟨?_, ?_⟩
  · intro a b hab
    have h1 : ((a : GL ι A) : Matrix ι ι A) = ((b : GL ι A) : Matrix ι ι A) := congrArg Subtype.val hab
    exact Subtype.ext (Units.ext h1)
  · rintro ⟨x, hx⟩
    obtain ⟨g, hg, rfl⟩ := (h x).1 hx
    exact ⟨⟨g, hg⟩, rfl⟩

end Generic

section Prod

variable {G : Type} [Group G]

def prodG (N H : Subgroup G) (hnorm : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N) : Subgroup G where
  carrier := {g | ∃ n ∈ N, ∃ h ∈ H, g = n * h}
  one_mem' := ⟨1, N.one_mem, 1, H.one_mem, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨n, hn, h, hh, rfl⟩ ⟨n', hn', h', hh', rfl⟩
    exact ⟨n * (h * n' * h⁻¹), N.mul_mem hn (hnorm h hh n' hn'), h * h', H.mul_mem hh hh', by group⟩
  inv_mem' := by
    rintro _ ⟨n, hn, h, hh, rfl⟩
    exact ⟨h⁻¹ * n⁻¹ * (h⁻¹)⁻¹, hnorm _ (H.inv_mem hh) _ (N.inv_mem hn), h⁻¹, H.inv_mem hh, by group⟩


end Prod

section Specific

variable {A : Type} [CommRing A] {r k : ℕ}

def cI (r k : ℕ) : Idx r k → ℕ
  | Sum.inl a => a
  | Sum.inr (Sum.inl _) => r
  | Sum.inr (Sum.inr a) => r + 1 + a

theorem isN_iff (x : Matrix (Idx r k) (Idx r k) A) : IsN x ↔ IsUc (cI r k) x := by
  constructor
  · rintro ⟨h11, h33, h22, h21, h31, h32⟩
    rintro (a | a | a) (b | b | b) hij
    · simp only [cI] at hij
      rcases hij.lt_or_eq with h | h
      · have h1 : b11 x a b = 0 := h11.1 (by simpa using h)
        have hne : a ≠ b := by rintro rfl; omega
        simpa [b11, Matrix.one_apply, hne] using h1
      · have hab : a = b := Fin.ext h.symm
        subst hab
        simpa [b11] using h11.2 a
    · simp only [cI] at hij; have := a.2; omega
    · simp only [cI] at hij; have := a.2; omega
    · simpa [b21] using congrFun (congrFun h21 a) b
    · simpa [b22, Matrix.one_apply] using congrFun (congrFun h22 a) b
    · simp only [cI] at hij; omega
    · simpa [b31] using congrFun (congrFun h31 a) b
    · simpa [b32] using congrFun (congrFun h32 a) b
    · simp only [cI] at hij
      have hij' : (b : ℕ) ≤ a := by omega
      rcases hij'.lt_or_eq with h | h
      · have h1 : b33 x a b = 0 := h33.1 (by simpa using h)
        have hne : a ≠ b := by rintro rfl; omega
        simpa [b33, Matrix.one_apply, hne] using h1
      · have hab : a = b := Fin.ext h.symm
        subst hab
        simpa [b33] using h33.2 a
  · intro h
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
    · intro a b hab
      have hab' : b < a := hab
      have hne : a ≠ b := hab'.ne'
      have := h (Sum.inl a) (Sum.inl b) (by simp only [cI]; exact hab'.le)
      simpa [b11, Matrix.one_apply, hne] using this
    · intro a
      simpa [b11] using h (Sum.inl a) (Sum.inl a) le_rfl
    · intro a b hab
      have hab' : b < a := hab
      have hne : a ≠ b := hab'.ne'
      have := h (Sum.inr (Sum.inr a)) (Sum.inr (Sum.inr b)) (by simp only [cI]; have : (b : ℕ) < a := hab'; omega)
      simpa [b33, Matrix.one_apply, hne] using this
    · intro a
      simpa [b33] using h (Sum.inr (Sum.inr a)) (Sum.inr (Sum.inr a)) le_rfl
    · ext a b
      simpa [b22, Matrix.one_apply] using h (Sum.inr (Sum.inl a)) (Sum.inr (Sum.inl b)) le_rfl
    · ext a b
      simpa [b21] using h (Sum.inr (Sum.inl a)) (Sum.inl b) (by simp only [cI]; exact b.2.le)
    · ext a b
      simpa [b31] using h (Sum.inr (Sum.inr a)) (Sum.inl b) (by simp only [cI]; have := b.2; omega)
    · ext a b
      simpa [b32] using h (Sum.inr (Sum.inr a)) (Sum.inr (Sum.inl b)) (by simp only [cI]; omega)

theorem hEmb_mul (h h' : Matrix (Fin k) (Fin k) A) : hEmb r (h * h') = hEmb r h * hEmb r h' := by
  simp [hEmb, midEmb, Matrix.fromBlocks_multiply]

theorem hEmb_one : hEmb r (1 : Matrix (Fin k) (Fin k) A) = 1 := by
  simp [hEmb, midEmb]

theorem hEmb_apply (h : Matrix (Fin k) (Fin k) A) (a b : Fin k) :
    hEmb r h (Sum.inr (Sum.inl (Sum.inl a))) (Sum.inr (Sum.inl (Sum.inl b))) = h a b := rfl

theorem hEmb_map {B : Type} [CommRing B] (f : A →+* B) (h : Matrix (Fin k) (Fin k) A) :
    (hEmb r h).map f = hEmb r (h.map f) := by
  simp [hEmb, midEmb, Matrix.fromBlocks_map]

theorem isLc_hEmb (h : Matrix (Fin k) (Fin k) A) : IsLc (cI r k) (hEmb r h) := by
  rintro (a | a | a) (b | b | b) hij
  · have hne : a ≠ b := by rintro rfl; exact hij rfl
    simp [hEmb, hne]
  · simp [hEmb]
  · simp [hEmb]
  · simp [hEmb]
  · exact absurd rfl hij
  · simp [hEmb]
  · simp [hEmb]
  · simp [hEmb]
  · have hne : a ≠ b := by rintro rfl; exact hij rfl
    simp [hEmb, hne]

variable (A r k) in

def hEmbHom : Matrix (Fin k) (Fin k) A →* Matrix (Idx r k) (Idx r k) A where
  toFun := hEmb r
  map_one' := hEmb_one
  map_mul' := hEmb_mul

variable (A r k) in

def phi : GL (Fin k) A →* GL (Idx r k) A := Units.map (hEmbHom A r k)

@[simp] theorem coe_phi (h : GL (Fin k) A) :
    (phi A r k h : Matrix (Idx r k) (Idx r k) A) = hEmb r (h : Matrix (Fin k) (Fin k) A) := rfl

theorem phi_injective : Function.Injective (phi A r k) := by
  intro a b hab
  apply Units.ext
  ext i j
  have h1 : hEmb r (a : Matrix (Fin k) (Fin k) A) = hEmb r (b : Matrix (Fin k) (Fin k) A) := by
    rw [← coe_phi, ← coe_phi, hab]
  rw [← hEmb_apply (r := r) (a : Matrix (Fin k) (Fin k) A), h1, hEmb_apply]

theorem norm_phi (V : Subgroup (GL (Fin k) A)) :
    ∀ h ∈ V.map (phi A r k), ∀ n ∈ UcG A (cI r k), h * n * h⁻¹ ∈ UcG A (cI r k) := by
  rintro _ ⟨h, -, rfl⟩ n hn
  rw [← map_inv]
  change IsUc (cI r k) (hEmb r (h : Matrix (Fin k) (Fin k) A) * (n : Matrix _ _ A) *
    hEmb r ((h⁻¹ : GL (Fin k) A) : Matrix (Fin k) (Fin k) A))
  refine IsUc.conj (isLc_hEmb _) (isLc_hEmb _) ?_ hn
  rw [← hEmb_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, hEmb_one]


variable (r) in

def PG (V : Subgroup (GL (Fin k) A)) : Subgroup (GL (Idx r k) A) :=
  prodG (UcG A (cI r k)) (V.map (phi A r k)) (norm_phi V)


theorem mem_PG (V : Subgroup (GL (Fin k) A)) (g : GL (Idx r k) A) :
    g ∈ PG r V ↔ ∃ n : GL (Idx r k) A, ∃ h ∈ V, IsN (n : Matrix (Idx r k) (Idx r k) A) ∧
      g = n * phi A r k h := by
  constructor
  · rintro ⟨n, hn, _, ⟨h, hh, rfl⟩, rfl⟩
    exact ⟨n, h, hh, (isN_iff _).2 hn, rfl⟩
  · rintro ⟨n, h, hh, hn, rfl⟩
    exact ⟨n, (isN_iff _).1 hn, _, ⟨h, hh, rfl⟩, rfl⟩

theorem isN_isUnit_det {x : Matrix (Idx r k) (Idx r k) A} (hx : IsN x) : IsUnit x.det := by
  rw [((isN_iff x).1 hx).det]; exact isUnit_one


theorem isS_set (x : Matrix (Idx r k) (Idx r k) A) :
    IsS x ↔ ∃ g ∈ PG r (⊤ : Subgroup (GL (Fin k) A)), (g : Matrix (Idx r k) (Idx r k) A) = x := by
  constructor
  · rintro ⟨n, _, hn, ⟨h, hh, rfl⟩, rfl⟩
    exact ⟨toGL n (isN_isUnit_det hn) * phi A r k (toGL h hh),
      (mem_PG _ _).2 ⟨_, _, Subgroup.mem_top _, hn, rfl⟩, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨n, h, -, hn, rfl⟩ := (mem_PG _ _).1 hg
    exact ⟨n, _, hn, ⟨h, (Matrix.isUnit_iff_isUnit_det _).1 h.isUnit, rfl⟩, rfl⟩

theorem isNU_set (x : Matrix (Idx r k) (Idx r k) A) :
    IsNU x ↔ ∃ g ∈ PG r (upUniG A k), (g : Matrix (Idx r k) (Idx r k) A) = x := by
  constructor
  · rintro ⟨n, _, hn, ⟨u, hu, rfl⟩, rfl⟩
    have hd : IsUnit u.det := by rw [isUpUni_det A hu]; exact isUnit_one
    exact ⟨toGL n (isN_isUnit_det hn) * phi A r k (toGL u hd),
      (mem_PG _ _).2 ⟨_, toGL u hd, hu, hn, rfl⟩, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨n, h, hh, hn, rfl⟩ := (mem_PG _ _).1 hg
    exact ⟨n, _, hn, ⟨h, hh, rfl⟩, rfl⟩

theorem isS_iff (g : GL (Idx r k) A) :
    IsS (g : Matrix (Idx r k) (Idx r k) A) ↔ g ∈ PG r (⊤ : Subgroup (GL (Fin k) A)) := by
  rw [isS_set]
  constructor
  · rintro ⟨g', hg', e⟩; rwa [← Units.ext e]
  · intro hg; exact ⟨g, hg, rfl⟩

theorem isNU_iff (g : GL (Idx r k) A) :
    IsNU (g : Matrix (Idx r k) (Idx r k) A) ↔ g ∈ PG r (upUniG A k) := by
  rw [isNU_set]
  constructor
  · rintro ⟨g', hg', e⟩; rwa [← Units.ext e]
  · intro hg; exact ⟨g, hg, rfl⟩



theorem card_S : Nat.card {x : Matrix (Idx r k) (Idx r k) A // IsS x} =
    Nat.card (PG r (⊤ : Subgroup (GL (Fin k) A))) :=
  card_of_subgroupSet _ _ isS_set

end Specific

section Local

variable (o : Type) [CommRing o] [IsLocalRing o]

local notation "𝔽" => IsLocalRing.ResidueField o

theorem coe_red (ι : Type) [Fintype ι] [DecidableEq ι] (g : GL ι o) :
    (red o ι g : Matrix ι ι 𝔽) = (g : Matrix ι ι o).map (IsLocalRing.residue o) := rfl

theorem red_surjective (ι : Type) [Fintype ι] [DecidableEq ι] : Function.Surjective (red o ι) := by
  intro g
  let y : Matrix ι ι o := Matrix.of fun i j =>
    Function.surjInv IsLocalRing.residue_surjective ((g : Matrix ι ι 𝔽) i j)
  have hy : y.map (IsLocalRing.residue o) = (g : Matrix ι ι 𝔽) := by
    ext i j
    simp [y, Function.surjInv_eq]
  have hdet : IsUnit y.det := by
    have h1 : IsLocalRing.residue o y.det = (g : Matrix ι ι 𝔽).det := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, hy]
    have h2 : IsUnit (IsLocalRing.residue o y.det) := by
      rw [h1]; exact (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit
    exact isUnit_of_map_unit (IsLocalRing.residue o) _ h2
  exact ⟨toGL y hdet, Units.ext hy⟩

variable {o} {r k : ℕ}

theorem red_phi (h : GL (Fin k) o) :
    red o (Idx r k) (phi o r k h) = phi 𝔽 r k (red o (Fin k) h) := by
  apply Units.ext
  rw [coe_red, coe_phi, coe_phi, coe_red, hEmb_map]






end Local

end Formalism.FourierDecayAlt.P.S3x2

namespace Formalism.FourierDecayAlt.P

open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.S3 Formalism.FourierDecayAlt.P.S3x2








end Formalism.FourierDecayAlt.P
