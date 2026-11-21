import Formalism.HermitianCurvature.MemParahoricTimesPrincipalCongruenceIff

namespace Formalism.FourierDecayAlt.P.S3x3

open Matrix Formalism.FourierDecayAlt.S3
open Formalism.DoubleCosetMeasures (IsUpUni upUniG)

section Blocks

variable {A : Type} {r k : ℕ}

@[simp] theorem block11_map {B : Type} (f : A → B) (x : Matrix (Idx r k) (Idx r k) A) :
    b11 (x.map f) = (b11 x).map f := rfl

@[simp] theorem block12_map {B : Type} (f : A → B) (x : Matrix (Idx r k) (Idx r k) A) :
    b12 (x.map f) = (b12 x).map f := rfl

@[simp] theorem block13_map {B : Type} (f : A → B) (x : Matrix (Idx r k) (Idx r k) A) :
    b13 (x.map f) = (b13 x).map f := rfl

@[simp] theorem block21_map {B : Type} (f : A → B) (x : Matrix (Idx r k) (Idx r k) A) :
    b21 (x.map f) = (b21 x).map f := rfl

@[simp] theorem block22_map {B : Type} (f : A → B) (x : Matrix (Idx r k) (Idx r k) A) :
    b22 (x.map f) = (b22 x).map f := rfl

@[simp] theorem block23_map {B : Type} (f : A → B) (x : Matrix (Idx r k) (Idx r k) A) :
    b23 (x.map f) = (b23 x).map f := rfl

@[simp] theorem block31_map {B : Type} (f : A → B) (x : Matrix (Idx r k) (Idx r k) A) :
    b31 (x.map f) = (b31 x).map f := rfl

@[simp] theorem block32_map {B : Type} (f : A → B) (x : Matrix (Idx r k) (Idx r k) A) :
    b32 (x.map f) = (b32 x).map f := rfl

@[simp] theorem block33_map {B : Type} (f : A → B) (x : Matrix (Idx r k) (Idx r k) A) :
    b33 (x.map f) = (b33 x).map f := rfl

variable [CommRing A]

theorem block11_mul (x y : Matrix (Idx r k) (Idx r k) A) :
    b11 (x * y) = b11 x * b11 y + b12 x * b21 y + b13 x * b31 y := by
  ext i j
  simp [b11, b11, b12, b13, b11, b21, b31, Matrix.mul_apply, Fintype.sum_sum_type, add_assoc]

theorem block12_mul (x y : Matrix (Idx r k) (Idx r k) A) :
    b12 (x * y) = b11 x * b12 y + b12 x * b22 y + b13 x * b32 y := by
  ext i j
  simp [b12, b11, b12, b13, b12, b22, b32, Matrix.mul_apply, Fintype.sum_sum_type, add_assoc]

theorem block13_mul (x y : Matrix (Idx r k) (Idx r k) A) :
    b13 (x * y) = b11 x * b13 y + b12 x * b23 y + b13 x * b33 y := by
  ext i j
  simp [b13, b11, b12, b13, b13, b23, b33, Matrix.mul_apply, Fintype.sum_sum_type, add_assoc]

theorem block21_mul (x y : Matrix (Idx r k) (Idx r k) A) :
    b21 (x * y) = b21 x * b11 y + b22 x * b21 y + b23 x * b31 y := by
  ext i j
  simp [b21, b21, b22, b23, b11, b21, b31, Matrix.mul_apply, Fintype.sum_sum_type, add_assoc]

theorem block22_mul (x y : Matrix (Idx r k) (Idx r k) A) :
    b22 (x * y) = b21 x * b12 y + b22 x * b22 y + b23 x * b32 y := by
  ext i j
  simp [b22, b21, b22, b23, b12, b22, b32, Matrix.mul_apply, Fintype.sum_sum_type, add_assoc]

theorem block23_mul (x y : Matrix (Idx r k) (Idx r k) A) :
    b23 (x * y) = b21 x * b13 y + b22 x * b23 y + b23 x * b33 y := by
  ext i j
  simp [b23, b21, b22, b23, b13, b23, b33, Matrix.mul_apply, Fintype.sum_sum_type, add_assoc]

theorem block31_mul (x y : Matrix (Idx r k) (Idx r k) A) :
    b31 (x * y) = b31 x * b11 y + b32 x * b21 y + b33 x * b31 y := by
  ext i j
  simp [b31, b31, b32, b33, b11, b21, b31, Matrix.mul_apply, Fintype.sum_sum_type, add_assoc]

theorem block32_mul (x y : Matrix (Idx r k) (Idx r k) A) :
    b32 (x * y) = b31 x * b12 y + b32 x * b22 y + b33 x * b32 y := by
  ext i j
  simp [b32, b31, b32, b33, b12, b22, b32, Matrix.mul_apply, Fintype.sum_sum_type, add_assoc]

theorem block33_mul (x y : Matrix (Idx r k) (Idx r k) A) :
    b33 (x * y) = b31 x * b13 y + b32 x * b23 y + b33 x * b33 y := by
  ext i j
  simp [b33, b31, b32, b33, b13, b23, b33, Matrix.mul_apply, Fintype.sum_sum_type, add_assoc]

@[simp] theorem block11_levi_embedding (h : Matrix (Fin k) (Fin k) A) : b11 (hEmb r h) = 1 := by
  ext i j
  simp [b11, hEmb, Matrix.one_apply]

@[simp] theorem block12_levi_embedding (h : Matrix (Fin k) (Fin k) A) : b12 (hEmb r h) = 0 := by
  ext i j
  simp [b12, hEmb]

@[simp] theorem block13_levi_embedding (h : Matrix (Fin k) (Fin k) A) : b13 (hEmb r h) = 0 := by
  ext i j
  simp [b13, hEmb]

@[simp] theorem block21_levi_embedding (h : Matrix (Fin k) (Fin k) A) : b21 (hEmb r h) = 0 := by
  ext i j
  simp [b21, hEmb]

@[simp] theorem block22_levi_embedding (h : Matrix (Fin k) (Fin k) A) : b22 (hEmb r h) = midEmb h := by
  ext i j
  simp [b22, hEmb]

@[simp] theorem block23_levi_embedding (h : Matrix (Fin k) (Fin k) A) : b23 (hEmb r h) = 0 := by
  ext i j
  simp [b23, hEmb]

@[simp] theorem block31_levi_embedding (h : Matrix (Fin k) (Fin k) A) : b31 (hEmb r h) = 0 := by
  ext i j
  simp [b31, hEmb]

@[simp] theorem block32_levi_embedding (h : Matrix (Fin k) (Fin k) A) : b32 (hEmb r h) = 0 := by
  ext i j
  simp [b32, hEmb]

@[simp] theorem block33_levi_embedding (h : Matrix (Fin k) (Fin k) A) : b33 (hEmb r h) = 1 := by
  ext i j
  simp [b33, hEmb, Matrix.one_apply]

@[simp] theorem block11_mul_levi_embedding (x : Matrix (Idx r k) (Idx r k) A) (h : Matrix (Fin k) (Fin k) A) :
    b11 (x * hEmb r h) = b11 x := by
  simp [block11_mul]

@[simp] theorem block12_mul_levi_embedding (x : Matrix (Idx r k) (Idx r k) A) (h : Matrix (Fin k) (Fin k) A) :
    b12 (x * hEmb r h) = b12 x * midEmb h := by
  simp [block12_mul]

@[simp] theorem block13_mul_levi_embedding (x : Matrix (Idx r k) (Idx r k) A) (h : Matrix (Fin k) (Fin k) A) :
    b13 (x * hEmb r h) = b13 x := by
  simp [block13_mul]

@[simp] theorem block21_mul_levi_embedding (x : Matrix (Idx r k) (Idx r k) A) (h : Matrix (Fin k) (Fin k) A) :
    b21 (x * hEmb r h) = b21 x := by
  simp [block21_mul]

@[simp] theorem block22_mul_levi_embedding (x : Matrix (Idx r k) (Idx r k) A) (h : Matrix (Fin k) (Fin k) A) :
    b22 (x * hEmb r h) = b22 x * midEmb h := by
  simp [block22_mul]

@[simp] theorem block23_mul_levi_embedding (x : Matrix (Idx r k) (Idx r k) A) (h : Matrix (Fin k) (Fin k) A) :
    b23 (x * hEmb r h) = b23 x := by
  simp [block23_mul]

@[simp] theorem block31_mul_levi_embedding (x : Matrix (Idx r k) (Idx r k) A) (h : Matrix (Fin k) (Fin k) A) :
    b31 (x * hEmb r h) = b31 x := by
  simp [block31_mul]

@[simp] theorem block32_mul_levi_embedding (x : Matrix (Idx r k) (Idx r k) A) (h : Matrix (Fin k) (Fin k) A) :
    b32 (x * hEmb r h) = b32 x * midEmb h := by
  simp [block32_mul]

@[simp] theorem block33_mul_levi_embedding (x : Matrix (Idx r k) (Idx r k) A) (h : Matrix (Fin k) (Fin k) A) :
    b33 (x * hEmb r h) = b33 x := by
  simp [block33_mul]

@[simp] theorem block11_levi_embedding_mul (x : Matrix (Idx r k) (Idx r k) A) (h : Matrix (Fin k) (Fin k) A) :
    b11 (hEmb r h * x) = b11 x := by
  simp [block11_mul]

@[simp] theorem block12_levi_embedding_mul (x : Matrix (Idx r k) (Idx r k) A) (h : Matrix (Fin k) (Fin k) A) :
    b12 (hEmb r h * x) = b12 x := by
  simp [block12_mul]

@[simp] theorem block13_levi_embedding_mul (x : Matrix (Idx r k) (Idx r k) A) (h : Matrix (Fin k) (Fin k) A) :
    b13 (hEmb r h * x) = b13 x := by
  simp [block13_mul]

@[simp] theorem block21_levi_embedding_mul (x : Matrix (Idx r k) (Idx r k) A) (h : Matrix (Fin k) (Fin k) A) :
    b21 (hEmb r h * x) = midEmb h * b21 x := by
  simp [block21_mul]

@[simp] theorem block22_levi_embedding_mul (x : Matrix (Idx r k) (Idx r k) A) (h : Matrix (Fin k) (Fin k) A) :
    b22 (hEmb r h * x) = midEmb h * b22 x := by
  simp [block22_mul]

@[simp] theorem block23_levi_embedding_mul (x : Matrix (Idx r k) (Idx r k) A) (h : Matrix (Fin k) (Fin k) A) :
    b23 (hEmb r h * x) = midEmb h * b23 x := by
  simp [block23_mul]

@[simp] theorem block31_levi_embedding_mul (x : Matrix (Idx r k) (Idx r k) A) (h : Matrix (Fin k) (Fin k) A) :
    b31 (hEmb r h * x) = b31 x := by
  simp [block31_mul]

@[simp] theorem block32_levi_embedding_mul (x : Matrix (Idx r k) (Idx r k) A) (h : Matrix (Fin k) (Fin k) A) :
    b32 (hEmb r h * x) = b32 x := by
  simp [block32_mul]

@[simp] theorem block33_levi_embedding_mul (x : Matrix (Idx r k) (Idx r k) A) (h : Matrix (Fin k) (Fin k) A) :
    b33 (hEmb r h * x) = b33 x := by
  simp [block33_mul]

end Blocks

section Alg

variable {A : Type} [CommRing A] {r k : ℕ}

theorem midEmb_mul (a b : Matrix (Fin k) (Fin k) A) : midEmb (a * b) = midEmb a * midEmb b := by
  simp [midEmb, Matrix.fromBlocks_multiply]

theorem midEmb_one : midEmb (1 : Matrix (Fin k) (Fin k) A) = 1 := by
  simp [midEmb]

theorem midEmb_inj {a b : Matrix (Fin k) (Fin k) A} (h : midEmb a = midEmb b) : a = b :=
  (Matrix.fromBlocks_inj.1 h).1

theorem hEmb_mul (a b : Matrix (Fin k) (Fin k) A) : hEmb r (a * b) = hEmb r a * hEmb r b := by
  simp [hEmb, Matrix.fromBlocks_multiply, midEmb_mul]

theorem hEmb_one : hEmb r (1 : Matrix (Fin k) (Fin k) A) = 1 := by
  simp [hEmb, midEmb_one]

theorem det_hEmb (h : Matrix (Fin k) (Fin k) A) : (hEmb r h).det = h.det := by
  simp [hEmb, midEmb, Matrix.det_fromBlocks_zero₂₁]

theorem hEmb_map {B : Type} [CommRing B] (f : A →+* B) (h : Matrix (Fin k) (Fin k) A) :
    (hEmb r h).map f = hEmb r (h.map f) := by
  simp [hEmb, midEmb, Matrix.fromBlocks_map]


theorem isUpUni_map {B : Type} [CommRing B] (f : A →+* B) {n : ℕ} {x : Matrix (Fin n) (Fin n) A}
    (hx : IsUpUni x) : IsUpUni (x.map f) :=
  ⟨fun i j hij => by simp [hx.1 hij], fun a => by simp [hx.2 a]⟩


theorem isN_map {B : Type} [CommRing B] (f : A →+* B) {n : Matrix (Idx r k) (Idx r k) A}
    (hn : IsN n) : IsN (n.map f) := by
  obtain ⟨h11, h33, h22, h21, h31, h32⟩ := hn
  refine ⟨isUpUni_map f h11, isUpUni_map f h33, ?_, ?_, ?_, ?_⟩
  · rw [block22_map, h22]; simp
  · rw [block21_map, h21]; simp
  · rw [block31_map, h31]; simp
  · rw [block32_map, h32]; simp




end Alg

section Integral

variable (o : Type) [CommRing o] {k0 : Type} [Field k0] [Algebra o k0]




variable [IsFractionRing o k0]




variable [IsLocalRing o]



end Integral

section Counting

theorem red_surjective (o : Type) [CommRing o] [IsLocalRing o] (ι : Type) [Fintype ι]
    [DecidableEq ι] : Function.Surjective (red o ι) := by
  intro g
  choose y hy using fun i j => IsLocalRing.residue_surjective ((g : Matrix ι ι (IsLocalRing.ResidueField o)) i j)
  have hmap : (Matrix.of y).map (IsLocalRing.residue o) = g := by
    ext i j; simp [hy]
  have hdet : IsUnit (Matrix.of y).det := by
    have h1 : IsUnit (IsLocalRing.residue o (Matrix.of y).det) := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, hmap]
      exact (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit
    exact isUnit_of_map_unit _ _ h1
  refine ⟨((Matrix.isUnit_iff_isUnit_det _).2 hdet).unit, ?_⟩
  apply Units.ext
  exact hmap

theorem index_mul_card {G H : Type} [Group G] [Group H] (f : G →* H)
    (hf : Function.Surjective f) (K : Subgroup G) (P : H → Prop) (hK : ∀ x, x ∈ K ↔ P (f x)) :
    K.index * Nat.card {h : H // P h} = Nat.card H := by
  have e : K = (K.map f).comap f := by
    ext x
    simp only [Subgroup.mem_comap, Subgroup.mem_map]
    constructor
    · intro hx; exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, e⟩; rw [hK, ← e, ← hK]; exact hy
  have hmem : ∀ h, h ∈ K.map f ↔ P h := by
    intro h
    obtain ⟨x, rfl⟩ := hf h
    constructor
    · rintro ⟨y, hy, e⟩; rw [← e, ← hK]; exact hy
    · intro hp; exact ⟨x, (hK x).2 hp, rfl⟩
  have h1 : K.index = (K.map f).index :=
    (congrArg Subgroup.index e).trans (Subgroup.index_comap_of_surjective _ hf)
  rw [h1, ← Subgroup.index_mul_card (K.map f)]
  congr 1
  exact Nat.card_congr (Equiv.subtypeEquivRight (fun h => (hmem h).symm))

theorem card_GL_subtype {ι K : Type} [Fintype ι] [DecidableEq ι] [CommRing K]
    (P : Matrix ι ι K → Prop) (hP : ∀ x, P x → IsUnit x.det) :
    Nat.card {g : GL ι K // P g} = Nat.card {x : Matrix ι ι K // P x} := by
  refine Nat.card_congr (Equiv.ofBijective (fun g => ⟨g.1, g.2⟩) ⟨?_, ?_⟩)
  · intro a b h
    exact Subtype.ext (Units.ext (congrArg Subtype.val h))
  · rintro ⟨x, hx⟩
    exact ⟨⟨((Matrix.isUnit_iff_isUnit_det x).2 (hP x hx)).unit, hx⟩, rfl⟩

variable {A : Type} [CommRing A] {r k : ℕ}

theorem card_prod_set (Q : Matrix (Fin k) (Fin k) A → Prop) (hQ : ∀ h, Q h → IsUnit h.det) :
    Nat.card {x : Matrix (Idx r k) (Idx r k) A //
        ∃ n h', IsN n ∧ (∃ h, Q h ∧ h' = hEmb r h) ∧ x = n * h'} =
      Nat.card {g : GL (Fin k) A // Q g} * Nat.card {x : Matrix (Idx r k) (Idx r k) A // IsN x} := by
  rw [card_GL_subtype Q hQ, ← Nat.card_prod]
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun p => ⟨p.2.1 * hEmb r p.1.1, p.2.1, hEmb r p.1.1, p.2.2, ⟨p.1.1, p.1.2, rfl⟩, rfl⟩) ⟨?_, ?_⟩)
  · rintro ⟨⟨g, hg⟩, ⟨n, hn⟩⟩ ⟨⟨g', hg'⟩, ⟨n', hn'⟩⟩ e
    have e1 : n * hEmb r g = n' * hEmb r g' := congrArg Subtype.val e
    have e2 := congrArg b22 e1
    rw [block22_mul_levi_embedding, block22_mul_levi_embedding, hn.2.2.1, hn'.2.2.1, one_mul, one_mul] at e2
    have e3 : g = g' := midEmb_inj e2
    subst e3
    have hu : IsUnit (hEmb r g) := (Matrix.isUnit_iff_isUnit_det _).2 (by rw [det_hEmb]; exact hQ g hg)
    have e4 : n = n' := hu.mul_left_injective e1
    subst e4
    rfl
  · rintro ⟨x, n, h', hn, ⟨h, hh, rfl⟩, rfl⟩
    exact ⟨⟨⟨h, hh⟩, ⟨n, hn⟩⟩, rfl⟩




theorem card_S : Nat.card {x : Matrix (Idx r k) (Idx r k) A // IsS x} =
    Nat.card (GL (Fin k) A) * Nat.card {x : Matrix (Idx r k) (Idx r k) A // IsN x} := by
  have h := card_prod_set (r := r) (fun h : Matrix (Fin k) (Fin k) A => IsUnit h.det) (fun _ h => h)
  have h2 : Nat.card {g : GL (Fin k) A // IsUnit (g : Matrix (Fin k) (Fin k) A).det} =
      Nat.card (GL (Fin k) A) :=
    Nat.card_congr (Equiv.subtypeUnivEquiv fun g => (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit)
  rw [h2] at h
  exact h


end Counting

section Levels

variable (o : Type) [CommRing o] [IsLocalRing o] {r k : ℕ} (L : Levels o r k)




end Levels

theorem ratios (I1 I2 I3 cN volK volKpp volKnat volKH volJH volNo cG cS cGLk cUk γ : ℝ)
    (hG : 0 < cG) (h1 : I1 * (cUk * cN) = cG) (h2 : I2 * (cGLk * cN) = cG) (h3 : I3 * cUk = cGLk)
    (hS : cS = cGLk * cN) (p1 : 0 < volKpp) (p2 : 0 < volKnat) (p3 : 0 < volJH) (p4 : 0 < volNo)
    (v1 : volK = I1 * volKpp) (v2 : volK = I2 * volKnat) (v3 : volKH = I3 * volJH)
    (hγ : γ = cGLk / cUk) :
    γ * cS / cG = γ ^ 2 / I1 ∧
      volKnat / volK = cS / cG ∧
      (volKnat / (volNo * volKH) ^ 2) / (volK / (volNo * volKH) ^ 2) = cS / cG ∧
      (volKpp / volJH ^ 2) / (volK / volKH ^ 2) = γ ^ 2 / I1 ∧
      γ * (volKnat / (volNo * volKH) ^ 2) = (volKpp / volJH ^ 2) / volNo ^ 2 := by
  have hI1 : I1 ≠ 0 := by rintro rfl; simp at h1; exact hG.ne h1
  have hUk : cUk ≠ 0 := by rintro rfl; simp at h1; exact hG.ne h1
  have hN : cN ≠ 0 := by rintro rfl; simp at h1; exact hG.ne h1
  have hI2 : I2 ≠ 0 := by rintro rfl; simp at h2; exact hG.ne h2
  have hGLk : cGLk ≠ 0 := by rintro rfl; simp at h2; exact hG.ne h2
  have hI3 : I3 ≠ 0 := by rintro rfl; simp at h3; exact hGLk h3.symm
  have hγ' : γ = I3 := by rw [hγ, ← h3]; field_simp
  have h12 : I1 = I2 * I3 := by
    have : I1 * (cUk * cN) = (I2 * I3) * (cUk * cN) := by rw [h1, ← h2, ← h3]; ring
    exact mul_right_cancel₀ (mul_ne_zero hUk hN) this
  have hv : volKnat = I3 * volKpp := by
    have : I2 * volKnat = I2 * (I3 * volKpp) := by rw [← v2, v1, h12]; ring
    exact mul_left_cancel₀ hI2 this
  subst hγ' hS
  subst v3 v1 hv h12
  rw [← h2, ← h3]
  have q1 := p1.ne'
  have q3 := p3.ne'
  have q4 := p4.ne'
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> field_simp

end Formalism.FourierDecayAlt.P.S3x3

namespace Formalism.FourierDecayAlt.P



end Formalism.FourierDecayAlt.P
