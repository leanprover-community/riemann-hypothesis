import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.IsUnimodularAtIffVd
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsLocalData
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocalDensityEighth

section
open NumberField Module Matrix

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.hermitianFormColumns

open HermitianSublattices idealPowerSpanBounds traceDeterminantCongruences reductionMapsOfForms

section col

variable {A : Type*} [CommRing A] [StarRing A] {m : Type} [Fintype m] [DecidableEq m]

def colU : (m → A) ≃ Matrix m Unit A where
  toFun x := Matrix.of fun i _ => x i
  invFun X := fun i => X i ()
  left_inv _ := rfl
  right_inv _ := rfl

theorem form_col (H : Matrix m m A) (x y : m → A) (a b : Unit) :
    ((colU x)ᴴ * H * colU y) a b = star x ⬝ᵥ (H *ᵥ y) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, colU, Equiv.coe_fn_mk, Matrix.of_apply,
    dotProduct, Matrix.mulVec, Pi.star_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun l _ => ?_))
  show star (x i) * H i l * y l = _
  ring

end col

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable [Fact (IsFixF K F)]
variable {m : Type} [Fintype m] [DecidableEq m]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)

abbrev fm {A : Type*} [CommRing A] [StarRing A] (H : Matrix m m A) (x y : m → A) : A :=
  star x ⬝ᵥ (H *ᵥ y)

private theorem conjTranspose_mul_mul_col_eq_const_iff_fm {A : Type*} [CommRing A] [StarRing A] (Hq : Matrix m m A) (t : A)
    (X : Matrix m Unit A) :
    Xᴴ * Hq * X = Matrix.of (fun _ _ => t) ↔ fm Hq (fun i => X i ()) (fun i => X i ()) = t := by
  have hX : X = colU (fun i => X i ()) := by
    ext i u
    rfl
  constructor
  · intro h
    have h1 := congrFun (congrFun h ()) ()
    rw [hX, form_col] at h1
    exact h1
  · intro h
    ext a b
    rw [hX, form_col]
    exact h

theorem card_vec_succ (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    (H : Matrix m m (𝓞 K)) (hH : Hᴴ = H) (n : 𝓞 F) {k j : ℕ}
    (hj : k + 1 ≤ 2 * j) (p' : (m → 𝓞 K ⧸ extP K 𝔭 ^ k) → Prop)
    (hinv : ∀ x y : m → 𝓞 K, (∀ a, y a ∈ extP K 𝔭 ^ j) →
      (p' (fun i => mkk K 𝔭 k ((x + y) i)) ↔ p' (fun i => mkk K 𝔭 k (x i))))
    (RC : ∀ x : m → 𝓞 K, p' (fun i => mkk K 𝔭 k (x i)) → fm H x x - ι n ∈ extP K 𝔭 ^ k →
      ∀ s ∈ extP K 𝔭 ^ k, star s - s ∈ extP K 𝔭 ^ (k + 1) →
      ∃ y : m → 𝓞 K, (∀ a, y a ∈ extP K 𝔭 ^ j) ∧ fm H x y + fm H y x - s ∈ extP K 𝔭 ^ (k + 1)) :
    Nat.card {x : m → 𝓞 K ⧸ extP K 𝔭 ^ (k + 1) // p' (fun i => piQ K 𝔭 k (x i)) ∧
        fm (H.map (mkk K 𝔭 (k + 1))) x x = mkk K 𝔭 (k + 1) (ι n)} * Ideal.absNorm 𝔭 =
      Ideal.absNorm 𝔭 ^ (2 * Fintype.card m) *
        Nat.card {x : m → 𝓞 K ⧸ extP K 𝔭 ^ k // p' x ∧
          fm (H.map (mkk K 𝔭 k)) x x = mkk K 𝔭 k (ι n)} := by
  have hF : IsFixF K F := Fact.out
  obtain ⟨T, hTdef⟩ : ∃ T : Matrix Unit Unit (𝓞 K), T = Matrix.of (fun _ _ => ι n) := ⟨_, rfl⟩
  have hT : Tᴴ = T := by
    rw [hTdef]
    refine Matrix.ext fun a b => ?_
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply]
    rw [idealPowerSpanBounds.star_def]
    exact conjO_map hF n
  have RC'' : ∀ X : Matrix m Unit (𝓞 K), (fun X => p' (fun i => X i ())) (X.map (mkk K 𝔭 k)) →
      (∀ a b, (Xᴴ * H * X - T) a b ∈ extP K 𝔭 ^ k) → ∀ S : Matrix Unit Unit (𝓞 K),
      (∀ a b, S a b ∈ extP K 𝔭 ^ k) → (∀ a b, (Sᴴ - S) a b ∈ extP K 𝔭 ^ (k + 1)) →
      ∃ Y : Matrix m Unit (𝓞 K), (∀ a b, Y a b ∈ extP K 𝔭 ^ j) ∧
        ∀ a b, (Xᴴ * H * Y + Yᴴ * H * X - S) a b ∈ extP K 𝔭 ^ (k + 1) := by
    intro X hp hX S hS hS'
    have hXc : X = colU (fun i => X i ()) := by
      ext i u
      rfl
    have hx : fm H (fun i => X i ()) (fun i => X i ()) - ι n ∈ extP K 𝔭 ^ k := by
      have h1 := hX () ()
      rw [Matrix.sub_apply, hXc, form_col, hTdef, Matrix.of_apply] at h1
      exact h1
    obtain ⟨y, hy, hy'⟩ := RC (fun i => X i ()) hp hx (S () ()) (hS () ()) (hS' () ())
    refine ⟨colU y, fun a b => hy a, fun a b => ?_⟩
    rw [Matrix.sub_apply, Matrix.add_apply, hXc, form_col, form_col]
    exact hy'
  have h := card_rep_succ (m := m) (r := Unit) hK h𝔭 H hH T hT hj (fun X => p' (fun i => X i ()))
    (fun X Y hY => hinv (fun i => X i ()) (fun i => Y i ()) (fun a => hY a ())) RC''
  have c1 : Nat.card {x : m → 𝓞 K ⧸ extP K 𝔭 ^ (k + 1) // p' (fun i => piQ K 𝔭 k (x i)) ∧
        fm (H.map (mkk K 𝔭 (k + 1))) x x = mkk K 𝔭 (k + 1) (ι n)} =
      Nat.card {X : Matrix m Unit (𝓞 K ⧸ extP K 𝔭 ^ (k + 1)) //
        (fun X => p' (fun i => X i ())) (X.map (piQ K 𝔭 k)) ∧
        Xᴴ * H.map (mkk K 𝔭 (k + 1)) * X = T.map (mkk K 𝔭 (k + 1))} := by
    rw [hTdef]
    exact Nat.card_congr (Equiv.subtypeEquiv colU (fun x => and_congr Iff.rfl
      (conjTranspose_mul_mul_col_eq_const_iff_fm (H.map (mkk K 𝔭 (k + 1))) (mkk K 𝔭 (k + 1) (ι n)) (colU x)).symm))
  have c2 : Nat.card {x : m → 𝓞 K ⧸ extP K 𝔭 ^ k // p' x ∧
        fm (H.map (mkk K 𝔭 k)) x x = mkk K 𝔭 k (ι n)} =
      Nat.card {X : Matrix m Unit (𝓞 K ⧸ extP K 𝔭 ^ k) // (fun X => p' (fun i => X i ())) X ∧
        Xᴴ * H.map (mkk K 𝔭 k) * X = T.map (mkk K 𝔭 k)} := by
    rw [hTdef]
    exact Nat.card_congr (Equiv.subtypeEquiv colU (fun x => and_congr Iff.rfl
      (conjTranspose_mul_mul_col_eq_const_iff_fm (H.map (mkk K 𝔭 k)) (mkk K 𝔭 k (ι n)) (colU x)).symm))
  rw [c1, c2]
  simp only [Fintype.card_unit, mul_one, pow_one] at h
  exact h

section star

variable {A : Type*} [CommRing A] [StarRing A]


theorem fm_eq (H : Matrix m m A) (x y : m → A) : fm H x y = (star x ᵥ* H) ⬝ᵥ y := Matrix.dotProduct_mulVec (star x) H y

theorem fm_star {H : Matrix m m A} (hH : Hᴴ = H) (x y : m → A) : fm H y x = star (fm H x y) := by
  have hHij : ∀ i j, star (H i j) = H j i := fun i j => by
    rw [← Matrix.conjTranspose_apply, hH]
  simp only [fm, dotProduct, Matrix.mulVec, Pi.star_apply, star_sum, star_mul', star_star, hHij,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  ring

theorem vecMul_adjugate (H : Matrix m m A) (x : m → A) :
    (x ᵥ* H) ᵥ* H.adjugate = H.det • x := by
  rw [Matrix.vecMul_vecMul, Matrix.mul_adjugate, Matrix.vecMul_smul, Matrix.vecMul_one]

theorem vecMul_mem {J : Ideal A} {w : m → A} (hw : ∀ j, w j ∈ J) (M : Matrix m m A) (i : m) :
    (w ᵥ* M) i ∈ J := by
  simp only [Matrix.vecMul, dotProduct]
  exact Ideal.sum_mem _ (fun j _ => Ideal.mul_mem_right _ _ (hw j))

end star

def Qc (𝔭 : Ideal (𝓞 F)) (k c : ℕ) (H : Matrix m m (𝓞 K)) (x : m → 𝓞 K ⧸ extP K 𝔭 ^ k) : Prop :=
  ∃ j, (star x ᵥ* H.map (mkk K 𝔭 k)) j ∉ idQ K 𝔭 k (c + 1)

theorem Qc_mk {𝔭 : Ideal (𝓞 F)} {k c : ℕ} (hck : c + 1 ≤ k) (H : Matrix m m (𝓞 K)) (x : m → 𝓞 K) :
    Qc 𝔭 k c H (fun i => mkk K 𝔭 k (x i)) ↔ ∃ j, (star x ᵥ* H) j ∉ extP K 𝔭 ^ (c + 1) := by
  have e : ∀ j, (star (fun i => mkk K 𝔭 k (x i)) ᵥ* H.map (mkk K 𝔭 k)) j =
      mkk K 𝔭 k ((star x ᵥ* H) j) := by
    intro j
    have hs : star (fun i => mkk K 𝔭 k (x i)) = fun i => mkk K 𝔭 k (star x i) := by
      funext i
      exact idealPowerSpanBounds.star_mk 𝔭 k (x i)
    rw [hs]
    exact (RingHom.map_vecMul (mkk K 𝔭 k) H (star x) j).symm
  unfold Qc
  simp only [e, mk_mem_idQ hck]

theorem exists_liftv (𝔭 : Ideal (𝓞 F)) (k : ℕ) (x : m → 𝓞 K ⧸ extP K 𝔭 ^ k) :
    ∃ y : m → 𝓞 K, (fun i => mkk K 𝔭 k (y i)) = x := by
  choose f hf using fun z : 𝓞 K ⧸ extP K 𝔭 ^ k => Ideal.Quotient.mk_surjective z
  exact ⟨fun i => f (x i), funext fun i => hf _⟩

theorem Qc_piQ {𝔭 : Ideal (𝓞 F)} {k c : ℕ} (hck : c + 1 ≤ k) (H : Matrix m m (𝓞 K))
    (x : m → 𝓞 K ⧸ extP K 𝔭 ^ (k + 1)) :
    Qc 𝔭 k c H (fun i => piQ K 𝔭 k (x i)) ↔ Qc 𝔭 (k + 1) c H x := by
  obtain ⟨y, rfl⟩ := exists_liftv 𝔭 (k + 1) x
  rw [Qc_mk (by omega) H y]
  exact Qc_mk hck H y

theorem mk_fm (𝔭 : Ideal (𝓞 F)) (k : ℕ) (H : Matrix m m (𝓞 K)) (x y : m → 𝓞 K) :
    fm (H.map (mkk K 𝔭 k)) (fun i => mkk K 𝔭 k (x i)) (fun i => mkk K 𝔭 k (y i)) =
      mkk K 𝔭 k (fm H x y) := by
  have hs : star (fun i => mkk K 𝔭 k (x i)) = fun i => mkk K 𝔭 k (star x i) := by
    funext i
    exact idealPowerSpanBounds.star_mk 𝔭 k (x i)
  have hv : H.map (mkk K 𝔭 k) *ᵥ (fun i => mkk K 𝔭 k (y i)) =
      fun i => mkk K 𝔭 k ((H *ᵥ y) i) := by
    funext i
    exact (RingHom.map_mulVec (mkk K 𝔭 k) H y i).symm
  show star (fun i => mkk K 𝔭 k (x i)) ⬝ᵥ (H.map (mkk K 𝔭 k) *ᵥ (fun i => mkk K 𝔭 k (y i))) =
    mkk K 𝔭 k (star x ⬝ᵥ (H *ᵥ y))
  rw [hs, hv, RingHom.map_dotProduct]
  rfl

def nkQ (𝔭 : Ideal (𝓞 F)) (k c : ℕ) (H : Matrix m m (𝓞 K)) (n : 𝓞 F) : ℕ :=
  Nat.card {x : m → 𝓞 K ⧸ extP K 𝔭 ^ k // Qc 𝔭 k c H x ∧
    fm (H.map (mkk K 𝔭 k)) x x = mkk K 𝔭 k (ι n)}

def nkM (𝔭 : Ideal (𝓞 F)) (k : ℕ) (H : Matrix m m (𝓞 K)) (n : 𝓞 F) : ℕ :=
  Nat.card {x : m → 𝓞 K ⧸ extP K 𝔭 ^ k // fm (H.map (mkk K 𝔭 k)) x x = mkk K 𝔭 k (ι n)}

theorem nkQ_succ (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    {H : Matrix m m (𝓞 K)} (hH : Hᴴ = H) (n : 𝓞 F) {c k : ℕ} (hk : 2 * c + 1 ≤ k) :
    nkQ 𝔭 (k + 1) c H n * Ideal.absNorm 𝔭 = Ideal.absNorm 𝔭 ^ (2 * Fintype.card m) * nkQ 𝔭 k c H n := by
  have hF : IsFixF K F := Fact.out
  have hck : c + 1 ≤ k := by omega
  have hj : k + 1 ≤ 2 * (k - c) := by omega
  have hinv : ∀ x y : m → 𝓞 K, (∀ a, y a ∈ extP K 𝔭 ^ (k - c)) →
      (Qc 𝔭 k c H (fun i => mkk K 𝔭 k ((x + y) i)) ↔ Qc 𝔭 k c H (fun i => mkk K 𝔭 k (x i))) := by
    intro x y hy
    rw [Qc_mk hck H, Qc_mk hck H]
    have hy' : ∀ j', (star y ᵥ* H) j' ∈ extP K 𝔭 ^ (c + 1) := fun j' =>
      Ideal.pow_le_pow_right (by omega)
        (vecMul_mem (fun a => conjO_mem_pow hF 𝔭 (k - c) _ (hy a)) H j')
    have e : ∀ j', (star (x + y) ᵥ* H) j' = (star x ᵥ* H) j' + (star y ᵥ* H) j' := by
      intro j'
      rw [star_add, Matrix.add_vecMul]
      rfl
    simp only [e]
    constructor
    · rintro ⟨j', hj'⟩
      exact ⟨j', fun h => hj' (Ideal.add_mem _ h (hy' j'))⟩
    · rintro ⟨j', hj'⟩
      refine ⟨j', fun h => hj' ?_⟩
      have h2 := Ideal.sub_mem _ h (hy' j')
      simpa using h2
  have RC : ∀ x : m → 𝓞 K, Qc 𝔭 k c H (fun i => mkk K 𝔭 k (x i)) →
      fm H x x - ι n ∈ extP K 𝔭 ^ k → ∀ s ∈ extP K 𝔭 ^ k, star s - s ∈ extP K 𝔭 ^ (k + 1) →
      ∃ y : m → 𝓞 K, (∀ a, y a ∈ extP K 𝔭 ^ (k - c)) ∧
        fm H x y + fm H y x - s ∈ extP K 𝔭 ^ (k + 1) := by
    intro x hQ _ s hs hs'
    obtain ⟨j0, hj0⟩ := (Qc_mk hck H x).mp hQ
    obtain ⟨r, hr, hr'⟩ := exists_solve_scalar hK hF h𝔭 (by omega : c ≤ k) hj0 hs hs'
    refine ⟨Pi.single j0 r, fun a => ?_, ?_⟩
    · by_cases ha : a = j0
      · subst ha
        simpa using hr
      · simp [Pi.single_apply, ha]
    · have e1 : fm H x (Pi.single j0 r) = (star x ᵥ* H) j0 * r := by
        rw [fm_eq]
        first
        | exact dotProduct_single _ _ _
        | simp [dotProduct, Pi.single_apply]
      rw [fm_star hH x (Pi.single j0 r), e1]
      exact hr'
  have h := card_vec_succ hK h𝔭 H hH n hj (Qc 𝔭 k c H) hinv RC
  have e : Nat.card {x : m → 𝓞 K ⧸ extP K 𝔭 ^ (k + 1) //
      Qc 𝔭 k c H (fun i => piQ K 𝔭 k (x i)) ∧
        fm (H.map (mkk K 𝔭 (k + 1))) x x = mkk K 𝔭 (k + 1) (ι n)} = nkQ 𝔭 (k + 1) c H n :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun x => by rw [Qc_piQ hck H x]))
  rw [e] at h
  exact h

theorem exists_notMem_of_sol {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {H : Matrix m m (𝓞 K)}
    (hH : Hᴴ = H) {D n : 𝓞 F} (hD : H.det = ι D) {d v c k : ℕ} (hDd : D ∉ 𝔭 ^ (d + 1))
    (hn : n ∉ 𝔭 ^ (v + 1)) (hk : d + v + 1 ≤ k) (hc : d + v + 1 ≤ 2 * (c + 1)) {x : m → 𝓞 K}
    (hx : fm H x x - ι n ∈ extP K 𝔭 ^ k) : ∃ j, (star x ᵥ* H) j ∉ extP K 𝔭 ^ (c + 1) := by
  have hF : IsFixF K F := Fact.out
  by_contra hall
  push_neg at hall
  have h1 : ∀ i, ι D * star (x i) ∈ extP K 𝔭 ^ (c + 1) := by
    intro i
    have h2 := vecMul_mem hall H.adjugate i
    rw [vecMul_adjugate, hD, Pi.smul_apply, smul_eq_mul] at h2
    exact h2
  have h3 : ∀ i, ι D * x i ∈ extP K 𝔭 ^ (c + 1) := by
    intro i
    have h4 := conjO_mem_pow hF 𝔭 (c + 1) _ (h1 i)
    rw [map_mul, conjO_map hF, ← idealPowerSpanBounds.star_def, star_star] at h4
    exact h4
  have h5 : ι D * fm H x x ∈ extP K 𝔭 ^ (d + v + 1) := by
    rw [fm_eq]
    simp only [dotProduct, Finset.mul_sum]
    refine Ideal.sum_mem _ (fun i _ => ?_)
    have h6 : (star x ᵥ* H) i * (ι D * x i) ∈ extP K 𝔭 ^ ((c + 1) + (c + 1)) := by
      rw [pow_add]
      exact Ideal.mul_mem_mul (hall i) (h3 i)
    have e : ι D * ((star x ᵥ* H) i * x i) = (star x ᵥ* H) i * (ι D * x i) := by ring
    rw [e]
    exact Ideal.pow_le_pow_right (by omega) h6
  have h7 : ι D * (fm H x x - ι n) ∈ extP K 𝔭 ^ (d + v + 1) :=
    Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right hk hx)
  have h8 : ι (D * n) ∈ extP K 𝔭 ^ (d + v + 1) := by
    have e : ι (D * n) = ι D * fm H x x - ι D * (fm H x x - ι n) := by
      rw [map_mul]
      ring
    rw [e]
    exact Ideal.sub_mem _ h5 h7
  rw [mem_pow_iff] at h8
  exact idealPowerSpanBounds.mul_notMem h𝔭.isPrime (idealPowerSpanBounds.ne_bot h𝔭) hDd hn h8

theorem nkM_eq_nkQ {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {H : Matrix m m (𝓞 K)}
    (hH : Hᴴ = H) {D n : 𝓞 F} (hD : H.det = ι D) {d v c k : ℕ} (hDd : D ∉ 𝔭 ^ (d + 1))
    (hn : n ∉ 𝔭 ^ (v + 1)) (hk : d + v + 1 ≤ k) (hc : d + v + 1 ≤ 2 * (c + 1)) (hck : c + 1 ≤ k) :
    nkM 𝔭 k H n = nkQ 𝔭 k c H n := by
  unfold nkM nkQ
  refine Nat.card_congr (Equiv.subtypeEquivRight (fun x => ?_))
  constructor
  · intro hx
    refine ⟨?_, hx⟩
    obtain ⟨y, rfl⟩ := exists_liftv 𝔭 k x
    rw [Qc_mk hck H y]
    rw [mk_fm] at hx
    have hy : fm H y y - ι n ∈ extP K 𝔭 ^ k := Ideal.Quotient.eq.mp hx
    exact exists_notMem_of_sol h𝔭 hH hD hDd hn hk hc hy
  · exact fun h => h.2

theorem nkM_succ (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    {H : Matrix m m (𝓞 K)} (hH : Hᴴ = H) {D n : 𝓞 F} (hD : H.det = ι D) {d v k : ℕ}
    (hDd : D ∉ 𝔭 ^ (d + 1)) (hn : n ∉ 𝔭 ^ (v + 1)) (hk : d + v + 1 ≤ k) :
    nkM 𝔭 (k + 1) H n * Ideal.absNorm 𝔭 = Ideal.absNorm 𝔭 ^ (2 * Fintype.card m) * nkM 𝔭 k H n := by
  obtain ⟨c, hcdef⟩ : ∃ c, c = (d + v) / 2 := ⟨_, rfl⟩
  have hc : d + v + 1 ≤ 2 * (c + 1) := by omega
  have h2c : 2 * c + 1 ≤ k := by omega
  rw [nkM_eq_nkQ (k := k + 1) (c := c) h𝔭 hH hD hDd hn (by omega) hc (by omega),
    nkM_eq_nkQ (k := k) (c := c) h𝔭 hH hD hDd hn hk hc (by omega)]
  exact nkQ_succ hK h𝔭 hH n h2c

end Formalism.HermitianLattices.Ext.L3.hermitianFormColumns
end
end

section
open NumberField Module Matrix

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.vectorCountBounds

open HermitianSublattices idealPowerSpanBounds traceDeterminantCongruences reductionMapsOfForms hermitianFormColumns

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable [Fact (IsFixF K F)]
variable {m : Type} [Fintype m] [DecidableEq m]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)

theorem finite_vec {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ) :
    Finite (m → 𝓞 K ⧸ extP K 𝔭 ^ k) := by
  haveI := finite_quot (K := K) h𝔭 k
  infer_instance

theorem card_vec (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ) :
    Nat.card (m → 𝓞 K ⧸ extP K 𝔭 ^ k) = Ideal.absNorm 𝔭 ^ (k * (2 * Fintype.card m)) := by
  haveI := finite_quot (K := K) h𝔭 k
  have h1 : Nat.card (m → 𝓞 K ⧸ extP K 𝔭 ^ k) =
      Nat.card (𝓞 K ⧸ extP K 𝔭 ^ k) ^ Fintype.card m := by
    rw [Nat.card_fun, ← Nat.card_eq_fintype_card]
  rw [h1, absNorm_extP_pow hK Fact.out h𝔭 k, ← pow_mul]
  congr 1
  ring

theorem card_sub_le (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ)
    (p : (m → 𝓞 K ⧸ extP K 𝔭 ^ k) → Prop) :
    Nat.card {x // p x} ≤ Ideal.absNorm 𝔭 ^ (k * (2 * Fintype.card m)) := by
  haveI := finite_vec (m := m) (K := K) h𝔭 k
  rw [← card_vec hK h𝔭 k]
  exact Finite.card_subtype_le p

theorem two_le_absNorm {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : 2 ≤ Ideal.absNorm 𝔭 := by
  have h5 : Ideal.absNorm 𝔭 ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact idealPowerSpanBounds.ne_bot h𝔭
  have h6 : Ideal.absNorm 𝔭 ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact h𝔭.ne_top
  omega

theorem nkQ_le (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    {H : Matrix m m (𝓞 K)} (hH : Hᴴ = H) (n : 𝓞 F) (c : ℕ) (hm : 1 ≤ Fintype.card m) (k : ℕ) :
    nkQ 𝔭 k c H n ≤ Ideal.absNorm 𝔭 ^ (2 * c + 1) * Ideal.absNorm 𝔭 ^ (k * (2 * Fintype.card m - 1)) := by
  have hq := absNorm_pos h𝔭
  have small : ∀ k, k ≤ 2 * c + 1 → nkQ 𝔭 k c H n ≤
      Ideal.absNorm 𝔭 ^ (2 * c + 1) * Ideal.absNorm 𝔭 ^ (k * (2 * Fintype.card m - 1)) := by
    intro k hk
    refine (card_sub_le hK h𝔭 k _).trans ?_
    rw [← pow_add]
    apply Nat.pow_le_pow_right hq
    have : k * (2 * Fintype.card m) = k + k * (2 * Fintype.card m - 1) := by
      obtain ⟨M, hM⟩ : ∃ M, Fintype.card m = M + 1 := ⟨Fintype.card m - 1, by omega⟩
      rw [hM]
      have : 2 * (M + 1) - 1 = 2 * M + 1 := by omega
      rw [this]; ring
    omega
  rcases le_total k (2 * c + 1) with hk | hk
  · exact small k hk
  · induction k, hk using Nat.le_induction with
    | base => exact small _ le_rfl
    | succ k hk ih =>
      have h1 := nkQ_succ hK h𝔭 hH n hk
      apply Nat.le_of_mul_le_mul_right _ hq
      rw [h1]
      calc Ideal.absNorm 𝔭 ^ (2 * Fintype.card m) * nkQ 𝔭 k c H n
          ≤ Ideal.absNorm 𝔭 ^ (2 * Fintype.card m) * (Ideal.absNorm 𝔭 ^ (2 * c + 1) *
            Ideal.absNorm 𝔭 ^ (k * (2 * Fintype.card m - 1))) := Nat.mul_le_mul_left _ ih
        _ = _ := by
          obtain ⟨M, hM⟩ : ∃ M, Fintype.card m = M + 1 := ⟨Fintype.card m - 1, by omega⟩
          rw [hM]
          have : 2 * (M + 1) - 1 = 2 * M + 1 := by omega
          rw [this]
          ring

def nkB (𝔭 : Ideal (𝓞 F)) (k c : ℕ) (H : Matrix m m (𝓞 K)) (n : 𝓞 F) : ℕ :=
  Nat.card {x : m → 𝓞 K ⧸ extP K 𝔭 ^ k // ¬ Qc 𝔭 k c H x ∧
    fm (H.map (mkk K 𝔭 k)) x x = mkk K 𝔭 k (ι n)}

theorem nkM_eq_add {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k c : ℕ) (H : Matrix m m (𝓞 K)) (n : 𝓞 F) :
    nkM 𝔭 k H n = nkQ 𝔭 k c H n + nkB 𝔭 k c H n := by
  classical
  haveI := finite_vec (m := m) (K := K) h𝔭 k
  unfold nkM nkQ nkB
  have e1 : Nat.card {x : m → 𝓞 K ⧸ extP K 𝔭 ^ k // Qc 𝔭 k c H x ∧
      fm (H.map (mkk K 𝔭 k)) x x = mkk K 𝔭 k (ι n)} =
      Nat.card {y : {x : m → 𝓞 K ⧸ extP K 𝔭 ^ k //
        fm (H.map (mkk K 𝔭 k)) x x = mkk K 𝔭 k (ι n)} // Qc 𝔭 k c H y.1} :=
    Nat.card_congr ((Equiv.subtypeEquivRight (fun x => and_comm)).trans
      (Equiv.subtypeSubtypeEquivSubtypeInter _ _).symm)
  have e2 : Nat.card {x : m → 𝓞 K ⧸ extP K 𝔭 ^ k // ¬ Qc 𝔭 k c H x ∧
      fm (H.map (mkk K 𝔭 k)) x x = mkk K 𝔭 k (ι n)} =
      Nat.card {y : {x : m → 𝓞 K ⧸ extP K 𝔭 ^ k //
        fm (H.map (mkk K 𝔭 k)) x x = mkk K 𝔭 k (ι n)} // ¬ Qc 𝔭 k c H y.1} :=
    Nat.card_congr ((Equiv.subtypeEquivRight (fun x => and_comm)).trans
      (Equiv.subtypeSubtypeEquivSubtypeInter _ _).symm)
  rw [e1, e2, ← Nat.card_sum]
  exact Nat.card_congr (Equiv.sumCompl _).symm

theorem card_preimage_piQ (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ)
    (T : (m → 𝓞 K ⧸ extP K 𝔭 ^ k) → Prop) :
    Nat.card {x : m → 𝓞 K ⧸ extP K 𝔭 ^ (k + 1) // T (fun i => piQ K 𝔭 k (x i))} =
      Ideal.absNorm 𝔭 ^ (2 * Fintype.card m) * Nat.card {x // T x} := by
  classical
  haveI := finite_quot (K := K) h𝔭 k
  haveI := finite_quot (K := K) h𝔭 (k + 1)
  haveI : Fintype (𝓞 K ⧸ extP K 𝔭 ^ k) := Fintype.ofFinite _
  haveI : Fintype (𝓞 K ⧸ extP K 𝔭 ^ (k + 1)) := Fintype.ofFinite _
  have hF : IsFixF K F := Fact.out
  have hz : ∀ w : 𝓞 K ⧸ extP K 𝔭 ^ k, Nat.card {z // piQ K 𝔭 k z = w} = Ideal.absNorm 𝔭 ^ 2 := by
    intro w
    obtain ⟨z0, hz0⟩ := piQ_surjective (K := K) 𝔭 k w
    rw [← card_ker_piQ hK hF h𝔭 k]
    exact Nat.card_congr
      { toFun := fun z => ⟨z.1 - z0, by rw [RingHom.mem_ker, map_sub, z.2, hz0, sub_self]⟩
        invFun := fun q => ⟨q.1 + z0, by rw [map_add, RingHom.mem_ker.mp q.2, hz0, zero_add]⟩
        left_inv := fun z => Subtype.ext (sub_add_cancel _ _)
        right_inv := fun q => Subtype.ext (add_sub_cancel_right _ _) }
  have hfib : ∀ y : m → 𝓞 K ⧸ extP K 𝔭 ^ k,
      Nat.card {x : m → 𝓞 K ⧸ extP K 𝔭 ^ (k + 1) // (fun i => piQ K 𝔭 k (x i)) = y} =
        Ideal.absNorm 𝔭 ^ (2 * Fintype.card m) := by
    intro y
    have e : {x : m → 𝓞 K ⧸ extP K 𝔭 ^ (k + 1) // (fun i => piQ K 𝔭 k (x i)) = y} ≃
        ((i : m) → {z // piQ K 𝔭 k z = y i}) :=
      (Equiv.subtypeEquivRight (fun x => funext_iff)).trans
        (Equiv.subtypePiEquivPi (p := fun i z => piQ K 𝔭 k z = y i))
    rw [Nat.card_congr e, Nat.card_pi]
    simp only [hz, Finset.prod_const, Finset.card_univ]
    rw [← pow_mul]
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype,
    Fintype.card_subtype]
  rw [Finset.card_eq_sum_card_fiberwise (f := fun x => fun i => piQ K 𝔭 k (x i))
    (t := Finset.univ.filter T) ?_]
  · rw [Finset.sum_congr rfl (g := fun _ => Ideal.absNorm 𝔭 ^ (2 * Fintype.card m)) ?_,
      Finset.sum_const, smul_eq_mul, mul_comm]
    intro b hb
    rw [Finset.mem_filter] at hb
    rw [← hfib b, Nat.card_eq_fintype_card, Fintype.card_subtype]
    apply congrArg Finset.card
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨h ▸ hb.2, h⟩
  · intro x hx
    simpa using hx

theorem fm_smul (hF : IsFixF K F) (H : Matrix m m (𝓞 K)) (a : 𝓞 F) (y : m → 𝓞 K) :
    fm H (fun i => ι a * y i) (fun i => ι a * y i) = ι (a * a) * fm H y y := by
  have hs : ∀ i, star (ι a * y i) = ι a * star (y i) := fun i => by
    rw [star_mul', idealPowerSpanBounds.star_def (ι a), conjO_map hF]
  simp only [fm, dotProduct, Matrix.mulVec, Pi.star_apply, hs, map_mul, Finset.mul_sum,
    Finset.sum_mul]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  ring

theorem nkB_le (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    {H : Matrix m m (𝓞 K)} (hH : Hᴴ = H) {D : 𝓞 F} (hD : H.det = ι D) {d : ℕ}
    (hDd : D ∉ 𝔭 ^ (d + 1)) (n : 𝓞 F) (k : ℕ) (hdk : d + 1 ≤ k + 2) :
    ∃ n' : 𝓞 F, nkB 𝔭 (k + 2) d H n ≤ Ideal.absNorm 𝔭 ^ (2 * Fintype.card m) * nkM 𝔭 k H n' := by
  have hF : IsFixF K F := Fact.out
  have := h𝔭.isPrime
  obtain ⟨π0, hπ1, hπ2⟩ : ∃ π0 ∈ 𝔭, π0 ∉ 𝔭 ^ (1 + 1) := by
    obtain ⟨x, hx, hx'⟩ := SetLike.exists_of_lt (Ideal.pow_succ_lt_pow (ne_bot h𝔭) 1)
    exact ⟨x, by simpa using hx, hx'⟩
  have hbad : ∀ x : {x : m → 𝓞 K ⧸ extP K 𝔭 ^ (k + 2) // ¬ Qc 𝔭 (k + 2) d H x ∧
      fm (H.map (mkk K 𝔭 (k + 2))) x x = mkk K 𝔭 (k + 2) (ι n)},
      ∃ y : m → 𝓞 K, (fun i => mkk K 𝔭 (k + 2) (ι π0 * y i)) = x.1 := by
    intro x
    obtain ⟨x0, hx0⟩ := exists_liftv 𝔭 _ x.1
    have h1 := x.2.1
    rw [← hx0, Qc_mk hdk] at h1
    push Not at h1
    have h2 : ∀ i, x0 i ∈ extP K 𝔭 ^ 1 := by
      intro i
      have h3 := vecMul_mem h1 H.adjugate i
      rw [vecMul_adjugate, hD] at h3
      have h4 : star (x0 i) ∈ extP K 𝔭 ^ 1 := mem_of_mul_mem h𝔭 hDd h3
      have h5 := conjO_mem_pow hF 𝔭 1 _ h4
      rwa [← star_def, star_star] at h5
    have h3 : ∀ i, ∃ y, x0 i - ι π0 * y ∈ extP K 𝔭 ^ (k + 2) := by
      intro i
      obtain ⟨a, ha, b, hb, e⟩ := Submodule.mem_sup.1 (map_pow_le_span_sup h𝔭 hπ2 (k + 2) (h2 i))
      obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 ha
      refine ⟨y, ?_⟩
      have : x0 i - ι π0 * y = b := by rw [← e]; ring
      rw [this]; exact hb
    choose y hy using h3
    exact ⟨y, by rw [← hx0]; funext i; exact (Ideal.Quotient.eq.2 (hy i)).symm⟩
  choose Y hY using hbad
  have hval : ∀ y : m → 𝓞 K, ∃ a : 𝓞 F, ι a = fm H y y := fun y =>
    (conjO_eq_iff_mem_range hF _).1 (by rw [← star_def, ← fm_star hH])
  have hsol : ∀ x, ι (π0 * π0) * fm H (Y x) (Y x) - ι n ∈ extP K 𝔭 ^ (k + 2) := by
    intro x
    have h1 := x.2.2
    rw [← hY x, mk_fm, fm_smul hF] at h1
    exact Ideal.Quotient.eq.1 h1
  by_cases hne : Nonempty {x : m → 𝓞 K ⧸ extP K 𝔭 ^ (k + 2) // ¬ Qc 𝔭 (k + 2) d H x ∧
      fm (H.map (mkk K 𝔭 (k + 2))) x x = mkk K 𝔭 (k + 2) (ι n)}
  · obtain ⟨x₀⟩ := hne
    obtain ⟨n', hn'⟩ := hval (Y x₀)
    refine ⟨n', ?_⟩
    unfold nkM nkB
    rw [← card_preimage_piQ hK h𝔭 k (fun z => fm (H.map (mkk K 𝔭 k)) z z = mkk K 𝔭 k (ι n'))]
    have := finite_vec (K := K) (m := m) h𝔭 (k + 1)
    refine Nat.card_le_card_of_injective (fun x => ⟨fun i => mkk K 𝔭 (k + 1) (Y x i), ?_⟩) ?_
    · show fm (H.map (mkk K 𝔭 k)) (fun i => mkk K 𝔭 k (Y x i)) (fun i => mkk K 𝔭 k (Y x i)) = _
      rw [mk_fm]
      apply Ideal.Quotient.eq.2
      have hπ : π0 * π0 ∉ 𝔭 ^ (1 + 1 + 1) := mul_notMem h𝔭.isPrime (ne_bot h𝔭) hπ2 hπ2
      apply mem_of_mul_mem h𝔭 hπ
      have : ι (π0 * π0) * (fm H (Y x) (Y x) - ι n') = (ι (π0 * π0) * fm H (Y x) (Y x) - ι n) -
          (ι (π0 * π0) * fm H (Y x₀) (Y x₀) - ι n) := by rw [hn']; ring
      rw [this, show 1 + 1 + k = k + 2 by ring]
      exact sub_mem (hsol x) (hsol x₀)
    · intro x x' hxx
      apply Subtype.ext
      rw [← hY x, ← hY x']
      funext i
      apply Ideal.Quotient.eq.2
      have h1 : Y x i - Y x' i ∈ extP K 𝔭 ^ (k + 1) :=
        Ideal.Quotient.eq.1 (congrFun (congrArg Subtype.val hxx) i)
      have h2 : ι π0 ∈ extP K 𝔭 := Ideal.mem_map_of_mem _ hπ1
      rw [← mul_sub, pow_succ', ]
      exact Ideal.mul_mem_mul h2 h1
  · refine ⟨0, ?_⟩
    unfold nkB
    rw [not_nonempty_iff] at hne
    rw [Nat.card_of_isEmpty]
    exact Nat.zero_le _

theorem nkM_le (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    {H : Matrix m m (𝓞 K)} (hH : Hᴴ = H) {D : 𝓞 F} (hD : H.det = ι D) {d : ℕ}
    (hDd : D ∉ 𝔭 ^ (d + 1)) (hm : 2 ≤ Fintype.card m) (k : ℕ) : ∀ n : 𝓞 F,
    nkM 𝔭 k H n ≤ 2 * Ideal.absNorm 𝔭 ^ (2 * d + 1) *
      Ideal.absNorm 𝔭 ^ (k * (2 * Fintype.card m - 1)) := by
  have hq := absNorm_pos h𝔭
  have hq2 := two_le_absNorm h𝔭
  obtain ⟨M, hM⟩ : ∃ M, Fintype.card m = M + 2 := ⟨Fintype.card m - 2, by omega⟩
  have hM' : 2 * (M + 2) - 1 = 2 * M + 3 := by omega
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro n
    rcases le_or_gt k (2 * d + 1) with hk | hk
    · refine (card_sub_le hK h𝔭 k _).trans ?_
      rw [hM, hM', mul_assoc, ← pow_add]
      refine le_trans ?_ (Nat.le_mul_of_pos_left _ (by norm_num))
      apply Nat.pow_le_pow_right hq
      have : k * (2 * (M + 2)) = k + k * (2 * M + 3) := by ring
      omega
    · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
      obtain ⟨n', hn'⟩ := nkB_le hK h𝔭 hH hD hDd n k' (by omega)
      have h1 := nkQ_le hK h𝔭 hH n d (by omega) (k' + 2)
      have h2 := ih k' (by omega) n'
      rw [nkM_eq_add h𝔭 (k' + 2) d H n]
      rw [hM, hM'] at *
      have h3 : nkB 𝔭 (k' + 2) d H n ≤ Ideal.absNorm 𝔭 ^ (2 * d + 1) *
          Ideal.absNorm 𝔭 ^ ((k' + 2) * (2 * M + 3)) := by
        refine hn'.trans ((Nat.mul_le_mul_left _ h2).trans ?_)
        have e1 : Ideal.absNorm 𝔭 ^ ((k' + 2) * (2 * M + 3)) = Ideal.absNorm 𝔭 ^ (2 * (M + 2)) *
            Ideal.absNorm 𝔭 * Ideal.absNorm 𝔭 ^ (2 * M + 1) * Ideal.absNorm 𝔭 ^ (k' * (2 * M + 3)) := by
          rw [← pow_succ, ← pow_add, ← pow_add]
          congr 1
          ring
        rw [e1]
        have h4 : 1 ≤ Ideal.absNorm 𝔭 ^ (2 * M + 1) := Nat.one_le_pow _ _ hq
        calc Ideal.absNorm 𝔭 ^ (2 * (M + 2)) * (2 * Ideal.absNorm 𝔭 ^ (2 * d + 1) *
              Ideal.absNorm 𝔭 ^ (k' * (2 * M + 3)))
            = Ideal.absNorm 𝔭 ^ (2 * d + 1) * (Ideal.absNorm 𝔭 ^ (2 * (M + 2)) * 2 * 1 *
              Ideal.absNorm 𝔭 ^ (k' * (2 * M + 3))) := by ring
          _ ≤ _ := by gcongr
      calc nkQ 𝔭 (k' + 2) d H n + nkB 𝔭 (k' + 2) d H n ≤ _ := Nat.add_le_add h1 h3
        _ = _ := by ring

end Formalism.HermitianLattices.Ext.L3.vectorCountBounds
end
end

section
open NumberField Module Matrix Filter Topology

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.firstFamilyOperatorEnd

open HermitianSublattices LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans traceDeterminantCongruences reductionMapsOfForms localValuationFiltration hermitianFormColumns vectorCountBounds

theorem limUnder_of_step {u : ℕ → ℕ} {q e k₀ : ℕ} (hq : 0 < q)
    (h : ∀ k, k₀ ≤ k → u (k + 1) = q ^ e * u k) {k : ℕ} (hk : k₀ ≤ k) :
    limUnder atTop (fun k : ℕ => (u k : ℝ) / (q : ℝ) ^ (k * e)) = (u k : ℝ) / (q : ℝ) ^ (k * e) := by
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hstep : ∀ j, k₀ ≤ j → (u (j + 1) : ℝ) / (q : ℝ) ^ ((j + 1) * e) =
      (u j : ℝ) / (q : ℝ) ^ (j * e) := by
    intro j hj
    rw [h j hj, Nat.cast_mul, Nat.cast_pow, div_eq_div_iff (pow_ne_zero _ hq') (pow_ne_zero _ hq'),
      add_mul, one_mul, pow_add]
    ring
  have hconst : ∀ j, k₀ ≤ j → (u j : ℝ) / (q : ℝ) ^ (j * e) = (u k₀ : ℝ) / (q : ℝ) ^ (k₀ * e) := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => rfl
    | succ j hj ih => rw [hstep j hj, ih]
  have ht : Tendsto (fun k : ℕ => (u k : ℝ) / (q : ℝ) ^ (k * e)) atTop
      (𝓝 ((u k : ℝ) / (q : ℝ) ^ (k * e))) := by
    rw [hconst k hk]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop k₀] with j hj
    exact (hconst j hj).symm
  exact ht.limUnder_eq

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)

theorem nkCount_succ_fine (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} {v : ℕ} (hn : n ∉ 𝔭 ^ (v + 1)) {k : ℕ}
    (hk : vd h L 𝔭 + v + 1 ≤ k) :
    nkCount h L 𝔭 (k + 1) n = Ideal.absNorm 𝔭 ^ (2 * finrank K V - 1) * nkCount h L 𝔭 k n := by
  haveI : Fact (IsFixF K F) := ⟨hF⟩
  obtain ⟨b, H, D, hb, hH, hHh, hD, hD0, hv⟩ := exists_local_data hF hs hd hL hLi h𝔭
  rw [nkCount_eq h h𝔭 b hb hH, nkCount_eq h h𝔭 b hb hH]
  change nkM 𝔭 (k + 1) H n = _ * nkM 𝔭 k H n
  rw [hv] at hk
  have key := nkM_succ hK h𝔭 hHh hD (notMem_pow_vF h𝔭 hD0) hn hk
  rw [Fintype.card_fin] at key
  have hN := absNorm_pos h𝔭
  rcases Nat.eq_zero_or_pos (finrank K V) with h0 | hpos
  · have e0 : 2 * finrank K V = 0 := by omega
    have e1 : 2 * finrank K V - 1 = 0 := by omega
    rw [e0, pow_zero, one_mul] at key
    rw [e1, pow_zero, one_mul]
    have h2 := two_le_absNorm h𝔭
    have hB : nkM 𝔭 k H n ≤ 1 :=
      (card_sub_le hK h𝔭 k _).trans (by rw [Fintype.card_fin, e0, mul_zero, pow_zero])
    have hAN : 2 * nkM 𝔭 (k + 1) H n ≤ nkM 𝔭 (k + 1) H n * Ideal.absNorm 𝔭 := by
      rw [mul_comm]
      exact Nat.mul_le_mul_left _ h2
    have hA0 : nkM 𝔭 (k + 1) H n = 0 := by
      rw [key] at hAN
      omega
    rw [hA0, zero_mul] at key
    omega
  · have e : 2 * finrank K V = (2 * finrank K V - 1) + 1 := by omega
    rw [e, pow_succ] at key
    apply Nat.eq_of_mul_eq_mul_right hN
    rw [key]
    ring

theorem alphaN_eq (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} {v : ℕ} (hn : n ∉ 𝔭 ^ (v + 1)) {k : ℕ}
    (hk : vd h L 𝔭 + v + 1 ≤ k) :
    alphaN h L 𝔭 n =
      (nkCount h L 𝔭 k n : ℝ) / (Ideal.absNorm 𝔭 : ℝ) ^ (k * (2 * finrank K V - 1)) := by
  unfold alphaN
  exact limUnder_of_step (absNorm_pos h𝔭)
    (fun j hj => nkCount_succ_fine hK hF hs hd hL hLi h𝔭 hn hj) hk

theorem nkCount_congr (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {n n' : 𝓞 F} {k : ℕ} (hc : n - n' ∈ 𝔭 ^ k) :
    nkCount h L 𝔭 k n = nkCount h L 𝔭 k n' := by
  haveI : Fact (IsFixF K F) := ⟨hF⟩
  obtain ⟨b, H, D, hb, hH, hHh, hD, hD0, hv⟩ := exists_local_data hF hs hd hL hLi h𝔭
  rw [nkCount_eq h h𝔭 b hb hH, nkCount_eq h h𝔭 b hb hH]
  have e : Ideal.Quotient.mk (extP K 𝔭 ^ k) (ι n) = Ideal.Quotient.mk (extP K 𝔭 ^ k) (ι n') := by
    rw [Ideal.Quotient.eq, ← map_sub]
    exact (mem_pow_iff 𝔭 k _).mpr hc
  rw [e]

theorem akCount_succ_fine (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {k : ℕ} (hk : 2 * vd h L 𝔭 + 1 ≤ k) :
    akCount h L 𝔭 (k + 1) = Ideal.absNorm 𝔭 ^ (finrank K V ^ 2) * akCount h L 𝔭 k := by
  haveI : Fact (IsFixF K F) := ⟨hF⟩
  obtain ⟨b, H, D, hb, hH, hHh, hD, hD0, hv⟩ := exists_local_data hF hs hd hL hLi h𝔭
  rw [akCount_eq h h𝔭 b hb hH, akCount_eq h h𝔭 b hb hH]
  rw [hv] at hk
  have key := akM_succ hK h𝔭 hHh hD (notMem_pow_vF h𝔭 hD0) hk
  rw [Fintype.card_fin, ← sq] at key
  exact key

theorem alphaL_eq (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {k : ℕ} (hk : 2 * vd h L 𝔭 + 1 ≤ k) :
    alphaL h L 𝔭 = (akCount h L 𝔭 k : ℝ) / (Ideal.absNorm 𝔭 : ℝ) ^ (k * finrank K V ^ 2) := by
  unfold alphaL
  exact limUnder_of_step (absNorm_pos h𝔭)
    (fun j hj => akCount_succ_fine hK hF hs hd hL hLi h𝔭 (le_trans hk hj)) le_rfl

theorem akCount_pos (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) (k : ℕ) : 0 < akCount h L 𝔭 k := by
  haveI : Fact (IsFixF K F) := ⟨hF⟩
  obtain ⟨b, H, D, hb, hH, hHh, hD, hD0, hv⟩ := exists_local_data hF hs hd hL hLi h𝔭
  rw [akCount_eq h h𝔭 b hb hH]
  haveI := finite_quot (K := K) h𝔭 k
  haveI : Nonempty {X : Matrix (Fin (finrank K V)) (Fin (finrank K V)) (𝓞 K ⧸ extP K 𝔭 ^ k) //
      Xᴴ * H.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) * X = H.map (Ideal.Quotient.mk (extP K 𝔭 ^ k))} :=
    ⟨⟨1, by rw [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]⟩⟩
  exact Nat.card_pos

theorem nkCount_le_nat (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (hm : 2 ≤ finrank K V)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ) (n : 𝓞 F) :
    nkCount h L 𝔭 k n ≤ 2 * Ideal.absNorm 𝔭 ^ (2 * vd h L 𝔭 + 1) *
      Ideal.absNorm 𝔭 ^ (k * (2 * finrank K V - 1)) := by
  haveI : Fact (IsFixF K F) := ⟨hF⟩
  obtain ⟨b, H, D, hb, hH, hHh, hD, hD0, hv⟩ := exists_local_data hF hs hd hL hLi h𝔭
  rw [nkCount_eq h h𝔭 b hb hH, hv]
  have key := nkM_le hK h𝔭 hHh hD (notMem_pow_vF h𝔭 hD0) (by rw [Fintype.card_fin]; exact hm) k n
  rw [Fintype.card_fin] at key
  exact key

end Formalism.HermitianLattices.Ext.L3.firstFamilyOperatorEnd
end
end

section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem nkCount_locF (hF : IsFixF K F) (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F))
    (h𝔭 : 𝔭.IsMaximal) (k : ℕ) (n : 𝓞 F) : nkCount h (locF 𝔭 L) 𝔭 k n = nkCount h L 𝔭 k n :=
  localizedQuotients.nkCount_locF hF h L 𝔭 h𝔭 k n

theorem akCount_locF (hF : IsFixF K F) (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F))
    (h𝔭 : 𝔭.IsMaximal) (k : ℕ) : akCount h (locF 𝔭 L) 𝔭 k = akCount h L 𝔭 k :=
  localizedQuotients.akCount_locF hF h L 𝔭 h𝔭 k

theorem vd_locF (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : vd h (locF 𝔭 L) 𝔭 = vd h L 𝔭 :=
  localizedQuotients.vd_locF hF h L h𝔭

theorem nkCount_succ (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : n ≠ 0) {k : ℕ}
    (hk : 2 * vd h L 𝔭 + 2 * vF 𝔭 n + 2 ≤ k) :
    nkCount h L 𝔭 (k + 1) n = Ideal.absNorm 𝔭 ^ (2 * finrank K V - 1) * nkCount h L 𝔭 k n :=
  firstFamilyOperatorEnd.nkCount_succ_fine hK hF hs hd hL hLi h𝔭 (localValuationFiltration.notMem_pow_vF h𝔭 hn) (by omega)

theorem alphaN_congr (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {n n' : 𝓞 F} (hn : n ≠ 0)
    {k : ℕ} (hk : vF 𝔭 n + 2 * vd h L 𝔭 + 2 ≤ k) (hc : n - n' ∈ 𝔭 ^ k) :
    alphaN h L 𝔭 n = alphaN h L 𝔭 n' := by
  have hn1 := localValuationFiltration.notMem_pow_vF h𝔭 hn
  have hn1' : n' ∉ 𝔭 ^ (vF 𝔭 n + 1) := by
    intro h'
    apply hn1
    have hk' : 𝔭 ^ k ≤ 𝔭 ^ (vF 𝔭 n + 1) := Ideal.pow_le_pow_right (by omega)
    have := Ideal.add_mem _ (hk' hc) h'
    simpa using this
  rw [firstFamilyOperatorEnd.alphaN_eq hK hF hs hd hL hLi h𝔭 hn1 (k := k) (by omega),
    firstFamilyOperatorEnd.alphaN_eq hK hF hs hd hL hLi h𝔭 hn1' (k := k) (by omega),
    firstFamilyOperatorEnd.nkCount_congr hF hs hd hL hLi h𝔭 hc]

theorem nkCount_le (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (hm : 2 ≤ finrank K V) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    ∃ C : ℝ, ∀ (k : ℕ) (n : 𝓞 F),
      (nkCount h L 𝔭 k n : ℝ) ≤ C * (Ideal.absNorm 𝔭 : ℝ) ^ (k * (2 * finrank K V - 1)) := by
  refine ⟨2 * (Ideal.absNorm 𝔭 : ℝ) ^ (2 * vd h L 𝔭 + 1), fun k n => ?_⟩
  have := firstFamilyOperatorEnd.nkCount_le_nat hK hF hs hd hL hLi hm h𝔭 k n
  exact_mod_cast this

theorem alphaL_pos (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : 0 < alphaL h L 𝔭 := by
  rw [firstFamilyOperatorEnd.alphaL_eq hK hF hs hd hL hLi h𝔭 (k := 2 * vd h L 𝔭 + 1) le_rfl]
  have hN : 0 < Ideal.absNorm 𝔭 := by
    haveI := h𝔭
    exact Nat.pos_of_ne_zero fun h0 =>
      Ideal.IsMaximal.ne_bot_of_isIntegral_int 𝔭 (Ideal.absNorm_eq_zero_iff.mp h0)
  apply div_pos
  · exact_mod_cast firstFamilyOperatorEnd.akCount_pos hF hs hd hL hLi h𝔭 _
  · apply pow_pos
    exact_mod_cast hN

end Formalism.HermitianLattices.Ext.L3
end
end
