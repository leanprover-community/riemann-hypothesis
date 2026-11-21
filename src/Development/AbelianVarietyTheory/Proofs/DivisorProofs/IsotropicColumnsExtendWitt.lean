import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPurelyImaginaryElement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHermNDSmulSkewForm

section
namespace GlobalTheory.TargetSimplification

theorem main {E V : Type} [Field E] [CharZero E] [AddCommGroup V] [Module E V] {s : E →+* E} {r : ℕ}
  (B : V →ₛₗ[s] V →ₗ[E] E) (hB : ∀ u v : V, B u v = s (B v u))
  {x y : Fin r → V} (hx : ∀ i j, B (x i) (x j) = 0) (hy : ∀ i j, B (y i) (y j) = 0)
  (hxy : ∀ i j, B (x i) (y j) = if i = j then 1 else 0)
  {z w₀ : V} (hxz : ∀ i, B (x i) z = 0) (hyz : ∀ i, B (y i) z = 0) (hzz : B z z = 0)
  (hzw : B z w₀ = 1) :
  ∃ (x' y' : Fin (r+1) → V), (∀ i j, B (x' i) (x' j) = 0) ∧ (∀ i j, B (y' i) (y' j) = 0) ∧
    (∀ i j, B (x' i) (y' j) = if i = j then 1 else 0) ∧ ∀ i : Fin r, x' (Fin.castSucc i) = x i := by
  have hyx : ∀ i j, B (y i) (x j) = if i = j then 1 else 0 := by
    intro i j; rw [hB, hxy]; by_cases h : j = i
    · subst h; simp
    · simp [h, Ne.symm h]
  have hzx : ∀ i, B z (x i) = 0 := fun i => by rw [hB, hxz, map_zero]
  have hzy : ∀ i, B z (y i) = 0 := fun i => by rw [hB, hyz, map_zero]
  obtain ⟨w₁, hw₁⟩ : ∃ w₁ : V, w₁ = w₀ - ∑ j, B (y j) w₀ • x j - ∑ j, B (x j) w₀ • y j := ⟨_, rfl⟩
  have hxw₁ : ∀ i, B (x i) w₁ = 0 := by
    intro i; simp [hw₁, map_sub, map_sum, hx, hxy]
  have hyw₁ : ∀ i, B (y i) w₁ = 0 := by
    intro i; simp [hw₁, map_sub, map_sum, hy, hyx]
  have hzw₁ : B z w₁ = 1 := by simp [hw₁, map_sub, map_sum, hzx, hzy, hzw]
  have h1 : B w₁ z = 1 := by rw [hB, hzw₁, map_one]
  have ht : s (B w₁ w₁) = B w₁ w₁ := (hB w₁ w₁).symm
  obtain ⟨c, hc⟩ : ∃ c : E, c = -(B w₁ w₁ / 2) := ⟨_, rfl⟩
  have hsc : s c = c := by rw [hc, map_neg, map_div₀, ht, map_ofNat]
  obtain ⟨w, hw⟩ : ∃ w : V, w = w₁ + c • z := ⟨_, rfl⟩
  have hxw : ∀ i, B (x i) w = 0 := by intro i; simp [hw, hxw₁, hxz]
  have hyw : ∀ i, B (y i) w = 0 := by intro i; simp [hw, hyw₁, hyz]
  have hwy : ∀ i, B w (y i) = 0 := fun i => by rw [hB, hyw, map_zero]
  have hzw' : B z w = 1 := by simp [hw, hzw₁, hzz]
  have hww : B w w = 0 := by
    simp only [hw, map_add, LinearMap.add_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
      smul_eq_mul, hzz, h1, hsc, hzw₁]
    rw [hc]; simp only [RingHom.id_apply]; ring
  refine ⟨Fin.snoc x z, Fin.snoc y w, ?_, ?_, ?_, ?_⟩
  · intro i j
    cases i using Fin.lastCases <;> cases j using Fin.lastCases <;>
      simp [Fin.snoc_castSucc, Fin.snoc_last, hx, hxz, hzx, hzz]
  · intro i j
    cases i using Fin.lastCases <;> cases j using Fin.lastCases <;>
      simp [Fin.snoc_castSucc, Fin.snoc_last, hy, hyw, hwy, hww]
  · intro i j
    cases i using Fin.lastCases <;> cases j using Fin.lastCases <;>
      simp [Fin.snoc_castSucc, Fin.snoc_last, hxy, hxw, hzy, hzw', Fin.castSucc_ne_last, (Fin.castSucc_ne_last _).symm]
  · intro i; simp

end GlobalTheory.TargetSimplification
end

section
noncomputable section

namespace GlobalTheory.AdjugateAppendColumn

open Matrix

section General

variable {E : Type} [Field E] (s : E →+* E)

def adj {a b : Type} (A : Matrix a b E) : Matrix b a E := (A.map s)ᵀ

theorem adj_mul {a b c : Type} [Fintype b] (A : Matrix a b E) (B : Matrix b c E) :
    adj s (A * B) = adj s B * adj s A := by
  simp only [adj, Matrix.map_mul, Matrix.transpose_mul]

theorem adj_one {a : Type} [DecidableEq a] : adj s (1 : Matrix a a E) = 1 := by
  simp only [adj, Matrix.map_one _ (map_zero s) (map_one s), Matrix.transpose_one]

theorem adj_sub {a b : Type} (A B : Matrix a b E) : adj s (A - B) = adj s A - adj s B := by
  ext i j; simp [adj]

theorem adj_smul {a b : Type} (c : E) (A : Matrix a b E) : adj s (c • A) = s c • adj s A := by
  ext i j; simp [adj]

theorem adj_adj (hs : ∀ x, s (s x) = x) {a b : Type} (A : Matrix a b E) : adj s (adj s A) = A := by
  ext i j; simp [adj, hs]

variable {n m : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem exists_left_inv {X : Matrix (Fin n) (Fin m) E} (hX : LinearIndependent E Xᵀ) :
    ∃ L : Matrix (Fin m) (Fin n) E, L * X = 1 := by
  have hi : Function.Injective X.mulVec := Matrix.mulVec_injective_iff.2 hX
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' X) (LinearMap.ker_eq_bot.2 hi)
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have := congrArg LinearMap.toMatrix' hg
  rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] at this

theorem exists_dual [CharZero E] (hs : ∀ x, s (s x) = x) (hJ : adj s J = J) (hd : J.det ≠ 0)
    {X : Matrix (Fin n) (Fin m) E} (hX : LinearIndependent E Xᵀ) (h0 : adj s X * J * X = 0) :
    ∃ Y : Matrix (Fin n) (Fin m) E, adj s X * J * Y = 1 ∧ adj s Y * J * X = 1 ∧ adj s Y * J * Y = 0 := by
  obtain ⟨L, hL⟩ := exists_left_inv hX
  have flip : ∀ Z : Matrix (Fin n) (Fin m) E, adj s X * J * Z = 1 → adj s Z * J * X = 1 := fun Z hZ => by
    have := congrArg (adj s) hZ
    rwa [adj_mul, adj_mul, adj_adj s hs, hJ, adj_one, ← Matrix.mul_assoc] at this
  obtain ⟨Z, hZ⟩ : ∃ Z : Matrix (Fin n) (Fin m) E, adj s X * J * Z = 1 := ⟨J⁻¹ * adj s L, by
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hd.isUnit, ← adj_mul, hL, adj_one]⟩
  obtain ⟨G, hG⟩ : ∃ G, G = adj s Z * J * Z := ⟨_, rfl⟩
  have h1 : adj s X * J * (Z - (2 : E)⁻¹ • (X * G)) = 1 := by
    rw [Matrix.mul_sub, Matrix.mul_smul, ← Matrix.mul_assoc, h0, hZ, Matrix.zero_mul, smul_zero, sub_zero]
  refine ⟨_, h1, flip _ h1, ?_⟩
  have hGG : adj s G = G := by
    rw [hG, adj_mul, adj_mul, adj_adj s hs, hJ, Matrix.mul_assoc]
  rw [Matrix.mul_sub, Matrix.mul_smul, ← Matrix.mul_assoc _ X G, flip _ h1, Matrix.one_mul, adj_sub, adj_smul, adj_mul, hGG,
    Matrix.sub_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_assoc G, Matrix.mul_assoc G, hZ,
    Matrix.mul_one, ← hG, map_inv₀, map_ofNat, sub_sub, ← add_smul, show (2 : E)⁻¹ + 2⁻¹ = 1 by norm_num, one_smul, sub_self]

theorem gram_apply {a b : Type} (A : Matrix (Fin n) a E) (B : Matrix (Fin n) b E) (i : a) (j : b) :
    (adj s A * J * B) i j = (fun k => s (Aᵀ i k)) ⬝ᵥ J *ᵥ (Bᵀ j) := by
  rw [Matrix.mul_assoc, Matrix.mul_apply]; rfl

theorem form_symm (hs : ∀ x, s (s x) = x) (hJ : adj s J = J) (x y : Fin n → E) :
    s ((fun k => s (x k)) ⬝ᵥ J *ᵥ y) = (fun k => s (y k)) ⬝ᵥ J *ᵥ x := by
  have e : ∀ i j, s (J j i) = J i j := fun i j => congrFun (congrFun hJ i) j
  simp only [dotProduct, Matrix.mulVec, map_sum, map_mul, hs, e, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

def app (X : Matrix (Fin n) (Fin m) E) (z : Fin n → E) : Matrix (Fin n) (Fin (m + 1)) E :=
  (Matrix.of (Fin.snoc (α := fun _ => Fin n → E) Xᵀ z))ᵀ

theorem app_transpose (X : Matrix (Fin n) (Fin m) E) (z : Fin n → E) :
    (app X z)ᵀ = Fin.snoc (α := fun _ => Fin n → E) Xᵀ z := rfl

theorem app_last (X : Matrix (Fin n) (Fin m) E) (z : Fin n → E) : (app X z)ᵀ (Fin.last m) = z :=
  Fin.snoc_last (α := fun _ => Fin n → E) z Xᵀ

theorem app_cast (X : Matrix (Fin n) (Fin m) E) (z : Fin n → E) (i : Fin m) : (app X z)ᵀ i.castSucc = Xᵀ i :=
  Fin.snoc_castSucc (α := fun _ => Fin n → E) z Xᵀ i

theorem exists_ext [CharZero E] (hs : ∀ x, s (s x) = x) (hJ : adj s J = J) (hd : J.det ≠ 0) (k : ℕ) :
    ∀ (m : ℕ) (C : Matrix (Fin n) (Fin m) E), n ≤ m + k → LinearIndependent E Cᵀ → adj s C * J * C = 0 →
      ∃ (m' : ℕ) (hm : m ≤ m') (X Y : Matrix (Fin n) (Fin m') E), adj s X * J * X = 0 ∧ adj s Y * J * Y = 0 ∧
        adj s X * J * Y = 1 ∧ (∀ z : Fin n → E, (adj s X * J) *ᵥ z = 0 → (adj s Y * J) *ᵥ z = 0 →
          (fun k => s (z k)) ⬝ᵥ J *ᵥ z = 0 → z = 0) ∧ X.submatrix id (Fin.castLE hm) = C := by
  have step : ∀ (m : ℕ) (C Y : Matrix (Fin n) (Fin m) E) (z : Fin n → E), LinearIndependent E Cᵀ → adj s C * J * C = 0 →
      adj s Y * J * C = 1 → (adj s C * J) *ᵥ z = 0 → (adj s Y * J) *ᵥ z = 0 → (fun k => s (z k)) ⬝ᵥ J *ᵥ z = 0 → z ≠ 0 →
      LinearIndependent E (app C z)ᵀ ∧ adj s (app C z) * J * app C z = 0 := by
    intro m C Y z hC h0 h1 a b c hz
    constructor
    · rw [app_transpose]
      refine linearIndependent_finSnoc.2 ⟨hC, fun hm => hz ?_⟩
      obtain ⟨u, hu⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hm
      have e : C *ᵥ u = z := by
        rw [← hu]; funext i; simp [Matrix.mulVec, dotProduct, mul_comm]
      rw [← e, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec] at b
      rw [← e, b, Matrix.mulVec_zero]
    · have a' : ∀ i, (fun k => s (Cᵀ i k)) ⬝ᵥ J *ᵥ z = 0 := fun i => by
        have := congrFun a i
        rw [← Matrix.mulVec_mulVec] at this
        exact this
      ext i j
      rw [gram_apply, Matrix.zero_apply]
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => rw [app_last]; exact c
        | cast j =>
          rw [app_last, app_cast, ← form_symm s hs hJ, a', map_zero]
      | cast i =>
        induction j using Fin.lastCases with
        | last => rw [app_last, app_cast]; exact a' i
        | cast j =>
          rw [app_cast, app_cast, ← gram_apply, h0, Matrix.zero_apply]
  induction k with
  | zero =>
    intro m C hm hC h0
    obtain ⟨Y, h1, h2, h3⟩ := exists_dual s hs hJ hd hC h0
    refine ⟨m, le_rfl, C, Y, h0, h3, h1, fun z a b c => ?_, rfl⟩
    by_contra hz
    have := (step m C Y z hC h0 h2 a b c hz).1.fintype_card_le_finrank
    simp at this
    omega
  | succ k ih =>
    intro m C hm hC h0
    obtain ⟨Y, h1, h2, h3⟩ := exists_dual s hs hJ hd hC h0
    by_cases H : ∀ z : Fin n → E, (adj s C * J) *ᵥ z = 0 → (adj s Y * J) *ᵥ z = 0 →
      (fun k => s (z k)) ⬝ᵥ J *ᵥ z = 0 → z = 0
    · exact ⟨m, le_rfl, C, Y, h0, h3, h1, H, rfl⟩
    push Not at H
    obtain ⟨z, a, b, c, hz⟩ := H
    obtain ⟨p, q⟩ := step m C Y z hC h0 h2 a b c hz
    obtain ⟨m', hm', X, Y', x1, x2, x3, x4, x5⟩ := ih (m + 1) (app C z) (by omega) p q
    refine ⟨m', by omega, X, Y', x1, x2, x3, x4, ?_⟩
    ext i j
    have := congrFun (congrFun x5 i) j.castSucc
    have e : app C z i j.castSucc = C i j := congrFun (app_cast C z j) i
    exact this.trans e

end General

theorem exists_wittFrame_initCols (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ) (n : ℕ) (J : Matrix (Fin n) (Fin n) E)
    (hJ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsHermND σ J) (r : ℕ) (C : Matrix (Fin n) (Fin (r + 1)) E)
    (hC : LinearIndependent E (Matrix.transpose C)) (h0 : Formalism.UG.cT (σ : E →+* E) C * J * C = 0) :
    ∃ (m : ℕ) (hm : r < m) (X : Matrix (Fin n) (Fin m) E) (Y : Matrix (Fin n) (Fin m) E),
      GlobalTheory.SiegelSet.IsWittFrame σ J X Y ∧ GlobalTheory.StdPar.initCols X (⟨r, hm⟩ : Fin m) = C := by
  have hs : ∀ x, (σ : E →+* E) ((σ : E →+* E) x) = x := fun x => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    have := h.2.2.2 τ
    simp only [RingHom.coe_coe]
    rw [this, this, star_star]
  obtain ⟨m, hm, X, Y, x1, x2, x3, x4, x5⟩ := exists_ext (σ : E →+* E) (J := J) hs (Matrix.ext fun i j => hJ.1 i j) hJ.2
    n (r + 1) C (by omega) hC h0
  refine ⟨m, hm, X, Y, ⟨x1, x2, x3, fun z a b c => x4 z a b ?_⟩, x5⟩
  simp only [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE, Formalism.UG.hform] at c
  simpa only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc] using c

end GlobalTheory.AdjugateAppendColumn

end
end

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
noncomputable section

namespace GlobalTheory.WittExt

open Matrix
open Formalism.UG (cT)

theorem exists_isWittFrame_initCols : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (C : Matrix (Fin n) (Fin (r + 1)) E),
      LinearIndependent E C.transpose → Formalism.UG.cT (σ : E →+* E) C * J * C = 0 →
        ∃ (m : ℕ) (hm : r < m) (X Y : Matrix (Fin n) (Fin m) E), IsWittFrame σ J X Y ∧ GlobalTheory.StdPar.initCols X ⟨r, hm⟩ = C := by
  first
  | exact @_root_.GlobalTheory.AdjugateAppendColumn.exists_wittFrame_initCols
  | exact _root_.GlobalTheory.AdjugateAppendColumn.exists_wittFrame_initCols
  | (apply _root_.GlobalTheory.AdjugateAppendColumn.exists_wittFrame_initCols <;> assumption)
  | (intros; apply _root_.GlobalTheory.AdjugateAppendColumn.exists_wittFrame_initCols <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AdjugateAppendColumn.exists_wittFrame_initCols <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AdjugateAppendColumn.exists_wittFrame_initCols ..)

end GlobalTheory.WittExt
end
end
