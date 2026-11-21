import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExponentialChartAtPointStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousOnFrameDirectionsInverse
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HorizontalCoordinateLatticeIsometryDetOneStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConstantPeriodMarkingUniversalCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodLinearAlgebraHodgeSequenceExactStatement

section
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology

namespace GlobalTheory.ShFam.Hor.PolyBd

section Gen

variable {P : Type} {A : P → ℝ}

def PB (A : P → ℝ) (f : P → ℂ) : Prop := ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ p, ‖f p‖ ≤ C * A p ^ k

theorem PB.const (a : ℂ) : PB A fun _ => a := ⟨‖a‖, 0, norm_nonneg _, fun _ => by simp⟩

theorem PB.of_le {f : P → ℂ} (h : ∀ p, ‖f p‖ ≤ A p) : PB A f := ⟨1, 1, zero_le_one, fun p => by simpa using h p⟩

theorem PB.mul {f g : P → ℂ} (hf : PB A f) (hg : PB A g) : PB A fun p => f p * g p := by
  obtain ⟨C, k, hC, h⟩ := hf
  obtain ⟨D, n, hD, h'⟩ := hg
  refine ⟨C * D, k + n, mul_nonneg hC hD, fun p => ?_⟩
  rw [norm_mul, pow_add]
  calc _ ≤ (C * A p ^ k) * (D * A p ^ n) :=
        mul_le_mul (h p) (h' p) (norm_nonneg _) ((norm_nonneg _).trans (h p))
    _ = _ := by ring

theorem PB.both (hA : ∀ p, 1 ≤ A p) {f g : P → ℂ} (hf : PB A f) (hg : PB A g) :
    ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ p, ‖f p‖ ≤ C * A p ^ k ∧ ‖g p‖ ≤ C * A p ^ k := by
  obtain ⟨C, k, hC, h⟩ := hf
  obtain ⟨D, n, hD, h'⟩ := hg
  refine ⟨max C D, max k n, le_max_of_le_left hC, fun p => ⟨(h p).trans ?_, (h' p).trans ?_⟩⟩
  · exact mul_le_mul (le_max_left _ _) (pow_le_pow_right₀ (hA p) (le_max_left _ _))
      (pow_nonneg (zero_le_one.trans (hA p)) _) (le_max_of_le_left hC)
  · exact mul_le_mul (le_max_right _ _) (pow_le_pow_right₀ (hA p) (le_max_right _ _))
      (pow_nonneg (zero_le_one.trans (hA p)) _) (le_max_of_le_left hC)

theorem PB.add (hA : ∀ p, 1 ≤ A p) {f g : P → ℂ} (hf : PB A f) (hg : PB A g) : PB A fun p => f p + g p := by
  obtain ⟨C, k, hC, h⟩ := hf.both hA hg
  refine ⟨2 * C, k, by positivity, fun p => (norm_add_le _ _).trans ?_⟩
  linarith [(h p).1, (h p).2]

theorem PB.sum (hA : ∀ p, 1 ≤ A p) {I : Type} (s : Finset I) {f : I → P → ℂ} (hf : ∀ i, PB A (f i)) :
    PB A fun p => ∑ i ∈ s, f i p := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using PB.const (A := A) 0
  | insert a s ha ih => simpa [Finset.sum_insert ha] using (hf a).add hA ih

theorem PB.prod {I : Type} (s : Finset I) {f : I → P → ℂ} (hf : ∀ i, PB A (f i)) :
    PB A fun p => ∏ i ∈ s, f i p := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using PB.const (A := A) 1
  | insert a s ha ih => simpa [Finset.prod_insert ha] using (hf a).mul ih

theorem PB.det (hA : ∀ p, 1 ≤ A p) {I : Type} [Fintype I] [DecidableEq I] {M : P → Matrix I I ℂ}
    (hM : ∀ i j, PB A fun p => M p i j) : PB A fun p => (M p).det := by
  simp only [Matrix.det_apply']
  exact PB.sum hA _ fun s => (PB.const _).mul (PB.prod _ fun i => hM _ _)

theorem PB.matMul (hA : ∀ p, 1 ≤ A p) {a b d : Type} [Fintype b] {M : P → Matrix a b ℂ} {N : P → Matrix b d ℂ}
    (hM : ∀ i j, PB A fun p => M p i j) (hN : ∀ i j, PB A fun p => N p i j) (i : a) (j : d) :
    PB A fun p => (M p * N p) i j := by
  simp only [Matrix.mul_apply]
  exact PB.sum hA _ fun k => (hM _ _).mul (hN _ _)

theorem horVal_bound (hA : ∀ p, 1 ≤ A p) {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    {K : P → Matrix (m ⊕ n) m ℂ} {C : P → Matrix n (m ⊕ n) ℂ} {R : P → Matrix m (m ⊕ n) ℂ}
    {S : P → Matrix (m ⊕ n) n ℂ} (h : ∀ p, C p * K p = 0) (hR : ∀ p, R p * K p = 1) (hS : ∀ p, C p * S p = 1)
    (bK : ∀ i j, PB A fun p => K p i j) (bC : ∀ i j, PB A fun p => C p i j) (bR : ∀ i j, PB A fun p => R p i j)
    (bS : ∀ i j, PB A fun p => S p i j) :
    ∃ (D : ℝ) (k : ℕ), 0 ≤ D ∧ ∀ p, ‖horVal (K p) (C p)‖ ≤ D * A p ^ k ∧ ‖(horVal (K p) (C p))⁻¹‖ ≤ D * A p ^ k := by
  have h1 : PB A fun p => horVal (K p) (C p) := by
    simp only [fun p => horVal_eq (h p) (hR p) (hS p)]
    refine PB.det hA fun i j => ?_
    rcases i with i | i
    · simpa using bR i j
    · simpa using bC i j
  have h2 : PB A fun p => (horVal (K p) (C p))⁻¹ := by
    simp only [fun p => inv_eq_of_mul_eq_one_right (horVal_mul (h p) (hR p) (hS p))]
    refine PB.det hA fun i j => ?_
    rcases j with j | j
    · simpa using bK i j
    · simpa using bS i j
  exact h1.both hA h2

end Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Di : Datum H}

theorem exists_comb {J : Type} [Fintype J] (x : J → Di.La) (f : (E →+* ℂ) → (E →+* ℂ)) (v : Di.La)
    (hv : ∃ n : ℕ, n ≠ 0 ∧ n • v ∈ Submodule.span (𝓞 E) (Set.range x)) :
    ∃ B : (E →+* ℂ) → J → ℂ, ∀ Q : Di.La →+ (Letter Dw → ℂ),
      (∀ (a : 𝓞 E) v (z : Letter Dw), Q (a • v) z = f z.1 (a : E) * Q v z) →
      ∀ z : Letter Dw, Q v z = ∑ k, B z.1 k * Q (x k) z := by
  obtain ⟨n, hn, hv⟩ := hv
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hv
  refine ⟨fun t k => (n : ℂ)⁻¹ * f t (a k : E), fun Q hQ z => ?_⟩
  have h := congrArg (fun w => Q w z) ha
  simp only [map_sum, Finset.sum_apply, hQ, map_nsmul, Pi.smul_apply, nsmul_eq_mul] at h
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
  simp only [_root_.mul_assoc]
  rw [← Finset.mul_sum, h, inv_mul_cancel_left₀ hn']

theorem perVal_bound (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (c : Coeff l) (σ : c.F →+* ℂ) (Di : Datum H) (τ : E →+* ℂ) (x : Idx Dw τ → Di.La)
    (hm : Matrix (Idx Dw τ) (Idx Dw τ) E) (g r : ℕ) (T₀ : Di.La ≃+ (Fin r → ℤ)) (ρ : Fin g → Fin r → ℂ)
    (hx : IsPerBasis Di x hm) : ∃ (C : ℝ) (k : ℕ), ∀ (Q : Di.La →+ (Letter Dw → ℂ))
      (W : Matrix (Letter Dw) (Fin g) ℂ) (Wi : Matrix (Fin g) (Letter Dw) ℂ) (lam : Fin r → Fin g → ℂ) (A : ℝ),
      GoodPer c σ τ x hm Q → W * Wi = 1 → Wi * W = 1 → (∀ v, ∑ z, Q v z • W z = ∑ m, T₀ v m • lam m) →
      (∀ j, ∑ m, ρ j m • lam m = Pi.single j 1) → 1 ≤ A → (∀ z j, ‖W z j‖ ≤ A) → (∀ j z, ‖Wi j z‖ ≤ A) →
      (∀ m j, ‖lam m j‖ ≤ A) → ‖perVal c σ τ x hm Q‖ ≤ C * A ^ k ∧ ‖(perVal c σ τ x hm Q)⁻¹‖ ≤ C * A ^ k := by
  let P : Type := {p : (Di.La →+ (Letter Dw → ℂ)) × Matrix (Letter Dw) (Fin g) ℂ × Matrix (Fin g) (Letter Dw) ℂ ×
      (Fin r → Fin g → ℂ) × ℝ // GoodPer c σ τ x hm p.1 ∧ p.2.1 * p.2.2.1 = 1 ∧
      (∀ v, ∑ z, p.1 v z • p.2.1 z = ∑ m, T₀ v m • p.2.2.2.1 m) ∧
      (∀ j, ∑ m, ρ j m • p.2.2.2.1 m = Pi.single j 1) ∧ 1 ≤ p.2.2.2.2 ∧ (∀ z j, ‖p.2.1 z j‖ ≤ p.2.2.2.2) ∧
      (∀ j z, ‖p.2.2.1 j z‖ ≤ p.2.2.2.2) ∧ (∀ m j, ‖p.2.2.2.1 m j‖ ≤ p.2.2.2.2)}
  let A : P → ℝ := fun p => p.1.2.2.2.2
  have hA : ∀ p, 1 ≤ A p := fun p => p.2.2.2.2.2.1
  choose B hB using fun m : Fin r =>
    exists_comb (Dw := Dw) x (Formalism.L2.PjFree.relab c σ) (T₀.symm (Pi.single m 1)) (hx.2.1 _)
  have hQ : ∀ (p : P) v z, p.1.1 v z = ∑ j, (∑ m, (T₀ v m : ℂ) * p.1.2.2.2.1 m j) * p.1.2.2.1 j z := by
    rintro ⟨⟨Q, W, Wi, lam, a⟩, -, h1, h2, -⟩ v z
    dsimp only at h1 h2 ⊢
    have h3 : ∀ j, ∑ m, (T₀ v m : ℂ) * lam m j = (Q v ᵥ* W) j := fun j => by
      have := congrFun (h2 v) j
      simp only [Finset.sum_apply, Pi.smul_apply] at this
      simp only [smul_eq_mul, zsmul_eq_mul] at this
      rw [← this]; rfl
    simp only [h3]
    have : Q v = (Q v ᵥ* W) ᵥ* Wi := by rw [Matrix.vecMul_vecMul, h1, Matrix.vecMul_one]
    exact congrFun this z
  have bQ : ∀ v z, PB A fun p => p.1.1 v z := fun v z => by
    simp only [hQ]
    exact PB.sum hA _ fun j => (PB.sum hA _ fun m => (PB.const _).mul (PB.of_le fun p => p.2.2.2.2.2.2.2.2 m j)).mul
      (PB.of_le fun p => p.2.2.2.2.2.2.2.1 j z)
  let S : ∀ t : E →+* ℂ, P → Matrix (Idx Dw τ) (Fin (Dw.mult t)) ℂ := fun t p =>
    Matrix.of fun k i => ∑ j, p.1.2.1 ⟨t, i⟩ j * ∑ m, ρ j m * B m t k
  have bS : ∀ t k i, PB A fun p => S t p k i := fun t k i => by
    simp only [S, Matrix.of_apply]
    exact PB.sum hA _ fun j => (PB.of_le fun p => p.2.2.2.2.2.2.1 _ j).mul (PB.const _)
  have hS : ∀ t (p : P), perMat x p.1.1 t * S t p = 1 := by
    intro t p
    have h4 : ∀ j z, ∑ m, ρ j m * p.1.1 (T₀.symm (Pi.single m 1)) z = p.1.2.2.1 j z := by
      intro j z
      have h5 : ∀ j', ∑ m, ρ j m * p.1.2.2.2.1 m j' = (Pi.single j (1 : ℂ) : Fin g → ℂ) j' := fun j' => by
        simpa [Finset.sum_apply] using congrFun (p.2.2.2.2.1 j) j'
      simp only [hQ, AddEquiv.apply_symm_apply, Pi.single_apply, Int.cast_ite, Int.cast_one, Int.cast_zero, ite_mul,
        _root_.one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.mul_sum]
      rw [Finset.sum_comm]
      simp only [← _root_.mul_assoc, ← Finset.sum_mul, h5, Pi.single_apply, ite_mul,
        _root_.one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ext i i'
    have h6 := congrFun (congrFun p.2.2.1 ⟨t, i'⟩) ⟨t, i⟩
    have h7 : (1 : Matrix (Letter Dw) (Letter Dw) ℂ) ⟨t, i'⟩ ⟨t, i⟩ =
        (1 : Matrix (Fin (Dw.mult t)) (Fin (Dw.mult t)) ℂ) i i' := by
      simp [Matrix.one_apply, eq_comm]
    rw [← h7, ← h6]
    simp only [Matrix.mul_apply, ← h4, hB _ _ p.2.1.1, perMat, S, Matrix.of_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  have hdet : IsUnit ((hm.map (Formalism.L2.PjFree.relab c σ τ))ᵀ).det := by
    rw [Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact ((map_ne_zero _).2 hx.2.2.2).isUnit
  obtain ⟨D, k, -, h⟩ := horVal_bound hA (K := fun p => kerMat c σ τ x hm p.1.1) (C := fun p => perMat x p.1.1 τ)
    (R := fun p => (S (conjEmb τ) p)ᵀ * (hm.map (Formalism.L2.PjFree.relab c σ τ))ᵀ) (S := S τ)
    (fun p => p.2.1.2.1)
    (fun p => by
      rw [kerMat, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hdet, ← Matrix.transpose_mul, hS,
        Matrix.transpose_one])
    (hS τ) (PB.matMul hA (fun _ _ => PB.const _) fun i j => bQ _ _) (fun i j => bQ _ _)
    (PB.matMul hA (fun i j => bS _ _ _) fun _ _ => PB.const _) (bS τ)
  exact ⟨D, k, fun Q W Wi lam a h1 h2 _ h3 h4 h5 h6 h7 h8 =>
    h ⟨⟨Q, W, Wi, lam, a⟩, h1, h2, h3, h4, h5, h6, h7, h8⟩⟩

end GlobalTheory.ShFam.Hor.PolyBd
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.horizontalCoordinate_polynomial_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (σ : c.F →+* ℂ) (Di : Datum H) (τ : E →+* ℂ) (x : Idx Dw τ → Di.La) (hm : Matrix (Idx Dw τ) (Idx Dw τ) E) (g r : ℕ) (T₀ : Di.La ≃+ (Fin r → ℤ)) (ρ : Fin g → Fin r → ℂ), IsPerBasis Di x hm → ∃ (C : ℝ) (k : ℕ), ∀ (Q : Di.La →+ (Letter Dw → ℂ)) (W : Matrix (Letter Dw) (Fin g) ℂ) (Wi : Matrix (Fin g) (Letter Dw) ℂ) (lam : Fin r → Fin g → ℂ) (A : ℝ), GoodPer c σ τ x hm Q → W * Wi = 1 → Wi * W = 1 → (∀ v, ∑ z, Q v z • W z = ∑ m, T₀ v m • lam m) → (∀ j, ∑ m, ρ j m • lam m = Pi.single j 1) → 1 ≤ A → (∀ z j, ‖W z j‖ ≤ A) → (∀ j z, ‖Wi j z‖ ≤ A) → (∀ m j, ‖lam m j‖ ≤ A) → ‖perVal c σ τ x hm Q‖ ≤ C * A ^ k ∧ ‖(perVal c σ τ x hm Q)⁻¹‖ ≤ C * A ^ k := by
  atlas_forward_decl GlobalTheory.ShFam.Hor.PolyBd.perVal_bound
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuousOn_frameDirections_inverse : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (n g : ℕ) (e : OpenPartialHomeomorph (CxPts (genStr Z) σ) (Fin n → ℂ)) (ex : ExpMaps Z σ g), IsExpChart e ex → ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (B : Set V) (a : V → CxFr Z σ), IsOpen B → HolFam B a → (∀ b ∈ B, (a b).1 ∈ e.source) → ∃ (W : V → Matrix (Letter Dw) (Fin g) ℂ) (Wi : V → Matrix (Fin g) (Letter Dw) ℂ), ContinuousOn W B ∧ ContinuousOn Wi B ∧ ∀ b ∈ B, Dirs (a b) (fun w => (ex (a b).1 w).left) (W b) ∧ W b * Wi b = 1 ∧ Wi b * W b = 1 := by
  first | exact @GlobalTheory.ShFam.Hor.ExpDirs.exists_dirs_continuousOn | exact GlobalTheory.ShFam.Hor.ExpDirs.exists_dirs_continuousOn | (intros; apply GlobalTheory.ShFam.Hor.ExpDirs.exists_dirs_continuousOn <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_constant_periodMarking_universalCover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Letter Dw) (Fu : Fam Xo c σ e) (n g' r k : ℕ) (ch : OpenPartialHomeomorph (CxPts (genStr Z) σ) (Fin n → ℂ)) (ex : ExpMaps Z σ g') (lam : (Fin n → ℂ) → Fin r → Fin g' → ℂ) (ρ : Fin g' → Fin r → ℂ), IsLogChart k ch ex lam ρ → ∃ (i : Fin Fu.n) (T₀ : (Fu.Di i).La ≃+ (Fin r → ℤ)), ∀ s ∈ logDom n k, ∀ (a : CxFr Z σ) (W : Letter Dw → Fin g' → ℂ), a.1 = ch.symm (logExp k s) → Dirs a (fun w => (ex a.1 w).left) W → ∃ (Q : (Fu.Di i).La →+ (Letter Dw → ℂ)) (gm : (Fu.Di i).La ≃ₗ[𝓞 E] (Fu.Di i).La), Per Fu a i Q ∧ IsIsom (Fu.Di i) gm ∧ ∀ v, ∑ z, Q (gm v) z • W z = ∑ m, T₀ v m • lam s m := by
  first | exact @GlobalTheory.ShFam.Hor.Mark.exists_marking_const | exact GlobalTheory.ShFam.Hor.Mark.exists_marking_const | (intros; apply GlobalTheory.ShFam.Hor.Mark.exists_marking_const <;> assumption)
end

section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology

namespace GlobalTheory.ShFam.Hor

theorem exists_log_lift {n : ℕ} (a : ℕ) (z : Fin n → ℂ) (hz : ‖z‖ < 1 / 2) (h0 : ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) :
    ∃ s ∈ logDom n a, logExp a s = z ∧ (∀ j : Fin n, (j : ℕ) < a → |(s j).im| ≤ Real.pi) ∧
      1 + ‖s‖ ≤ 5 * (1 + |Real.log ‖∏ k ∈ Finset.univ.filter (fun k : Fin n => (k : ℕ) < a), z k‖|) := by
  classical
  set s : Fin n → ℂ := fun k => if (k : ℕ) < a then Complex.log (z k) else z k with hs
  have hzk : ∀ k, ‖z k‖ < 1 / 2 := fun k => lt_of_le_of_lt (norm_le_pi_norm z k) hz
  have hpos : ∀ k : Fin n, (k : ℕ) < a → 0 < ‖z k‖ := fun k hk => norm_pos_iff.mpr (h0 k hk)
  have hlogneg : ∀ k : Fin n, (k : ℕ) < a → Real.log ‖z k‖ < 0 := fun k hk =>
    Real.log_neg (hpos k hk) (by linarith [hzk k])
  set ℓ := |Real.log ‖∏ k ∈ Finset.univ.filter (fun k : Fin n => (k : ℕ) < a), z k‖| with hℓ
  have hℓk : ∀ k : Fin n, (k : ℕ) < a → -Real.log ‖z k‖ ≤ ℓ := by
    intro k hk
    rw [hℓ, norm_prod, Real.log_prod]
    · calc -Real.log ‖z k‖ ≤ ∑ j ∈ Finset.univ.filter (fun k : Fin n => (k : ℕ) < a), -Real.log ‖z j‖ := by
            apply Finset.single_le_sum (f := fun j => -Real.log ‖z j‖)
            · intro j hj
              have := hlogneg j (Finset.mem_filter.mp hj).2
              linarith
            · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩
        _ = -∑ j ∈ Finset.univ.filter (fun k : Fin n => (k : ℕ) < a), Real.log ‖z j‖ := by
            rw [Finset.sum_neg_distrib]
        _ ≤ _ := neg_le_abs _
    · intro j hj
      exact (hpos j (Finset.mem_filter.mp hj).2).ne'
  have hℓ0 : 0 ≤ ℓ := abs_nonneg _
  refine ⟨s, ?_, ?_, ?_, ?_⟩
  · intro k
    by_cases hk : (k : ℕ) < a
    · simp only [hk, if_true, hs]
      rw [Complex.log_re]
      exact hlogneg k hk
    · simp only [hk, if_false, hs]
      linarith [hzk k]
  · funext k
    by_cases hk : (k : ℕ) < a
    · simp only [logExp, hk, if_true, hs]
      exact Complex.exp_log (h0 k hk)
    · simp only [logExp, hk, if_false, hs]
  · intro j hj
    simp only [hj, if_true, hs]
    rw [Complex.log_im]
    exact Complex.abs_arg_le_pi _
  · have hsk : ∀ k, ‖s k‖ ≤ ℓ + 4 := by
      intro k
      by_cases hk : (k : ℕ) < a
      · simp only [hk, if_true, hs]
        have h1 : ‖Complex.log (z k)‖ ≤ |(Complex.log (z k)).re| + |(Complex.log (z k)).im| :=
          Complex.norm_le_abs_re_add_abs_im _
        rw [Complex.log_re, Complex.log_im] at h1
        have h2 : |Real.log ‖z k‖| = -Real.log ‖z k‖ := abs_of_neg (hlogneg k hk)
        have h3 := Complex.abs_arg_le_pi (z k)
        have h4 := hℓk k hk
        linarith [Real.pi_lt_four]
      · simp only [hk, if_false, hs]
        linarith [hzk k]
    have : ‖s‖ ≤ ℓ + 4 := (pi_norm_le_iff_of_nonneg (by linarith)).mpr hsk
    linarith

theorem eventually_entries_le {V m n : Type} [TopologicalSpace V] [Fintype m] [Fintype n] {W : V → Matrix m n ℂ} {b₀ : V}
    (h : ContinuousAt W b₀) : ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ b in 𝓝 b₀, ∀ i j, ‖W b i j‖ ≤ M := by
  classical
  have hij : ∀ i j, ∀ᶠ b in 𝓝 b₀, ‖W b i j‖ < ‖W b₀ i j‖ + 1 := by
    intro i j
    have hc : ContinuousAt (fun b => ‖W b i j‖) b₀ :=
      continuous_norm.continuousAt.comp ((continuous_id.matrix_elem i j).continuousAt.comp h)
    exact hc.eventually_lt continuousAt_const (lt_add_one _)
  refine ⟨∑ i, ∑ j, (‖W b₀ i j‖ + 1), ?_, ?_⟩
  · exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity
  · have hall : ∀ᶠ b in 𝓝 b₀, ∀ i j, ‖W b i j‖ < ‖W b₀ i j‖ + 1 :=
      Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun j => hij i j
    filter_upwards [hall] with b hb i j
    calc ‖W b i j‖ ≤ ‖W b₀ i j‖ + 1 := (hb i j).le
      _ ≤ ∑ j', (‖W b₀ i j'‖ + 1) :=
          Finset.single_le_sum (f := fun j' => ‖W b₀ i j'‖ + 1) (fun _ _ => by positivity) (Finset.mem_univ j)
      _ ≤ ∑ i', ∑ j', (‖W b₀ i' j'‖ + 1) :=
          Finset.single_le_sum (f := fun i' => ∑ j', (‖W b₀ i' j'‖ + 1))
            (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ i)

theorem differentiableOn_finset_prod {V J : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {u : Finset J} {f : J → V → ℂ}
    {B : Set V} (h : ∀ i ∈ u, DifferentiableOn ℂ (f i) B) : DifferentiableOn ℂ (fun b => ∏ i ∈ u, f i b) B := by
  classical
  induction u using Finset.induction_on with
  | empty => simp [differentiableOn_const]
  | insert i u hi ih =>
    simp only [Finset.prod_insert hi]
    exact (h i (Finset.mem_insert_self i u)).mul (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem logGrowth_of_eq_perVal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Letter Dw) (Fu : Fam Xo c σ e) (τ : E →+* ℂ) (x : ∀ i, Idx Dw τ → (Fu.Di i).La) (hm : Fin Fu.n → Matrix (Idx Dw τ) (Idx Dw τ) E) (h : CxFr T.Z σ → ℂ), Formalism.L2.PjFree.GoodEmb c σ → 1 ≤ Dw.p + Dw.q → (∀ i, IsPerBasis (Fu.Di i) (x i) (hm i)) → (∀ a i Q, Per Fu a i Q → h a = perVal c σ τ (x i) (hm i) Q) → LogGrowth h := by
  classical
  intro E _ _ _ H Dw l Xo c O _ β Y T σ g e Fu τ x hm h hσ hpq hx hh x₀
  obtain ⟨n, g', r, ka, ch, ex, lam, ρ, hx₀, he0, hL⟩ := GlobalTheory.T.exists_exponential_chart_at_point E H Dw l Xo c O β Y T σ hσ hpq x₀
  obtain ⟨hE, hIn, -, hlam, C0, k0, hC0⟩ := id hL
  refine ⟨ch.source ∩ ch ⁻¹' Metric.ball 0 (1 / 2),
    fun y => ∏ j ∈ Finset.univ.filter (fun j : Fin n => (j : ℕ) < ka), ch y j, ?_, ?_, ?_, ?_, ?_⟩
  · exact ch.isOpen_inter_preimage Metric.isOpen_ball
  · refine ⟨hx₀, ?_⟩
    simp only [Set.mem_preimage, he0, Metric.mem_ball, dist_self]
    norm_num
  · intro V _ _ _ B y hB hy hmaps
    show DifferentiableOn ℂ (fun b => ∏ j ∈ Finset.univ.filter (fun j : Fin n => (j : ℕ) < ka), ch (y b) j) B
    exact differentiableOn_finset_prod (f := fun j b => ch (y b) j)
      fun j _ => hE.2.1 j V B y hB hy fun b hb => (hmaps hb).1
  · intro y hy
    simp only [Finset.prod_ne_zero_iff, Finset.mem_filter, Finset.mem_univ, true_and]
    exact (hIn y hy.1).symm
  · intro V _ _ _ B f hB hf hfN b₀ hb₀
    obtain ⟨i, T₀, hT⟩ := GlobalTheory.T.exists_constant_periodMarking_universalCover E H Dw l Xo c O β T.Z σ g e Fu n g' r ka ch ex lam ρ hL
    obtain ⟨C, k, hCk⟩ := GlobalTheory.T.horizontalCoordinate_polynomial_bound E H Dw l c σ (Fu.Di i) τ (x i) (hm i) g' r T₀ ρ (hx i)
    obtain ⟨W, Wi, hW, hWi, hWW⟩ :=
      GlobalTheory.T.exists_continuousOn_frameDirections_inverse E H Dw l Xo c O β T.Z σ n g' ch ex hE V B f hB hf fun b hb => (hfN b hb).1
    obtain ⟨M, hM0, hMe⟩ := eventually_entries_le (hW.continuousAt (hB.mem_nhds hb₀))
    obtain ⟨M', hM'0, hMe'⟩ := eventually_entries_le (hWi.continuousAt (hB.mem_nhds hb₀))
    set K : ℝ := 1 + M + M' + |C0| * 5 ^ k0 with hK
    have hc5 : 0 ≤ |C0| * 5 ^ k0 := by positivity
    refine ⟨max C 0 * K ^ k, k0 * k, ?_⟩
    filter_upwards [hMe, hMe', hB.mem_nhds hb₀] with b hbW hbWi hbB
    intro hin
    obtain ⟨hys, hyb⟩ := hfN b hbB
    have hyb' : ‖ch (f b).1‖ < 1 / 2 := by
      simpa only [Set.mem_preimage, Metric.mem_ball, dist_zero_right] using hyb
    have hnz : ∀ j : Fin n, (j : ℕ) < ka → ch (f b).1 j ≠ 0 := (hIn _ hys).mp hin
    obtain ⟨s, hsD, hsE, hsIm, hsB⟩ := exists_log_lift ka (ch (f b).1) hyb' hnz
    have hsymm : ch.symm (logExp ka s) = (f b).1 := by rw [hsE]; exact ch.left_inv hys
    obtain ⟨Q, gm, hPer, hIso, hQ⟩ := hT s hsD (f b) (W b) hsymm.symm (hWW b hbB).1
    have hGood := GlobalTheory.T.periodLinearAlgebra_hodgeSequence_exact E H Dw l Xo c O β T.Z σ g e Fu τ (f b) i Q (x i) (hm i) hPer (hx i)
    obtain ⟨hGood', hnorm, -⟩ := GlobalTheory.T.horizontalCoordinate_lattice_isometry_det_one E H Dw l c σ (Fu.Di i) τ (x i) (hm i) Q gm (hx i) hGood hIso
    have hhb : h (f b) = perVal c σ τ (x i) (hm i) Q := hh (f b) i Q hPer
    have hlamb : ‖lam s‖ ≤ C0 * (1 + ‖s‖) ^ k0 := hC0 s hsD (by rw [hsE]; exact hyb'.le) hsIm
    set large₂ : ℝ := 1 + |Real.log ‖∏ j ∈ Finset.univ.filter (fun j : Fin n => (j : ℕ) < ka), ch (f b).1 j‖| with hLg
    have hLg1 : 1 ≤ large₂ := le_add_of_nonneg_right (abs_nonneg _)
    have hpowL : 1 ≤ large₂ ^ k0 := one_le_pow₀ hLg1
    set A : ℝ := max 1 (max (max M M') ‖lam s‖) with hA
    have hA1 : 1 ≤ A := le_max_left _ _
    have hKle : K ≤ K * large₂ ^ k0 := le_mul_of_one_le_right (by linarith) hpowL
    have hlam' : ‖lam s‖ ≤ K * large₂ ^ k0 := by
      calc ‖lam s‖ ≤ C0 * (1 + ‖s‖) ^ k0 := hlamb
        _ ≤ |C0| * (1 + ‖s‖) ^ k0 := mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
        _ ≤ |C0| * (5 * large₂) ^ k0 :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hsB k0) (abs_nonneg _)
        _ = (|C0| * 5 ^ k0) * large₂ ^ k0 := by rw [mul_pow]; ring
        _ ≤ K * large₂ ^ k0 := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have hAK : A ≤ K * large₂ ^ k0 :=
      max_le (by linarith) (max_le (max_le (by linarith) (by linarith)) hlam')
    have hb := hCk (Q.comp gm.toLinearMap.toAddMonoidHom) (W b) (Wi b) (lam s) A hGood'
      (hWW b hbB).2.1 (hWW b hbB).2.2 (fun v => hQ v) (hlam s hsD).2.2 hA1
      (fun z j => (hbW z j).trans (le_trans (le_trans (le_max_left M M') (le_max_left _ _)) (le_max_right _ _)))
      (fun j z => (hbWi j z).trans (le_trans (le_trans (le_max_right M M') (le_max_left _ _)) (le_max_right _ _)))
      (fun m j => (norm_le_pi_norm (lam s m) j).trans
        ((norm_le_pi_norm (lam s) m).trans (le_trans (le_max_right _ _) (le_max_right _ _))))
    have hAk : A ^ k ≤ K ^ k * large₂ ^ (k0 * k) := by
      calc A ^ k ≤ (K * large₂ ^ k0) ^ k := pow_le_pow_left₀ (by linarith) hAK k
        _ = K ^ k * large₂ ^ (k0 * k) := by rw [mul_pow, ← pow_mul]
    have hCA : C * A ^ k ≤ max C 0 * K ^ k * large₂ ^ (k0 * k) := by
      calc C * A ^ k ≤ max C 0 * A ^ k := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
        _ ≤ max C 0 * (K ^ k * large₂ ^ (k0 * k)) := mul_le_mul_of_nonneg_left hAk (le_max_right _ _)
        _ = max C 0 * K ^ k * large₂ ^ (k0 * k) := by ring
    have key1 : ‖h (f b)‖ ≤ max C 0 * K ^ k * large₂ ^ (k0 * k) := by
      rw [hhb, ← hnorm]; exact hb.1.trans hCA
    have key2 : ‖(h (f b))⁻¹‖ ≤ max C 0 * K ^ k * large₂ ^ (k0 * k) := by
      rw [hhb, norm_inv, ← hnorm, ← norm_inv]; exact hb.2.trans hCA
    exact ⟨key1, key2⟩

end GlobalTheory.ShFam.Hor
end
