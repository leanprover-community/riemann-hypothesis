import ReciprocityTheory.SemistableReduction.LatSemiSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.IndependentSectionsUpperCount
import ReciprocityTheory.SemistableReduction.Unipotent

section
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open Matrix NumberField ComplexConjugate Module
open scoped ComplexOrder

def ballRatio (r : ℕ) : ℝ := (1 + 1 / (7 * (r : ℝ))) / (1 - 1 / (7 * (r : ℝ)))

def signMat (p r : ℕ) : Matrix (Fin r) (Fin r) ℂ := Matrix.diagonal fun k : Fin r => sgn p k

def BoundedBallStatement : Prop :=
  ∀ (r p : ℕ) (H : Matrix (Fin r) (Fin r) ℂ) (s : ℝ),
    H.PosDef → H * signMat p r * H = signMat p r → 0 ≤ s → s < 1 →
    (∀ u : Fin r → ℂ, signMat p r *ᵥ (H *ᵥ u) = u → negSq p u ≤ s ^ 2 * posSq p u) →
    ∀ u : Fin r → ℂ, hq H u ≤ (1 + s) / (1 - s) * normSq u ∧
      normSq u ≤ (1 + s) / (1 - s) * hq H u

def NearMaj {K : Type} [Field K] [NumberField K] {r : ℕ} {S : HermForm K r}
    (M0 M : Majorant S) (c : ℝ) : Prop :=
  ∀ (σ : K →+* ℂ) (u : Fin r → ℂ),
    hq (M.H σ) u ≤ c * hq (M0.H σ) u ∧ hq (M0.H σ) u ≤ c * hq (M.H σ) u

def NoContraction {K : Type} [Field K] [NumberField K] {r : ℕ}
    (H : (K →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (L : Submodule (𝓞 K) (Fin r → K)) : Prop :=
  ∀ N : Matrix (Fin r) (Fin r) K, (∀ x ∈ L, N *ᵥ x ∈ L) →
    (∀ (σ : K →+* ℂ) (u : Fin r → ℂ), u ≠ 0 → hq (H σ) (N.map σ *ᵥ u) < hq (H σ) u) → N = 0

def BallTrivialStatement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (r g : ℕ) (S : HermForm K r)
    (L : Submodule (𝓞 K) (Fin r → K)) (M0 M1 M2 : Majorant S) (γ : Matrix (Fin r) (Fin r) K),
    NoContraction M0.H L → NearMaj M0 M1 (ballRatio r) → NearMaj M0 M2 (ballRatio r) →
    (∀ (σ : K →+* ℂ) (u : Fin r → ℂ), hq (M2.H σ) (γ.map σ *ᵥ u) = hq (M1.H σ) u) →
    (∀ x ∈ L, γ *ᵥ x ∈ L) →
    (∀ n : ℕ, 1 ≤ n → n ≤ r → ∃ z : 𝓞 K, (γ ^ n).trace - r = (g : K) * z) → 3 * r < g →
    γ = 1

def orbitMat {U Z : Type} [Group U] [MulAction U Z] (u0 : Z → ℂ) (z : Z) : Matrix U U ℂ :=
  Matrix.of fun a b => u0 ((a * b) • z)

def MonomialDetStatement : Prop :=
  ∀ (U : Type) [Group U] [Fintype U] [DecidableEq U] (Z : Type) [MulAction U Z]
    (u0 : Z → ℂ) (z0 : Z),
    u0 z0 ≠ 0 → (∀ a : U, a ≠ 1 → u0 (a • z0) = 0) →
    ∀ h : U, (orbitMat (U := U) u0 (h • z0)).det ≠ 0

def ZeroByDetStatement : Prop :=
  ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La]
    (A : ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas n Y ι La) (U : Type) [Fintype U] [DecidableEq U]
    (la la' : La) (M : U → U → ι → Y → ℂ) (x : ι → Y → ℂ),
    (∀ a b, A.IsSec la (M a b)) → A.IsSec la' x →
    (∀ y, ∃ y' ∈ connectedComponent y,
      (Matrix.of fun a b => M a b (A.pick y') y').det ≠ 0) →
    (∀ y, (Matrix.of fun a b => M a b (A.pick y) y).det ≠ 0 → x (A.pick y) y = 0) →
    ∀ j y, y ∈ (A.chart j).source → x j y = 0

def CountStatement : Prop :=
  ∀ (V W R R' : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup R] [Module ℂ R] [AddCommGroup R'] [Module ℂ R'] (U : Type) [Fintype U]
    (m d0 : ℕ) (g : Fin m → V) (res : V →ₗ[ℂ] R) (resW : W →ₗ[ℂ] R')
    (Φ : V →ₗ[ℂ] (U → W)) (Wψ : Submodule ℂ W),
    LinearIndependent ℂ (res ∘ g) →
    (∀ v ∈ Submodule.span ℂ (Set.range g), ∀ h, Φ v h ∈ Wψ) →
    (∀ v ∈ Submodule.span ℂ (Set.range g), (∀ h, resW (Φ v h) = 0) → res v = 0) →
    (∀ (k : ℕ) (f : Fin k → W), (∀ i, f i ∈ Wψ) → LinearIndependent ℂ (resW ∘ f) → k ≤ d0) →
    m ≤ Fintype.card U * d0

def psiPart {K U V : Type} [Field K] [Monoid U] [AddCommGroup V] [Module K V]
    (ρ : Representation K U V) (χ : U →* Kˣ) : Submodule K V :=
  ⨅ u : U, LinearMap.ker (ρ u - ((χ u : Kˣ) : K) • LinearMap.id)

def psiPartBC {K L U V : Type} [Field K] [Field L] [Algebra K L] [Monoid U] [AddCommGroup V]
    [Module K V] (ρ : Representation K U V) (χ : U →* Kˣ) :
    Submodule L (TensorProduct K L V) :=
  ⨅ u : U, LinearMap.ker ((ρ u).baseChange L - algebraMap K L ((χ u : Kˣ) : K) • LinearMap.id)

def FreePsiStatement : Prop :=
  ∀ (K : Type) [Field K] (U : Type) [Group U] [Fintype U] [DecidableEq U]
    (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Representation K U V) (χ : U →* Kˣ) (W0 : Submodule K V),
    DirectSum.IsInternal (fun u : U => W0.map (ρ u)) →
    Fintype.card U * finrank K (psiPart ρ χ) = finrank K V

def PsiBaseChangeStatement : Prop :=
  ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (U : Type) [Group U] [Fintype U]
    (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Representation K U V) (χ : U →* Kˣ),
    finrank L (psiPartBC (L := L) ρ χ) = finrank K (psiPart ρ χ)

def ShareNumbersStatement : Prop :=
  ∀ (D T P f k : ℕ), 6 ≤ D → P ^ 3 * D ^ 3 * k * f ≤ T → f * k ≤ P → 2 ≤ f * k →
    ((D * (D + 6) : ℕ) : ℝ) / T ≤ 1 / (4 * ((f * k : ℕ) : ℝ) ^ 3)

end ReciprocityTheory.MultiplicativeHeights
end
end

section
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open Matrix NumberField
open scoped ComplexOrder MatrixOrder

theorem sb_re_star_dot {r : ℕ} (v : Fin r → ℂ) : (star v ⬝ᵥ v).re = normSq v := by
  unfold normSq dotProduct
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Pi.star_apply, Complex.star_def, Complex.conj_mul']
  norm_cast

theorem sb_normSq_pos {r : ℕ} {v : Fin r → ℂ} (hv : v ≠ 0) : 0 < normSq v := by
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hv
  exact Finset.sum_pos' (fun i _ => by positivity)
    ⟨k, Finset.mem_univ _, pow_pos (norm_pos_iff.mpr hk) 2⟩

theorem sb_exists_root {r : ℕ} {H : Matrix (Fin r) (Fin r) ℂ} (hH : H.PosDef) :
    ∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧ ∀ u, hq H u = normSq (Q *ᵥ u) := by
  have hnn : 0 ≤ H := Matrix.nonneg_iff_posSemidef.mpr hH.posSemidef
  obtain ⟨Q, hQ⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hnn
  rw [Matrix.star_eq_conjTranspose] at hQ
  refine ⟨Q, ?_, fun u => ?_⟩
  · intro h0
    have := hH.det_pos
    rw [hQ, det_mul, h0, mul_zero] at this
    exact lt_irrefl _ this
  · have e : star u ᵥ* Qᴴ = star (Q *ᵥ u) := (star_mulVec Q u).symm
    unfold hq
    rw [hQ, ← mulVec_mulVec, dotProduct_mulVec, e, sb_re_star_dot]

theorem sb_normSq_mulVec_le {r : ℕ} (A : Matrix (Fin r) (Fin r) ℂ) (v : Fin r → ℂ) :
    normSq (A *ᵥ v) ≤ (∑ a, ∑ b, ‖A a b‖ ^ 2) * normSq v := by
  unfold normSq
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun a _ => ?_
  calc ‖(A *ᵥ v) a‖ ^ 2 = ‖∑ b, A a b * v b‖ ^ 2 := rfl
    _ ≤ (∑ b, ‖A a b‖ * ‖v b‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) ((norm_sum_le _ _).trans (le_of_eq (by simp [norm_mul]))) 2
    _ ≤ (∑ b, ‖A a b‖ ^ 2) * (∑ b, ‖v b‖ ^ 2) := Finset.sum_mul_sq_le_sq_mul_sq _ _ _

theorem sb_ballRatio_nonneg {r : ℕ} (hr : 0 < r) : 0 ≤ ballRatio r := by
  have h1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have h7 : 1 / (7 * (r : ℝ)) ≤ 1 / 7 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hx : 0 < 1 / (7 * (r : ℝ)) := by positivity
  unfold ballRatio
  apply div_nonneg <;> linarith

theorem sb_ballRatio_le {r : ℕ} (hr : 0 < r) : ballRatio r ≤ Real.exp (1 / (3 * (r : ℝ))) := by
  have h1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have h7 : 1 / (7 * (r : ℝ)) ≤ 1 / 7 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hx : 0 < 1 / (7 * (r : ℝ)) := by positivity
  have he : 1 / (3 * (r : ℝ)) = 7 * (1 / (7 * (r : ℝ))) / 3 := by
    field_simp
    try ring

  have key : ballRatio r ≤ 7 * (1 / (7 * (r : ℝ))) / 3 + 1 := by
    unfold ballRatio
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  rw [he]
  exact key.trans (Real.add_one_le_exp _)

theorem sb_exp_third_lt_two : Real.exp (1 / 3) < 2 := by
  calc Real.exp (1 / 3) < Real.exp (Real.log 2) :=
        Real.exp_lt_exp.mpr (by have := Real.log_two_gt_d9; linarith)
    _ = 2 := Real.exp_log (by norm_num)

end ReciprocityTheory.MultiplicativeHeights
end
end
