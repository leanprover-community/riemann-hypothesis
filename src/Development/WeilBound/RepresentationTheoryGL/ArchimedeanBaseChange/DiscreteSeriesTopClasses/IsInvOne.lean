import Mathlib

section
noncomputable section

open Finset Matrix Filter Topology MeasureTheory

namespace PositivityTheory.RgTw

def prev {R : Type} [Zero R] (q : ℕ → R) : ℕ → R
  | 0 => 0
  | k + 1 => q k

def IsMQ {ι R : Type} [Fintype ι] [CommRing R] [Algebra ℂ R] (D : ι → Derivation ℂ R R) (s : ι → R) (P : ℕ → R)
    (Q : ι → ℕ → R) : Prop :=
  (∀ k : ℕ, (∑ a, s a ^ 2) * P k + (2 * (k : ℤ) + 2 - Fintype.card ι) • P (k + 1) =
      ∑ i, (D i (Q i k) + (∑ a, s a * D i (s a)) * prev (Q i) k)) ∧
    (∀ k, (2 * k < Fintype.card ι ∨ Fintype.card ι < k) → P k = 0) ∧
    ∀ i k, (2 * k + 1 < Fintype.card ι ∨ Fintype.card ι ≤ k) → Q i k = 0


def MQAlg : Prop :=
  ∀ (ι R : Type) [Fintype ι] [DecidableEq ι] [CommRing R] [Algebra ℂ R] (D : ι → Derivation ℂ R R) (s : ι → R)
    (r : ι → ι → Matrix ι ι ℂ), (∀ i j, (r i j)ᵀ = -r i j) → (∀ i j, r j i = -r i j) →
    (∀ i j a, D i (D j (s a)) - D j (D i (s a)) = ∑ b, r i j a b • s b) →
    ∃ P Q, IsMQ D s P Q ∧ P (Fintype.card ι) = (Matrix.of fun i a => D i (s a)).det

def BlowR : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (β : (ι → ℝ) → (ι → ℝ)) (L : (ι → ℝ) →L[ℝ] (ι → ℝ)),
    LinearMap.det (L : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) ≠ 0 → Continuous β → β 0 = 0 → HasFDerivAt β L 0 →
    (∀ δ : ℝ, 0 < δ → ∃ η : ℝ, 0 < η ∧ ∀ B, ∑ x, β B x ^ 2 ≤ η → ‖B‖ ≤ δ) →
    ∀ F : ℝ → ℝ, Continuous F → (∀ x, 1 ≤ x → F x = 0) → ∀ ψ : (ι → ℝ) → ℂ, Continuous ψ →
      (∀ᶠ t : ℝ in atTop, Integrable fun B => (F (t ^ 2 * (∑ x, β B x ^ 2) / 2) : ℂ) * ψ B) ∧
      Tendsto (fun t : ℝ => (t : ℂ) ^ Fintype.card ι * ∫ B, (F (t ^ 2 * (∑ x, β B x ^ 2) / 2) : ℂ) * ψ B) atTop
        (𝓝 (ψ 0 * ((∫ w : ι → ℝ, F ((∑ x, w x ^ 2) / 2) : ℝ) : ℂ) /
          ((|LinearMap.det (L : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))| : ℝ) : ℂ)))

def Hopf : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (d T : Module.End ℂ V), d * d = 0 →
    T * d = -(d * T) → LinearMap.trace ℂ V T ≠ 0 → ∃ x, d x = 0 ∧ x ∉ LinearMap.range d

def DetAd : Prop :=
  ∀ (n : ℕ) (z : Fin n → ℂ), (∀ a, z a ≠ 0) →
    LinearMap.det ((LinearMap.id + (LinearMap.mulLeft ℂ (diagonal z)) ∘ₗ (LinearMap.mulRight ℂ (diagonal fun a => (z a)⁻¹)) :
      Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ)) = ∏ a, ∏ b, (1 + z a / z b)

end PositivityTheory.RgTw
end
end

section
noncomputable section

open MvPolynomial Matrix
open scoped ContDiff

namespace PositivityTheory.RgTw

variable {n : ℕ}

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

abbrev G (n : ℕ) := Matrix.GeneralLinearGroup (Fin n) ℂ

abbrev Poly (n : ℕ) := MvPolynomial (Fin 4 × Fin n × Fin n) ℂ

def Xm (j : Fin 4) : Matrix (Fin n) (Fin n) (Poly n) := fun a b => X (j, a, b)

def ev (d : Mat n) : Poly n →+* ℂ := MvPolynomial.eval fun x => ![d, dᴴ, d⁻¹, dᴴ⁻¹] x.1 x.2.1 x.2.2

def dZ (Z : Mat n) : Derivation ℂ (Poly n) (Poly n) :=
  MvPolynomial.mkDerivation ℂ fun x =>
    (if (x.1 : ℕ) < 2 then -1 else 1 : Poly n) * (Z.map C * Xm x.1 + Xm x.1 * Z.map C : Matrix (Fin n) (Fin n) (Poly n)) x.2.1 x.2.2

def sigP (n : ℕ) : Matrix (Fin n) (Fin n) (Poly n) := Xm 0 * Xm 1 - Xm 3 * Xm 2

def hb (p : Fin n × Fin n) : Mat n :=
  if p.1 = p.2 then Matrix.single p.1 p.1 1
  else if p.1 < p.2 then ((Real.sqrt 2)⁻¹ : ℂ) • (Matrix.single p.1 p.2 1 + Matrix.single p.2 p.1 1)
  else (((Real.sqrt 2)⁻¹ : ℂ) * Complex.I) • (Matrix.single p.1 p.2 1 - Matrix.single p.2 p.1 1)

def sP (p : Fin n × Fin n) : Poly n := Matrix.trace (sigP n * (hb p).map C)

def uM (d : Mat n) : ℝ := (∑ p, (ev d (sP p)).re ^ 2) / 2

def th (g : G n) : G n := (star g)⁻¹

theorem th_one : th (1 : G n) = 1 := by simp [th]

def tw (x d : G n) : G n := x⁻¹ * d * th x

def twCent (d : G n) : Subgroup (G n) where
  carrier := {x | d * th x = x * d}
  one_mem' := by simp [th]
  mul_mem' := fun {x y} hx hy => by
    simp only [Set.mem_setOf_eq, th, star_mul, _root_.mul_inv_rev] at *
    rw [← mul_assoc, hx, mul_assoc, hy, mul_assoc]
  inv_mem' := fun {x} hx => by
    simp only [Set.mem_setOf_eq, th, star_inv, inv_inv] at *
    rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, ← hx, inv_mul_cancel_right]

def IsInv (τ : Poly n) : Prop :=
  (∀ p, dZ (hb p) τ = 0) ∧ ∀ (x d : G n), ev (tw x d : G n).val τ = ev d.val τ

def IsCutFn (H : ℝ → ℝ) : Prop := ContDiff ℝ ∞ H ∧ ∃ R : ℝ, ∀ x, R ≤ x → H x = 0

def bas (H : ℝ → ℝ) (P : Poly n) (d : G n) : ℂ := (H (uM d.val) : ℂ) * ev d.val P

def adBas (p : Fin n × Fin n) (H : ℝ → ℝ) (P : Poly n) (d : G n) : ℂ :=
  bas (deriv H) ((∑ q, sP q * dZ (hb p) (sP q)) * P) d + bas H (dZ (hb p) P) d

def Shape (n m : ℕ) : Submodule ℂ (G n → ℂ) :=
  Submodule.span ℂ {φ | ∃ H P, IsCutFn H ∧ P.totalDegree ≤ m ∧ φ = bas H P}

def AdSpan (n : ℕ) : Submodule ℂ (G n → ℂ) := Submodule.span ℂ {φ | ∃ p H P, IsCutFn H ∧ φ = adBas p H P}

def fam (F : ℝ → ℝ) (τ : Poly n) (P : ℕ → Poly n) (t : ℝ) (d : G n) : ℂ :=
  ∑ k ∈ Finset.range (n * n + 1), ((t ^ (2 * (k : ℤ) - (n * n : ℕ)) : ℝ) : ℂ) *
    bas (fun x => iteratedDeriv k F (t ^ 2 * x)) (τ * P k) d

def topP (n : ℕ) : Poly n := (Matrix.of fun p q : Fin n × Fin n => dZ (hb p) (sP q)).det

def StInst : Prop :=
  ∀ n : ℕ, ∃ r : Fin n × Fin n → Fin n × Fin n → Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ,
    (∀ i j, (r i j)ᵀ = -r i j) ∧ (∀ i j, r j i = -r i j) ∧
    ∀ i j a, dZ (hb i) (dZ (hb j) (sP a)) - dZ (hb j) (dZ (hb i) (sP a)) = ∑ b, r i j a b • sP b

def StTopVal : Prop :=
  ∀ (n : ℕ) (z : Fin n → ℂ), (∀ a, ‖z a‖ = 1) →
    ev (diagonal z) (topP n) = (-4) ^ (n * n) * ∏ a, ∏ b, (1 + z a / z b)

def StHomot : Prop :=
  ∀ (n : ℕ) (F : ℝ → ℝ) (τ : Poly n) (P : ℕ → Poly n) (Q : Fin n × Fin n → ℕ → Poly n), IsCutFn F → IsInv τ →
    IsMQ (fun p => dZ (hb p)) sP P Q → ∀ t₁ t₂ : ℝ, 0 < t₁ → 0 < t₂ → fam F τ P t₁ - fam F τ P t₂ ∈ AdSpan n

end PositivityTheory.RgTw
end
end
