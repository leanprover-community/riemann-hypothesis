import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.SpanRatSmulMem

open NumberField ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj.FJ
open scoped ComplexConjugate

namespace GlobalTheory.FJCuspCheck

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}

theorem emb_cc (τ : E →+* ℂ) (x : E) : τ (cc x) = conj (τ x) :=
  IsCMField.complexEmbedding_complexConj E τ x

theorem cc_kappa (X : Data E r) : cc X.κ0 = -X.κ0 := by
  have h := X.ξ0_im
  unfold cc at h ⊢
  rcases X.κ0_xi with h' | h' <;> rw [h'] <;> simp [h, map_ofNat]

noncomputable def ev (χ : Matrix (Fin ρ) (Fin ρ) E) (u u' : Fin ρ → E) : E :=
  ∑ a, ∑ b, u a * χ a b * cc (u' b)

noncomputable def gen (X : Data E r) (b : E) (u u' : Fin ρ → E) : Matrix (Fin ρ) (Fin ρ) E :=
  Matrix.of fun i k => X.κ0 / 2 * (b * u i * cc (u' k) + cc b * u' i * cc (u k))


def cuspOfIso (X : Data E r) (ξ : Fin r → E) (h0 : ξ ≠ 0) (hi : herm X.Gm ξ ξ = 0) : CuspFD X 1 where
  e := fun _ => ξ
  ind := linearIndependent_unique_iff.2 h0
  iso := fun _ _ => hi

end GlobalTheory.FJCuspCheck
