module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.PeriodMapPresentation

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct Topology

section Period

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

open Classical in
def sigMult (D : Datum H) (τ : E →+* ℂ) : ℕ := if τ (H.rt : E) = H.rt0 then D.p else D.q

def IsTypeFn (D : Datum H) {g : ℕ} (ty : Fin g → (E →+* ℂ)) : Prop :=
  ∀ τ : E →+* ℂ, Nat.card {i : Fin g // ty i = τ} = sigMult D τ

def tyAct {g : ℕ} (ty : Fin g → (E →+* ℂ)) (a : 𝓞 E) (z : Fin g → ℂ) : Fin g → ℂ :=
  fun i => ty i (a : E) * z i

def actR (D : Datum H) (a : 𝓞 E) : ℝ ⊗[ℤ] D.La →ₗ[ℝ] ℝ ⊗[ℤ] D.La :=
  (DistribSMul.toLinearMap ℤ D.La a).baseChange ℝ

def sigTrace (D : Datum H) (a : 𝓞 E) : ℂ :=
  ∑ τ ∈ Finset.univ.filter (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0),
    ((D.p : ℂ) * τ (a : E) + (D.q : ℂ) * starRingEnd ℂ (τ (a : E)))

def domain (D : Datum H) : Set (ℝ ⊗[ℤ] D.La →ₗ[ℝ] ℝ ⊗[ℤ] D.La) :=
  {J | (∀ x, J (J x) = -x) ∧
    (∀ a : 𝓞 E, J ∘ₗ actR D a = actR D a ∘ₗ J) ∧
    (∀ x y, D.EF.baseChange ℝ (J x) (J y) = D.EF.baseChange ℝ x y) ∧
    (∀ x, x ≠ 0 → 0 < D.EF.baseChange ℝ (J x) x) ∧
    ∀ a : 𝓞 E, ((LinearMap.trace ℝ _ (actR D a) : ℝ) : ℂ) / 2 -
      Complex.I * ((LinearMap.trace ℝ _ (J ∘ₗ actR D a) : ℝ) : ℂ) / 2 = sigTrace D a}

def Presents (D : Datum H) {g : ℕ} (ty : Fin g → (E →+* ℂ)) (P : D.La →+ (Fin g → ℂ))
    (J : ℝ ⊗[ℤ] D.La →ₗ[ℝ] ℝ ⊗[ℤ] D.La) : Prop :=
  ∃ φ : (ℝ ⊗[ℤ] D.La) ≃ₗ[ℝ] (Fin g → ℂ),
    (∀ x : D.La, φ ((1 : ℝ) ⊗ₜ[ℤ] x) = P x) ∧ (∀ v, φ (J v) = Complex.I • φ v) ∧
      ∀ (a : 𝓞 E) v, φ (actR D a v) = tyAct ty a (φ v)

theorem domain_nonempty (D : Datum H) : (domain D).Nonempty := by
  obtain ⟨J, h1, h2, h3, h4⟩ := D.dom
  have key := fun a : 𝓞 E => h4 a (actR D a) (sigTrace D a) (fun x => rfl) rfl
  refine ⟨J, h1, fun a => (key a).1, h2, h3, fun a => ?_⟩
  rw [(key a).2.1, (key a).2.2]
  apply Complex.ext
  · simp
  · simp; ring

end Period

section Hol

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X : Scheme.{0}}

end Hol

section Theta

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {S : Scheme.{0}} {G : Over S} [GrpObj G] {g : ℕ}

end Theta

end GlobalTheory.IndefiniteRowSideFullHecke.PeriodMapPresentation
