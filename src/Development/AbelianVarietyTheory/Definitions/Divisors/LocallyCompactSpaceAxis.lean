module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EisensteinIsotropicLine
import Mathlib.Tactic.Linter.HaveILetI
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIdTorusEltOne

@[expose] public section

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
open GlobalTheory.Doubling (absE)
open scoped TensorProduct NNReal

namespace GlobalTheory.ResLine

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def col {n r : ℕ} (X : Matrix (Fin n) (Fin (r + 1)) E) : Matrix (Fin n) (Fin 1) E := X.submatrix id fun _ => 0

def Scales (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x : Matrix (Fin n) (Fin 1) E) (p : GAd σ J)
    (l : (AF F ⊗[F] E)ˣ) : Prop := (matHom _ σ J p).1 * adMat F x = l.1 • adMat F x

def lineGrp (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x : Matrix (Fin n) (Fin 1) E) : Subgroup (GAd σ J) where
  carrier := {p | ∃ l, Scales σ J x p l}
  one_mem' := ⟨1, by simp [Scales]⟩
  mul_mem' := fun {a b} ⟨l, e⟩ ⟨l', e'⟩ => ⟨l * l', by
    unfold Scales at *
    rw [map_mul, Units.val_mul, Matrix.mul_assoc, e', Matrix.mul_smul, e, smul_smul, Units.val_mul, mul_comm]⟩
  inv_mem' := fun {a} ⟨l, e⟩ => ⟨l⁻¹, by
    unfold Scales at *
    have := congrArg (fun Z => (l⁻¹).1 • ((matHom _ σ J a⁻¹).1 * Z)) e
    simp only [← Matrix.mul_assoc, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, Matrix.one_mul,
      Matrix.mul_smul, smul_smul, one_smul] at this
    exact this.symm⟩

structure Data (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ} (X Y : Matrix (Fin n) (Fin (r + 1)) E)
    (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ) : Prop where
  cm : IsCMExt F E σ
  unr : Algebra.Unramified (𝓞 F) (𝓞 E)
  herm : IsHermND σ J
  witt : IsWittFrame σ J X Y
  adapted : GlobalTheory.EisLine.IsAdapted σ J X Y L a
  iwa : ∀ g, ∃ p l, Scales σ J (col X) p l ∧ ∃ k ∈ levelAll σ J L a, g = p * k
  ht : ∀ p l, Scales σ J (col X) p l → ∀ k ∈ levelAll σ J L a, h (p * k) = absE F E l

def IsReps (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x : Matrix (Fin n) (Fin 1) E) (T : Set (ratPts σ J)) : Prop :=
  ∀ γ : ratPts σ J, ∃! t, t ∈ T ∧ ∃ l, Scales σ J x (γ * t⁻¹ : ratPts σ J).1 l

structure IsHt {G : Type} [Group G] [TopologicalSpace G] (K : Subgroup G) (h : G → ℝ) : Prop where
  pos : ∀ g, 0 < h g
  cont : Continuous h
  one : ∀ k ∈ K, h k = 1
  iw : ∀ g, ∃ k ∈ K, ∀ x, h (g * x) = h g * h (k * x)

instance countable_inf {G : Type} [Group G] (Γ H : Subgroup G) [Countable Γ] : Countable (Γ ⊓ H : Subgroup G) :=
  (Subgroup.inclusion_injective inf_le_left).countable

structure SemiLat {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] (N M Λ : Subgroup G) (ν : Measure N)
    (π : Measure M) (𝓝 : Set N) (𝓜 : Set M) : Prop where
  closedN : IsClosed (N : Set G)
  closedM : IsClosed (M : Set G)
  norm : ∀ m ∈ M, ∀ u ∈ N, m * u * m⁻¹ ∈ N
  disj : ∀ g ∈ N, g ∈ M → g = 1
  dec : ∀ γ ∈ Λ, ∃ u ∈ N, ∃ m ∈ M, u ∈ Λ ∧ m ∈ Λ ∧ γ = u * m
  haarN : ν.IsHaarMeasure
  haarM : π.IsHaarMeasure
  domN : IsFundamentalDomain (Λ.subgroupOf N) 𝓝 ν
  domM : IsFundamentalDomain (Λ.subgroupOf M) 𝓜 π
  finN : ν 𝓝 ≠ ⊤
  finM : π 𝓜 ≠ ⊤
  count : Countable Λ := by infer_instance
  topGrp : IsTopologicalGroup G := by infer_instance
  borel : BorelSpace G := by infer_instance

namespace Inhab

open GlobalTheory.IdTorus
open Formalism.UG (cT)
open GlobalTheory.Doubling (conjUnit)

variable {σ : E →ₐ[F] E}
  {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin (r + 1)) E}

theorem semiLat_ne_zero {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G]
    {N M Λ : Subgroup G} {ν : Measure N} {π : Measure M} {𝓝 : Set N} {𝓜 : Set M}
    (H : SemiLat N M Λ ν π 𝓝 𝓜) : ν 𝓝 ≠ 0 := by
  haveI := H.haarN
  haveI := H.count
  haveI := H.topGrp
  haveI := H.borel
  haveI : Countable (Λ.subgroupOf N) := Function.Injective.countable
    (f := fun x : Λ.subgroupOf N => (⟨x.1.1, x.2⟩ : Λ)) fun a b h => Subtype.ext (Subtype.ext (congrArg (·.1) h))
  exact H.domN.measure_ne_zero (NeZero.ne ν)

end Inhab

end GlobalTheory.ResLine

end
