module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace UpperTheory.Reformulated.B.Re3

noncomputable def Jm : {n : ℕ} → (Fin n → Bool) → Matrix (Fin n) (Fin n) ℂ :=
  fun {_} ε => Matrix.diagonal fun a => if ε a = true then 1 else -1

noncomputable def inUJ : {n : ℕ} → (Fin n → Bool) → Matrix (Fin n) (Fin n) ℂ → Prop :=
  fun {_} ε g => g.conjTranspose * Jm ε * g = Jm ε

theorem aux3 : ∀ {n : ℕ} (ε : Fin n → Bool) {g h : (Matrix (Fin n) (Fin n) ℂ)ˣ},
  g ∈ {g : (Matrix (Fin n) (Fin n) ℂ)ˣ | inUJ ε g.val} →
    h ∈ {g : (Matrix (Fin n) (Fin n) ℂ)ˣ | inUJ ε g.val} → g * h ∈ {g : (Matrix (Fin n) (Fin n) ℂ)ˣ | inUJ ε g.val} := by
  intro n ε g h hg hh
  have hg' : (g : Matrix (Fin n) (Fin n) ℂ).conjTranspose * Jm ε * g = Jm ε := hg
  have hh' : (h : Matrix (Fin n) (Fin n) ℂ).conjTranspose * Jm ε * h = Jm ε := hh
  show ((g * h : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ).conjTranspose * Jm ε *
    ((g * h : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = Jm ε
  rw [Units.val_mul, Matrix.conjTranspose_mul]
  calc _ = (h : Matrix (Fin n) (Fin n) ℂ).conjTranspose *
        ((g : Matrix (Fin n) (Fin n) ℂ).conjTranspose * Jm ε * g) * h := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hg', hh']

theorem aux4 : ∀ {n : ℕ} (ε : Fin n → Bool),
  (1 : Matrix (Fin n) (Fin n) ℂ).conjTranspose * Jm ε * 1 = Jm ε := by
  intro n ε
  simp

theorem aux5 : ∀ {n : ℕ} (ε : Fin n → Bool) {g : (Matrix (Fin n) (Fin n) ℂ)ˣ},
  g ∈ {g : (Matrix (Fin n) (Fin n) ℂ)ˣ | inUJ ε g.val} → g⁻¹ ∈ {g : (Matrix (Fin n) (Fin n) ℂ)ˣ | inUJ ε g.val} := by
  intro n ε g hg
  have hg' : (g : Matrix (Fin n) (Fin n) ℂ).conjTranspose * Jm ε * g = Jm ε := hg
  show ((g⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ).conjTranspose * Jm ε *
    ((g⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = Jm ε
  calc _ = ((g⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ).conjTranspose *
        ((g : Matrix (Fin n) (Fin n) ℂ).conjTranspose * Jm ε * g) *
        ((g⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) := by rw [hg']
    _ = ((g : Matrix (Fin n) (Fin n) ℂ) * ((g⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)).conjTranspose *
        Jm ε *
        ((g : Matrix (Fin n) (Fin n) ℂ) * ((g⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [Units.mul_inv, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

noncomputable def UJ : {n : ℕ} → (Fin n → Bool) → Subgroup (Matrix (Fin n) (Fin n) ℂ)ˣ :=
  fun {_} ε =>
    { carrier := {g | inUJ ε g.val}
      mul_mem' := aux3 ε
      one_mem' := aux4 ε
      inv_mem' := aux5 ε }

@[reducible] noncomputable def instMeasurableSpaceUJ : (n : ℕ) →
  (ε : Fin n → Bool) → MeasurableSpace ↥(UJ ε) :=
  fun _ ε => borel ↥(UJ ε)

attribute [local instance] instMeasurableSpaceUJ

theorem aux8 : ∀ {n : ℕ} (ε : Fin n → Bool),
  IsTopologicalGroup ↥(UJ ε) := by
  intro n ε
  infer_instance

theorem aux9 : ∀ (n : ℕ) (ε : Fin n → Bool),
  BorelSpace ↥(UJ ε) := by
  intro n ε
  exact ⟨rfl⟩

theorem laurent_T_neg_one_mul_T_one : ∀ (n : ℕ) (ε : Fin n → Bool),
  LocallyCompactSpace ↥(UJ ε) := by
  intro n ε
  have : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))
  have hc : IsClosed (UJ ε : Set (Matrix (Fin n) (Fin n) ℂ)ˣ) := by
    show IsClosed {g : (Matrix (Fin n) (Fin n) ℂ)ˣ |
      (g : Matrix (Fin n) (Fin n) ℂ).conjTranspose * Jm ε * g = Jm ε}
    exact isClosed_eq
      ((Units.continuous_val.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul Units.continuous_val)
      continuous_const
  exact hc.locallyCompactSpace

noncomputable def muG : {n : ℕ} →
  (ε : Fin n → Bool) → MeasureTheory.Measure ↥(UJ ε) :=
  fun {n} ε => by
    letI := aux8 ε
    letI := aux9 n ε
    letI := laurent_T_neg_one_mul_T_one n ε
    exact MeasureTheory.Measure.haar

theorem algebra_smulCommClass_complex : (1 + 1).AtLeastTwo := by
  exact ⟨le_refl 2⟩

@[reducible] noncomputable def L2 : {n : ℕ} → (Fin n → Bool) → Type :=
  fun {_} ε => ↥(MeasureTheory.Lp ℂ 2 (muG ε))

noncomputable def d15 : {n : ℕ} → (Fin n → Bool) → Matrix (Fin n) (Fin n) ℂ :=
  fun {_} ε => Jm ε

noncomputable def Kset : {n : ℕ} → (Fin n → Bool) → Set (Matrix (Fin n) (Fin n) ℂ) :=
  fun {n} ε =>
    {g |
      g ∈ Matrix.unitaryGroup (Fin n) ℂ ∧
        g * d15 ε = d15 ε * g}

theorem complex_normed_instance_compat : IsBoundedSMul ℂ ℂ := by
  infer_instance

@[reducible] noncomputable def umat : {n : ℕ} →
  {ε : Fin n → Bool} → ↥(UJ ε) → Matrix (Fin n) (Fin n) ℂ :=
  fun {_} {_} g => g.val.val

noncomputable def rregG : {n : ℕ} → (ε : Fin n → Bool) → ↥(UJ ε) → L2 ε →L[ℂ] L2 ε :=
  fun {_} ε y => by
    classical
    exact if hm : MeasureTheory.MeasurePreserving (fun x => x * y) (muG ε) (muG ε) then
      (MeasureTheory.Lp.compMeasurePreservingₗᵢ ℂ (fun x => x * y) hm).toContinuousLinearMap
    else 1

noncomputable def rreg : {n : ℕ} → (ε : Fin n → Bool) →
    Matrix (Fin n) (Fin n) ℂ → L2 ε →L[ℂ] L2 ε :=
  fun {_} ε g => by
    classical
    exact if h : ∃ y, umat y = g then rregG ε h.choose else 1

noncomputable def d21 : {n : ℕ} → (Fin n → Bool) → Set (Matrix (Fin n) (Fin n) ℂ) :=
  fun {n} ε =>
    {g |
      g ∈ Matrix.unitaryGroup (Fin n) ℂ ∧
        g * Jm ε = Jm ε * g}

noncomputable def IsKStableOn.{u_1} {n : ℕ} {H : Type u_1}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ε : Fin n → Bool)
    (σ : Matrix (Fin n) (Fin n) ℂ → H →L[ℂ] H) (S : Submodule ℂ H) : Prop :=
  ∀ g ∈ d21 ε, ∀ v ∈ S, σ g v ∈ S

noncomputable def IsWtOn.{u_1} {n : ℕ} {H : Type u_1}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (G : Set (Matrix (Fin n) (Fin n) ℂ))
    (σ : Matrix (Fin n) (Fin n) ℂ → H →L[ℂ] H) (μ : Fin n → ℝ) (v : H) : Prop :=
  ∀ (θ : Fin n → ℝ),
    (Matrix.diagonal fun a => Complex.exp (↑(θ a) * Complex.I)) ∈ G →
      σ (Matrix.diagonal fun a => Complex.exp (↑(θ a) * Complex.I)) v =
        Complex.exp (↑(∑ a, μ a * θ a) * Complex.I) • v

noncomputable def root : {n : ℕ} → Fin n → Fin n → Fin n → ℝ :=
  fun {_} a b => Pi.single a 1 - Pi.single b 1

noncomputable def CDom : {n : ℕ} → (Fin n → Bool) → (Fin n → ℝ) → (Fin n → ℝ) → Prop :=
  fun {n} ε μ Λ =>
    ∃ c : Fin n → Fin n → ℕ,
      (∀ (a b : Fin n), c a b ≠ 0 → a < b ∧ ε a = ε b) ∧
        Λ - μ = ∑ a, ∑ b, (c a b : ℝ) • root a b

noncomputable def IsKTypeOf.{u_1} {n : ℕ} {H : Type u_1}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ε : Fin n → Bool)
    (σ : Matrix (Fin n) (Fin n) ℂ → H →L[ℂ] H) (Λ : Fin n → ℝ)
    (S : Submodule ℂ H) : Prop :=
  FiniteDimensional ℂ S ∧
    IsKStableOn ε σ S ∧
    (∀ S' ≤ S, IsKStableOn ε σ S' → S' = ⊥ ∨ S' = S) ∧
    (∃ v ∈ S, v ≠ 0 ∧ IsWtOn (d21 ε) σ Λ v) ∧
    ∀ μ : Fin n → ℝ, ∀ v ∈ S, v ≠ 0 → IsWtOn (d21 ε) σ μ v → CDom ε μ Λ

private theorem transfer_gen {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ε : Fin n → Bool} {Λ : Fin n → ℝ} (σ : Matrix (Fin n) (Fin n) ℂ → H →L[ℂ] H) (A : H →ₗ[ℂ] H)
    (hA : ∀ k ∈ d21 ε, ∀ x : H, A (σ k x) = σ k (A x))
    {S : Submodule ℂ H} (hinj : ∀ w ∈ S, A w = 0 → w = 0)
    (hS : IsKTypeOf ε σ Λ S) :
    IsKTypeOf ε σ Λ (Submodule.map A S) := by
  obtain ⟨hfd, hst, hirr, ⟨v, hvS, hv0, hvw⟩, hdom⟩ := hS
  refine ⟨inferInstance, ?_, ?_, ?_, ?_⟩
  · rintro g hg _ ⟨w, hw, rfl⟩
    exact ⟨σ g w, hst g hg w hw, hA g hg w⟩
  · intro S' hS' hst'
    have hT : IsKStableOn ε σ (S ⊓ Submodule.comap A S') := by
      intro g hg w hw
      refine ⟨hst g hg w hw.1, ?_⟩
      show A (σ g w) ∈ S'
      rw [hA g hg w]
      exact hst' g hg _ hw.2
    rcases hirr _ inf_le_left hT with h | h
    · left
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨w, hw, rfl⟩ := hS' hx
      have hw0 : w ∈ S ⊓ Submodule.comap A S' := ⟨hw, hx⟩
      rw [h, Submodule.mem_bot] at hw0
      simp [hw0]
    · right
      refine le_antisymm hS' ?_
      rintro _ ⟨w, hw, rfl⟩
      have hw1 : w ∈ S ⊓ Submodule.comap A S' := by rw [h]; exact hw
      exact hw1.2
  · refine ⟨A v, ⟨v, hvS, rfl⟩, fun h => hv0 (hinj v hvS h), ?_⟩
    intro θ hθ
    rw [← hA _ hθ, hvw θ hθ, map_smul]
  · rintro μ _ ⟨w, hw, rfl⟩ hw0 hwt
    refine hdom μ w hw (fun h => hw0 (by simp [h])) ?_
    intro θ hθ
    apply sub_eq_zero.mp
    apply hinj _ (S.sub_mem (hst _ hθ w hw) (S.smul_mem _ hw))
    rw [map_sub, map_smul, hA _ hθ, hwt θ hθ, sub_self]

theorem hloweq_transfer : ∀ {n : ℕ} {ε : Fin n → Bool} {Λ : Fin n → ℝ}
  (A : L2 ε →ₗ[ℂ] L2 ε),
  (∀ k ∈ Kset ε,
      ∀ (x : L2 ε),
        A ((rreg ε k) x) = (rreg ε k) (A x)) →
    ∀ {S : Submodule ℂ (L2 ε)},
      (∀ w ∈ S, A w = 0 → w = 0) →
        IsKTypeOf ε (rreg ε) Λ S →
          IsKTypeOf ε (rreg ε) Λ (Submodule.map A S) := by
  intro n ε Λ A hA S hinj hS
  exact transfer_gen (rreg ε) A hA hinj hS

end UpperTheory.Reformulated.B.Re3
