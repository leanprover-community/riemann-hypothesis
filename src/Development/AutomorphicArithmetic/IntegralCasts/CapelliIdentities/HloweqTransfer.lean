module

import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ComplexNormedInstanceCompat

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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace UpperTheory.Reformulated.B.Re4

noncomputable def Jm : {n : ℕ} → (Fin n → Bool) → Matrix (Fin n) (Fin n) ℂ :=
  fun {_} ε => Matrix.diagonal fun a => if ε a = true then 1 else -1

noncomputable def inUJ : {n : ℕ} → (Fin n → Bool) → Matrix (Fin n) (Fin n) ℂ → Prop :=
  fun {_} ε g => g.conjTranspose * Jm ε * g = Jm ε

theorem aux3 : ∀ {n : ℕ} (ε : Fin n → Bool) {g h : (Matrix (Fin n) (Fin n) ℂ)ˣ},
  g ∈ {g : (Matrix (Fin n) (Fin n) ℂ)ˣ | inUJ ε g.val} →
    h ∈ {g : (Matrix (Fin n) (Fin n) ℂ)ˣ | inUJ ε g.val} → g * h ∈ {g : (Matrix (Fin n) (Fin n) ℂ)ˣ | inUJ ε g.val} :=
  @UpperTheory.Reformulated.B.Re3.aux3

theorem aux4 : ∀ {n : ℕ} (ε : Fin n → Bool),
  (1 : Matrix (Fin n) (Fin n) ℂ).conjTranspose * Jm ε * 1 = Jm ε :=
  @UpperTheory.Reformulated.B.Re3.aux4

theorem aux5 : ∀ {n : ℕ} (ε : Fin n → Bool) {g : (Matrix (Fin n) (Fin n) ℂ)ˣ},
  g ∈ {g : (Matrix (Fin n) (Fin n) ℂ)ˣ | inUJ ε g.val} → g⁻¹ ∈ {g : (Matrix (Fin n) (Fin n) ℂ)ˣ | inUJ ε g.val} :=
  @UpperTheory.Reformulated.B.Re3.aux5

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
  IsTopologicalGroup ↥(UJ ε) :=
  @UpperTheory.Reformulated.B.Re3.aux8

theorem aux9 : ∀ (n : ℕ) (ε : Fin n → Bool),
  BorelSpace ↥(UJ ε) :=
  @UpperTheory.Reformulated.B.Re3.aux9

theorem laurent_T_neg_one_mul_T_one : ∀ (n : ℕ) (ε : Fin n → Bool),
  LocallyCompactSpace ↥(UJ ε) :=
  @UpperTheory.Reformulated.B.Re3.laurent_T_neg_one_mul_T_one

noncomputable def muG : {n : ℕ} →
  (ε : Fin n → Bool) → MeasureTheory.Measure ↥(UJ ε) :=
  fun {n} ε => by
    letI := aux8 ε
    letI := aux9 n ε
    letI := laurent_T_neg_one_mul_T_one n ε
    exact MeasureTheory.Measure.haar

theorem algebra_smulCommClass_complex : (1 + 1).AtLeastTwo :=
  inferInstance

@[reducible] noncomputable def L2 : {n : ℕ} → (Fin n → Bool) → Type :=
  fun {_} ε => ↥(MeasureTheory.Lp ℂ 2 (muG ε))

noncomputable def d15 : {n : ℕ} → (Fin n → Bool) → Matrix (Fin n) (Fin n) ℂ :=
  fun {_} ε => Jm ε

noncomputable def Kset : {n : ℕ} → (Fin n → Bool) → Set (Matrix (Fin n) (Fin n) ℂ) :=
  fun {n} ε =>
    {g |
      g ∈ Matrix.unitaryGroup (Fin n) ℂ ∧
        g * d15 ε = d15 ε * g}

theorem complex_normed_instance_compat : IsBoundedSMul ℂ ℂ :=
  @UpperTheory.Reformulated.B.Re3.complex_normed_instance_compat

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

theorem hloweq_transfer : ∀ {n : ℕ} {ε : Fin n → Bool} {Λ : Fin n → ℝ}
  (A : L2 ε →ₗ[ℂ] L2 ε),
  (∀ k ∈ Kset ε,
      ∀ (x : L2 ε),
        A ((rreg ε k) x) = (rreg ε k) (A x)) →
    ∀ {S : Submodule ℂ (L2 ε)},
      (∀ w ∈ S, A w = 0 → w = 0) →
        IsKTypeOf ε (rreg ε) Λ S →
          IsKTypeOf ε (rreg ε) Λ (Submodule.map A S) :=
  @UpperTheory.Reformulated.B.Re3.hloweq_transfer

end UpperTheory.Reformulated.B.Re4
