module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial MeasureTheory Module

abbrev GlobalTheory (κ : Type) : Unit → Type := fun _ => κ

abbrev Ix (κ : Type) : Type := Σ k, GlobalTheory κ k

section Points

variable {J : Type} [Fintype J] {D : ℕ}

abbrev pts (P : Ideal (MvPolynomial J ℤ)) : Set (J → ℂ) :=
  conePts (Int.castRingHom ℂ) P

def coneOver (U : Set (Fin D → ℂ)) (γ : (Fin D → ℂ) → J → ℂ) : Set (J → ℂ) :=
  {z | ∃ y ∈ U, ∃ c : ℂ, c ≠ 0 ∧ z = c • γ y}

def IsParam (P : Ideal (MvPolynomial J ℤ)) (U : Set (Fin D → ℂ)) (γ : (Fin D → ℂ) → J → ℂ) :
    Prop :=
  IsOpen U ∧ AnalyticOnNhd ℂ γ U ∧ (∀ y ∈ U, γ y ∈ pts P) ∧
    ∃ (O : Set (J → ℂ)) (q : (J → ℂ) → Fin D → ℂ), IsOpen O ∧ AnalyticOnNhd ℂ q O ∧
      O ∩ pts P = coneOver U γ ∧ (∀ z ∈ O, ∀ c : ℂ, c ≠ 0 → c • z ∈ O ∧ q (c • z) = q z) ∧
      ∀ y ∈ U, q (γ y) = y

def IsSmoothPts (P : Ideal (MvPolynomial J ℤ)) (D : ℕ) : Prop :=
  ∀ z ∈ pts P, ∃ T : Submodule ℂ (J → ℂ),
    (∀ w, w ∈ T ↔ IsConeTangent (Int.castRingHom ℂ) P z w) ∧ finrank ℂ T = D + 1

def IsDegZero (g : (J → ℂ) → ℝ) : Prop :=
  ∀ (c : ℂ) (z : J → ℂ), c ≠ 0 → g (c • z) = g z

def IsVolumeOn (P : Ideal (MvPolynomial J ℤ)) (D : ℕ) (μ : Measure (J → ℂ)) : Prop :=
  IsProbabilityMeasure μ ∧ μ (pts P)ᶜ = 0 ∧
    ∀ (U : Set (Fin D → ℂ)) (γ : (Fin D → ℂ) → J → ℂ), IsParam P U γ →
      ∃ ν : (Fin D → ℂ) → ℝ, ContDiffOn ℝ 1 ν U ∧ (∀ y ∈ U, 0 < ν y) ∧
        ∀ g : (J → ℂ) → ℝ, Measurable g → IsDegZero g → (∀ z, 0 ≤ g z) →
          ∫⁻ z in coneOver U γ, ENNReal.ofReal (g z) ∂μ =
            ∫⁻ y in U, ENNReal.ofReal (g (γ y) * ν y)

def conjPt (z : J → ℂ) : J → ℂ := fun i => starRingEnd ℂ (z i)

end Points

section Lattice

variable {Ω : Type*} [Field Ω] [CharZero Ω] {J : Type} [Fintype J]

def IsSecBasis (x : J → Ω) (n : ℕ) {r : ℕ} (b : Fin r → MvPolynomial J ℚ) : Prop :=
  (∀ k, ∃ f : MvPolynomial J ℤ, f.IsHomogeneous n ∧ b k = map (Int.castRingHom ℚ) f) ∧
    LinearIndependent ℤ (fun k => aeval x (b k)) ∧
    Submodule.span ℤ (Set.range fun k => aeval x (b k)) = sec ℤ x n


open Classical in
def chi (x : J → Ω) (m : ConeMetric (C := ℂ) (ι := J)) (μ : Measure (J → ℂ)) (n : ℕ) : ℝ := by
  classical
  exact if h : ∃ p : (Σ r : ℕ, Fin r → MvPolynomial J ℚ), IsSecBasis x n p.2 then
    l2Degree (K := ℚ) (fun _ => m) (fun _ => μ) n h.choose.2
  else 0

def matAct (A : Matrix J J ℚ) (x : J → Ω) : J → Ω :=
  fun i => ∑ j, (A i j : Ω) * x j

def matActC (A : Matrix J J ℚ) (z : J → ℂ) : J → ℂ :=
  fun i => ∑ j, (A i j : ℂ) * z j

end Lattice

section Top

variable {κ : Type} [Fintype κ]

def _root_.ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofCone
    (m : ConeMetric (C := ℂ) (ι := Ix κ)) : HermLine (GlobalTheory κ) where
  a := 1
  h := m.ρ
  pos z hz := m.pos z fun h0 => by
    obtain ⟨i, hi⟩ := hz ()
    exact hi (congrFun h0 _)
  smul c z _ := by
    have : (fun p : Ix κ => c p.1 * z p) = c () • z := by
      funext p
      rfl
    rw [this, m.smul]
    simp

abbrev AllFam : Type 1 :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)],
    Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ

def AllFam.IsFamily (I : AllFam) : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)], IsIntersectionFamily (I K ι)

variable {Ω : Type*} [Field Ω] [CharZero Ω]

def top (I : AllFam) (x : Ix κ → Ω) (m : ConeMetric (C := ℂ) (ι := Ix κ)) (D : ℕ) : ℝ :=
  I Unit (GlobalTheory κ) (coordIdeal ℤ x) (D + 1) fun _ => HermLine.ofCone m

structure IsGood (D : ℕ) (x : Ix κ → Ω) (m : ConeMetric (C := ℂ) (ι := Ix κ))
    (μ : Measure (Ix κ → ℂ)) :
    Prop where
  arith : IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1)
  indep : LinearIndependent ℚ x
  smooth : IsSmoothPts (coordIdeal ℤ x) D
  semipos : IsSemipositiveOn m (Int.castRingHom ℂ) (coordIdeal ℤ x) (pts (coordIdeal ℤ x))
  conjM : IsConjInvariant m
  conjMu : μ.map conjPt = μ
  vol : IsVolumeOn (coordIdeal ℤ x) D μ

end Top

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
