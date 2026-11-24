module

public import GroundTheory.AutomorphicForms.MacdonaldNormalization
public import GroundTheory.AutomorphicForms.MacdonaldSpherical
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical

namespace UpperTheory.Gal.Gen

def pt {n : ℕ} (θ : Fin n → UnitAddCircle) : Fin n → ℂˣ := fun i => Circle.toUnits (AddCircle.toCircle (θ i))

abbrev prs (n : ℕ) : Finset (Fin n × Fin n) := (Finset.univ : Finset (Fin n × Fin n)).filter fun p => p.1 < p.2

def half {n : ℕ} (t : ℂ) (z : Fin n → ℂˣ) : ℂ :=
  ∏ p ∈ prs n, (1 - (z p.1 : ℂ) / (z p.2 : ℂ)) / (1 - t * ((z p.1 : ℂ) / (z p.2 : ℂ)))

def dens {n : ℕ} (t : ℂ) (z : Fin n → ℂˣ) : ℂ := half t z * half t z⁻¹

def RFormula : Prop :=
  ∀ (n : ℕ) (t : ℂ) (l : Fin n → ℤ) (z : Fin n → ℂˣ), Function.Injective z →
    evalAt z (hlR t l) = ∑ σ : Equiv.Perm (Fin n), monomialChar l (z ∘ σ) *
      ∏ p ∈ prs n, ((z (σ p.1) : ℂ) - t * (z (σ p.2) : ℂ)) / ((z (σ p.1) : ℂ) - (z (σ p.2) : ℂ))

def RConj : Prop :=
  ∀ (n : ℕ) (t : ℝ) (l : Fin n → ℤ) (z : Fin n → ℂˣ), Function.Injective z → (∀ i, ‖(z i : ℂ)‖ = 1) →
    evalAt z (hlR (t : ℂ) (fun i => -l (Fin.rev i))) = (starRingEnd ℂ) (evalAt z (hlR (t : ℂ) l))

def WtPos : Prop :=
  ∀ (n : ℕ) (l : Fin n → ℤ), Antitone l → l ≠ 0 → ∃ c : ℤ, 0 < ∑ i, l i * (c - (i : ℕ))

def MeanVal : Prop :=
  ∀ (n : ℕ) (t : ℝ), 0 ≤ t → t < 1 → ∀ (z : Fin n → ℂˣ), (∀ i, ‖(z i : ℂ)‖ = 1) → ∀ (c : ℤ) (m : ℕ),
    ∫ s : UnitAddCircle, ((AddCircle.toCircle s : Circle) : ℂ) ^ m *
      half (t : ℂ) (fun i => Circle.toUnits (AddCircle.toCircle s) ^ (c - (i : ℕ)) * z i) = if m = 0 then 1 else 0

def DensCont : Prop :=
  ∀ (n : ℕ) (t : ℝ), 0 ≤ t → t < 1 → (Continuous fun θ : Fin n → UnitAddCircle => half (t : ℂ) (pt θ)) ∧
    (Continuous fun θ : Fin n → UnitAddCircle => dens (t : ℂ) (pt θ)) ∧
    (∀ p : LaurentRing n, Continuous fun θ : Fin n → UnitAddCircle => evalAt (pt θ) p) ∧
    ∀ θ : Fin n → UnitAddCircle, ∀ i, ‖(pt θ i : ℂ)‖ = 1

def HalfInt : Prop :=
  ∀ (n : ℕ) (t : ℝ), 0 ≤ t → t < 1 → ∀ l : Fin n → ℤ, Antitone l →
    ∫ θ : Fin n → UnitAddCircle, monomialChar l (pt θ) * half (t : ℂ) (pt θ) = if l = 0 then 1 else 0

def NullZero : Prop :=
  ∀ (n : ℕ) (p : MvPolynomial (Fin n) ℂ), p ≠ 0 →
    ∀ᵐ θ : Fin n → UnitAddCircle, MvPolynomial.eval (fun i => (pt θ i : ℂ)) p ≠ 0

def RDens : Prop :=
  ∀ (n : ℕ) (t : ℝ), 0 ≤ t → t < 1 → ∀ (l : Fin n → ℤ) (z : Fin n → ℂˣ), Function.Injective z → (∀ i, ‖(z i : ℂ)‖ = 1) →
    evalAt z (hlR (t : ℂ) l) * dens (t : ℂ) z = ∑ σ : Equiv.Perm (Fin n), monomialChar l (z ∘ σ) * half (t : ℂ) (z ∘ σ)

def RInt : Prop :=
  ∀ (n : ℕ) (t : ℝ), 0 ≤ t → t < 1 → ∀ l : Fin n → ℤ, Antitone l →
    ∫ θ : Fin n → UnitAddCircle, evalAt (pt θ) (hlR (t : ℂ) l) * dens (t : ℂ) (pt θ) = if l = 0 then (n.factorial : ℂ) else 0

def StarEx : Prop :=
  ∀ (n : ℕ), ∀ p ∈ symmetricLaurent (n := n), ∃ q ∈ symmetricLaurent (n := n),
    ∀ z : Fin n → ℂˣ, (∀ i, ‖(z i : ℂ)‖ = 1) →
    evalAt z q = (starRingEnd ℂ) (evalAt z p)

def SymEx : Prop :=
  ∀ (n : ℕ) (Φ : MvPolynomial (Fin n) ℂ), ∃ p ∈ symmetricLaurent (n := n),
    (∀ z : Fin n → ℂˣ, evalAt z p = ∏ σ : Equiv.Perm (Fin n), MvPolynomial.eval (fun i => (z (σ i) : ℂ)) Φ) ∧
    (Φ ≠ 0 → ∃ Ψ : MvPolynomial (Fin n) ℂ, Ψ ≠ 0 ∧ ∀ z : Fin n → ℂˣ, evalAt z p = MvPolynomial.eval (fun i => (z i : ℂ)) Ψ)

def Small : Prop :=
  ∀ (n : ℕ) (Φ : MvPolynomial (Fin n) ℂ), Φ ≠ 0 → ∀ δ : ℝ, 0 < δ → ∃ p ∈ symmetricLaurent (n := n),
    (∀ z : Fin n → ℂˣ, MvPolynomial.eval (fun i => (z i : ℂ)) Φ = 0 → evalAt z p = 1) ∧
    ∫ θ : Fin n → UnitAddCircle, ‖evalAt (pt θ) p‖ ^ 2 ≤ δ

section

variable (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ)
  [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)] (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure]


open Classical in
def GammaIntAt : Prop :=
  ∀ g : GL (Fin n) F,
    (Continuous fun θ : Fin n → UnitAddCircle => zonalSpherical μ (pt θ) g) ∧
    vPoly n ((qF F : ℂ))⁻¹ * ∫ θ : Fin n → UnitAddCircle, zonalSpherical μ (pt θ) g * dens ((qF F : ℂ))⁻¹ (pt θ) =
      if g ∈ GLnLocal.integralGL F n then (n.factorial : ℂ) else 0

def GammaConjAt : Prop :=
  ∀ (z : Fin n → ℂˣ), Function.Injective z → (∀ i, ‖(z i : ℂ)‖ = 1) → ∀ g : GL (Fin n) F,
    zonalSpherical μ z g⁻¹ = (starRingEnd ℂ) (zonalSpherical μ z g)


variable {F n μ} in
def IsReps (h : SphericalHecke μ (F := F) (n := n)) (T : Finset (GL (Fin n) F)) : Prop :=
  (∀ g ∈ T, ∀ g' ∈ T, g⁻¹ * g' ∈ GLnLocal.integralGL F n → g = g') ∧
  ∀ f : GL (Fin n) F → ℂ, (∀ g, ∀ k ∈ GLnLocal.integralGL F n, f (g * k) = f g) →
    ∫ x, (h : HeckeAlgebra μ) x * f x ∂μ =
      (μ.real (GLnLocal.integralGL F n : Set (GL (Fin n) F)) : ℂ) * ∑ g ∈ T, (h : HeckeAlgebra μ) g * f g

def RepsExAt : Prop := ∀ h : SphericalHecke μ (F := F) (n := n), ∃ T, IsReps h T

def PlanchAt : Prop :=
  ∃ C : ℝ, ∀ (h : SphericalHecke μ (F := F) (n := n)) (T : Finset (GL (Fin n) F)), IsReps h T →
    ∑ g ∈ T, ‖(h : HeckeAlgebra μ) g‖ ^ 2 ≤ C * ∫ θ : Fin n → UnitAddCircle, ‖evalAt (pt θ) (satakeTransform μ h)‖ ^ 2

end

def GammaInt : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ)
    [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)] (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure], GammaIntAt F n μ

def GammaConj : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ)
    [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)] (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure], GammaConjAt F n μ

def RepsEx : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ)
    [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)] (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure], RepsExAt F n μ

def Planch : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ)
    [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)] (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure], PlanchAt F n μ

end UpperTheory.Gal.Gen

end
