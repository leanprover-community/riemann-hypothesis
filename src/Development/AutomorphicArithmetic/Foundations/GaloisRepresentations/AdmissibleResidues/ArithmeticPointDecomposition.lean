module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ArithmeticPointClassicality
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.MapRepApply
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal

@[expose] public section

noncomputable section

namespace UpperTheory.GalN.V

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime]

def PureW (ι : PadicAlgCl l ≃+* ℂ) (r : G ℚ Ω →* M4 (PadicAlgCl l)) : Prop :=
  ∃ (H : Subgroup (G ℚ Ω)) (M : ℕ), IsOpen (H : Set (G ℚ Ω)) ∧ M ≠ 0 ∧ ∀ p : ℕ, p.Prime → ¬ p ∣ M →
    ∀ A : ValuationSubring Ω, A.valuation (p : Ω) < 1 → ∀ (f : ℕ) (σ : G ℚ Ω), 0 < f → σ ∈ H → IsFrob A (p ^ f) σ →
      ∀ x ∈ (r σ).charpoly.roots, ∀ y ∈ (r σ).charpoly.roots, y ≠ 0 → ‖ι x‖ < (p : ℝ) ^ f * ‖ι y‖

theorem pureW' {ι : PadicAlgCl l ≃+* ℂ} {r : G ℚ Ω →* M4 (PadicAlgCl l)} (h : PureW ι r) : PureW ι r := h
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.W UpperTheory.V.HV GlobalTheory.GalOfCusp Formalism.MainNotions.N Polynomial
variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
variable {s : HidaSetting l L Ω} {V : s.Lev} {c : Coef l} {n : ℕ} {r : Resid V.frame c.O n}
variable (B : UniversalOrdinaryDeterminantRing r) (ι : Qbar l ≃+* ℂ) (J : Ideal B.B)

def ArithmeticPointDecomposition : Prop :=
  ∀ (x : B.Pt) (h : s.Wt n), J ≤ RingHom.ker x → x.Arith h →
    ∃ ρ : G L Ω →* GL (Fin n) (Qbar l), Continuous ρ ∧ IsSSRep ρ ∧ x.IsRep ρ ∧
      ∃ (a : ℕ) (d m : Fin a → ℕ) (ρ' : ∀ i, G L Ω →* GL (Fin (d i)) (Qbar l)),
        (∀ i, 1 ≤ d i ∧ 1 ≤ m i ∧ Continuous (ρ' i)) ∧
        (∀ g, (mat ρ g).charpoly =
          ∏ i, ∏ j ∈ Finset.range (m i), (mat (Af.tw (ρ' i) (cycBar L Ω l ^ (-(j : ℤ)))) g).charpoly) ∧
        ((∀ i, m i = 1) → ∀ᶠ w : Plc L in Filter.cofinite, ∀ b : Multiset ℂ, Af.FrobEig ι ρ w b →
          ∀ z ∈ b, ∀ z' ∈ b, ‖z‖ < (normV w : ℝ) * ‖z'‖)

variable {B ι J}
theorem end1W' (h : ArithmeticPointDecomposition B ι J) : ArithmeticPointDecomposition B ι J := h
end

end UpperTheory.GalN.V
