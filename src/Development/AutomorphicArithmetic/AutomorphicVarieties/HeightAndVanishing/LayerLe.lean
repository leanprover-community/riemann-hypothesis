module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V.Base UpperTheory.Top

namespace UpperTheory.V.HV

def lossAll (l N n e : ℕ) : ℕ := Chr.loss l N n e + N.primeFactors.card * n.factorization l

def LayerLe (χ : PChar) (l : ℕ) [Fact l.Prime] (j t : ℕ) (B : ℝ) : Prop :=
  ∀ (L₀ : Type) [Field L₀] [NumberField L₀], IsAbField (Lchi χ l) L₀ →
    ∀ (L₁ : Type) [Field L₁] [NumberField L₁] [Algebra L₀ L₁], IsLayer l j L₀ L₁ → VVat l L₁ t B

def CountIV : Prop :=
  ∀ (χ : PChar) (l : ℕ) [Fact l.Prime] (j : ℕ), l ∈ Bchi χ → ∃ C : ℕ, ∀ h : Host, h.chi = χ → ∀ t : ℕ, 2 ≤ t → h.Big t →
    ∀ B : ℝ, LayerLe χ l j t B → ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (c : Coef l)
      (ψ : DirichletCharacter c.O h.N), h.IsChar ψ → Odd (orderOf (chiP l ψ)) →
        Chr.SumLe l c.O (fun e => Vlen Ω c e ψ) t (B + ((h.N : ℝ) * t) ^ C)

def PlusLe {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (ld : ∀ (p : ℕ) [Fact p.Prime], LData E Ω p) (S : Finset Nat.Primes) (t : ℕ) (B : ℝ) : Prop :=
  (∀ l ∈ S, ∀ e : ℕ, 0 < e → e < t → plusLen (ld l) e ≠ ⊤) ∧
    ∑ l ∈ S, Real.log (l : ℕ) * ∑ e ∈ Finset.Ico 1 t, ((plusLen (ld l) e).toNat : ℝ) ≤ B

def SumIn : Prop :=
  ∀ (χ : PChar) (l : Nat.Primes) (j : ℕ), (l : ℕ) ∈ Bchi χ → ∃ C : ℕ, ∀ h : Host, h.chi = χ → ∀ t : ℕ, 2 ≤ t → h.Big t →
    ∀ B : ℝ, 0 ≤ B → LayerLe χ l j t B → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], IsChiField χ h.ex h.q1 h.d E →
      ∀ (Ω : Type) [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (ld : ∀ (p : ℕ) [Fact p.Prime], LData E Ω p),
        PlusLe ld {l} t (((h.N : ℝ) * t) ^ C + C * B)

def SumOut : Prop :=
  ∀ χ : PChar, ∃ (C r₁ r₂ : ℕ), r₁.Prime ∧ r₂.Prime ∧ ∀ h : Host, h.chi = χ → r₁ < h.q1 → r₁ < h.d → r₂ < h.q1 → r₂ < h.d →
    ∀ t : ℕ, 2 ≤ t → h.Big t → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], IsChiField χ h.ex h.q1 h.d E →
      ∀ (Ω : Type) [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (ld : ∀ (p : ℕ) [Fact p.Prime], LData E Ω p)
        (S : Finset Nat.Primes), (∀ l ∈ S, (l : ℕ) ≠ 2 ∧ (l : ℕ) ∉ Bchi χ) → PlusLe ld S t (((h.N : ℝ) * t) ^ C)

def PointHV : Prop :=
  ∀ (χ : PChar) (j : ℕ → ℕ), ∃ (C r₁ r₂ : ℕ), r₁.Prime ∧ r₂.Prime ∧ ∀ h : Host, h.chi = χ →
    r₁ < h.q1 → r₁ < h.d → r₂ < h.q1 → r₂ < h.d → ∀ t : ℕ, 2 ≤ t → h.Big t → ∀ B : ℝ, 0 ≤ B →
      (∀ l ∈ Bchi χ, ∀ [Fact l.Prime], LayerLe χ l (j l) t B) →
      ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], IsChiField χ h.ex h.q1 h.d E →
        VVplusLe E t (((h.N : ℝ) * t) ^ C + C * B)

end UpperTheory.V.HV

end
