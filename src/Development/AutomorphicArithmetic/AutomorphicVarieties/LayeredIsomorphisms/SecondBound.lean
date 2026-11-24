module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimeSetBoundDataOfPrimitiveChar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.LemmaK
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.LevelInertiaLeLevelDec
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V.LDataCardLeFinrank

namespace UpperTheory.V.Win

def jZero (l R : ℕ) : ℕ := Nat.log l R + 3

def SecondBound (l R : ℕ) [Fact l.Prime] (L₀ : Type) [Field L₀] : Prop :=
  ∀ e : ℕ, 1 ≤ e → ∀ (m : ℕ) (L₁ : Type) [Field L₁] [NumberField L₁] [Algebra L₀ L₁], IsLayer l m L₀ L₁ →
    ∀ (L₂ : Type) [Field L₂] [NumberField L₂] [Algebra L₀ L₂], IsLayer l (jZero l R) L₀ L₂ →
      ∀ (Ω : Type) [Field Ω] [Algebra L₂ Ω] [IsAlgClosure L₂ Ω] (D : LData L₂ Ω l),
        shaInv L₁ l e ≤ VLen D e + ((R * (m - jZero l R) : ℕ) : ℕ∞)

def ABound (l R : ℕ) [Fact l.Prime] (L₀ : Type) [Field L₀] : Prop :=
  (∃ (K : Type) (_ : NormedField K) (_ : NormedAlgebra ℚ_[l] K) (_ : IsUltrametricDist K) (c R' : ℕ) (s : Fin R' → K),
    R' ≤ R ∧ (∃ ζ : L₀, IsPrimitiveRoot ζ (l ^ c)) ∧
    ∀ e : ℕ, 1 ≤ e → ∀ (m : ℕ) (L₁ : Type) [Field L₁] [NumberField L₁] [Algebra L₀ L₁], IsLayer l m L₀ L₁ →
      ∀ B : ℕ, (∀ i, (l : ℝ) ^ (-(B : ℤ)) ≤ ‖s i - (e : K)‖) →
        shaInv L₁ l e ≤ ((R' * (max m (jZero l R) + c + B) : ℕ) : ℕ∞)) ∧
  SecondBound l R L₀

def FirstBound (l R c : ℕ) [Fact l.Prime] (L₀ : Type) [Field L₀] (Z : ℕ) (Exc : Finset ℕ) : Prop :=
  Exc.card ≤ R ∧ ∀ e : ℕ, 1 ≤ e → e ≤ Z → e ∉ Exc →
    ∀ (m : ℕ) (L₁ : Type) [Field L₁] [NumberField L₁] [Algebra L₀ L₁], IsLayer l m L₀ L₁ →
      shaInv L₁ l e ≤ ((R * (max m (jZero l R) + c + Nat.log l Z) : ℕ) : ℕ∞)

def FixedIn : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ A : AbF, A.HasMu l → ∀ (L₀ : Type) [Field L₀] [NumberField L₀], IsAbField A L₀ →
    ∃ R : ℕ, ABound l R L₀

def TwoBase (M : AbF) (q d : ℕ) (L₀ : Type) [Field L₀] [NumberField L₀] : Prop :=
  HasMuQ 2 L₀ ∧ Module.finrank ℚ L₀ ≤ 8 * M.deg ∧ Nonempty (L₀ →ₐ[ℚ] CyclotomicField (4 * M.m * q * d) ℚ) ∧
    ∀ e : ℕ, 2 ≤ e → ∀ (E : Type) [Field E] [NumberField E], IsCompField M e q d E →
      ∃ (m : ℕ) (L₁ : Type) (_ : Field L₁) (_ : NumberField L₁) (_ : Algebra L₀ L₁), IsLayer 2 m L₀ L₁ ∧ m ≤ e + 2 ∧
        ∀ k : ℕ, 1 ≤ k → shaInv E 2 k ≤ 1 + shaInv L₁ 2 k

def TwoIn : Prop :=
  ∀ M : AbF, ∃ R : ℕ, ∀ q d : ℕ, PrimePair M.m q d →
    ∃ (L₀ : Type) (_ : Field L₀) (_ : NumberField L₀), TwoBase M q d L₀ ∧ ABound 2 R L₀

def Good (eta Ct : ℝ) (Exc : Finset ℕ) (x : ℝ) : Prop := ∀ e ∈ Exc, (e : ℝ) ≤ x ^ Ct → (e : ℝ) ≤ x ^ eta

def ptBound (C eps x : ℝ) : ℝ := C * (1 + Real.log x) + 2 * Real.exp (C * x ^ (3 * eps / 4))

end UpperTheory.V.Win

end
