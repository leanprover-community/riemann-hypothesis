module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RsIntegralEntireTheta
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RsTermZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.JSW
open scoped ComplexConjugate

namespace GlobalTheory.RSnmUnf

def padNat {m n : ℕ} (l : Fin m → ℕ) : Fin n → ℕ := fun i => if h : (i : ℕ) < m then l ⟨i, h⟩ else 0

theorem padNat_zero {m n : ℕ} : padNat (m := m) (n := n) 0 = 0 := by
  funext i; simp only [padNat, Pi.zero_apply]; split_ifs <;> rfl


open Classical in
def rsTermNM (q : ℕ) {n m : ℕ} (α : Fin n → ℂ) (β : Fin m → ℂ) (x : ℝ) (v : Fin m → ℤ) : ℂ :=
  if (∀ i, 0 ≤ v i) ∧ Antitone v then
    schurAt (padNat fun i => (v i).toNat) α * conj (schurAt (fun i => (v i).toNat) β) *
      ((q : ℂ) ^ (-(x : ℂ))) ^ (∑ i, (v i).toNat)
  else 0

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

def uIntNM {m n : ℕ} (hmn : m + 1 ≤ n) (F : (Fin (m + 1) → Ad E) → ℂ) (φ : GA E n → ℂ) (φ' : GA E (m + 1) → ℂ)
    (x : ℝ) (h : GA E (m + 1)) : ℂ :=
  whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL hmn h) * conj (whit φ' h) * GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow h) *
    ((GlobalTheory.RSnm.detAbs h : ℝ) : ℂ) ^ ((x : ℂ) - ((n : ℂ) - ((m + 1 : ℕ) : ℂ)) / 2)

end GlobalTheory.RSnmUnf
