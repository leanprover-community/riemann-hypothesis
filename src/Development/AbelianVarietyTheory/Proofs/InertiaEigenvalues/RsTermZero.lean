module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ZintZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.RSJ
open scoped ComplexConjugate

namespace GlobalTheory.ZEul


open Classical in
def rsTerm (q : ℕ) {n : ℕ} (α β : Fin n → ℂ) (x : ℝ) (v : Fin n → ℤ) : ℂ :=
  if (∀ i, 0 ≤ v i) ∧ Antitone v then
    schurAt (fun i => (v i).toNat) α * conj (schurAt (fun i => (v i).toNat) β) *
      ((q : ℂ) ^ (-(x : ℂ))) ^ (∑ i, (v i).toNat)
  else 0

theorem rsTerm_zero (q : ℕ) {n : ℕ} (α β : Fin n → ℂ) (x : ℝ) : rsTerm q α β x 0 = 1 := by
  have h : (fun _ : Fin n => (0 : ℕ)) = fun i => ((0 : Fin n → ℤ) i).toNat := by funext i; simp
  have hs : schurAt (fun i => ((0 : Fin n → ℤ) i).toNat) α = 1 := by
    rw [← h, schurAt, schur_zero]; simp
  have hs' : schurAt (fun i => ((0 : Fin n → ℤ) i).toNat) β = 1 := by
    rw [← h, schurAt, schur_zero]; simp
  rw [rsTerm, if_pos ⟨fun i => le_rfl, antitone_const⟩, hs, hs']
  simp

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {m : ℕ}

def lastRow (g : GA E (m + 1)) : Fin (m + 1) → Ad E := fun j => (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) j

def uInt (φ φ' : GA E (m + 1) → ℂ) (Φ : (Fin (m + 1) → Cinf E) → ℂ) (N : ℕ) (x : ℝ) (g : GA E (m + 1)) : ℂ :=
  whit φ (g * infGL E (m + 1) (secInv fun i => pInf E (lastRow g i))) *
    conj (whit φ' (g * infGL E (m + 1) (secInv fun i => pInf E (lastRow g i)))) *
    Φ (fun i => pInf E (lastRow g i)) * indN N (fun i => GlobalTheory.RSJ.pFin E (lastRow g i)) * (detPow E (m + 1) x g : ℂ)

end GlobalTheory.ZEul
