module

import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FormalDegreeLeOfNeighbourhoodVolume
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ProjExists
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LinMulti
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace
open GlobalTheory.SepReal
open scoped ContDiff

noncomputable section
namespace GlobalTheory.SepReal.ProjSm

variable {m : ℕ}

theorem mem_iff (ε : Fin m → Bool) (g : Mat m) : g ∈ UJset ε ↔ gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε := Iff.rfl

theorem mul_mem' {ε : Fin m → Bool} {g h : Mat m} (hg : g ∈ UJset ε) (hh : h ∈ UJset ε) : g * h ∈ UJset ε := by
  rw [mem_iff] at *
  rw [Matrix.conjTranspose_mul]
  calc hᴴ * gᴴ * Formalism.REAL.Jm ε * (g * h) = hᴴ * (gᴴ * Formalism.REAL.Jm ε * g) * h := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hg, hh]

theorem one_mem' (ε : Fin m → Bool) : (1 : Mat m) ∈ UJset ε := by
  rw [mem_iff]; simp

theorem exp_mem {ε : Fin m → Bool} {X : Mat m} (hX : X ∈ lieOf (Jm ε)) (t : ℝ) :
    NormedSpace.exp (t • X) ∈ UJset ε := by
  apply GlobalTheory.SepReal.expS_mem_UJset <;> assumption

theorem list_mem {m : ℕ} {ε : Fin m → Bool} : ∀ l : List (Mat m), (∀ x ∈ l, x ∈ UJset ε) → l.prod ∈ UJset ε
  | [], _ => by simpa using one_mem' ε
  | a :: l, h => by
    rw [List.prod_cons]
    exact mul_mem' (h a (by simp)) (list_mem l fun x hx => h x (by simp [hx]))

theorem embH_list {n : ℕ} (e : Option (Fin n) ≃ Fin (n + 1)) : ∀ l : List (Mat n), embH e l.prod = (l.map (embH e)).prod
  | [] => by simp [embH_one]
  | a :: l => by rw [List.prod_cons, embH_mul, embH_list e l, List.map_cons, List.prod_cons]

variable {n : ℕ} {e : Option (Fin n) ≃ Fin (n + 1)} {ε : Fin (n + 1) → Bool} {ε' : Fin n → Bool}
  {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
  {π : Mat (n + 1) → (H →L[ℂ] H)} {σ : Mat n → (H' →L[ℂ] H')} {j : H' →L[ℂ] H} {P : H →L[ℂ] H'}

end GlobalTheory.SepReal.ProjSm
