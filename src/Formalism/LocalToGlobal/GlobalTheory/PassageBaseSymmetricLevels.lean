module

public import Formalism.LocalToGlobal.GlobalTheory.DivPassage
public import Formalism.LocalToGlobal.GlobalTheory.DivPassageP
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option linter.style.haveILetI false

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.DivPassage2

open Formalism.L2.Indef Formalism.L2.GlobalTheoryTheory.DivPassage

section Chars

variable {K : Type} [Field K] {Γ : Type} [Group Γ] [Finite Γ]

end Chars

section TP

variable {K : Type} [Field K] {Γ : Type} [Group Γ] [Finite Γ] {n : ℕ}

variable [NumberField K]

end TP

section Norms

open Formalism.HermitianLatticesTheory

variable {K : Type} [Field K] [NumberField K] [StarRing K] {n : ℕ} (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ)

end Norms

section Adj

open Formalism.HermitianLatticesTheory

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Γ : Type} [Group Γ] [Finite Γ] {n : ℕ}
  (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ)

end Adj

section Lat

open Formalism.HermitianLatticesTheory

variable {K : Type} [Field K] [NumberField K] [StarRing K] {D0 D1 : ℕ} (A : LevelAmb K D0 D1)

end Lat

section Gen

open Formalism.HermitianLatticesTheory

variable {K : Type} [Field K] [NumberField K] [StarRing K] {D0 D1 : ℕ} (A : LevelAmb K D0 D1)

theorem rows_gen (hL : A.LatG) {D : ℕ} (ι : Matrix (Fin A.Dg) (Fin D) K) (P : Matrix (Fin A.Dg) (Fin A.Dg) K)
    (hD : 0 < D) (hinj : Function.Injective ι.mulVec) (hr : LinearMap.range ι.mulVecLin = LinearMap.range P.mulVecLin) :
    A.partLat P ≠ ⊥ := by
  intro hb
  have hspan := A.span_partLat hL P
  rw [hb, Submodule.bot_coe, Submodule.span_zero_singleton] at hspan
  obtain ⟨x, hx⟩ : ∃ x : Fin D → K, x ≠ 0 := ⟨fun _ => 1, fun h => one_ne_zero (congrFun h ⟨0, hD⟩)⟩
  have hmem : ι *ᵥ x ∈ LinearMap.range P.mulVecLin := by
    rw [← hr]
    exact ⟨_, rfl⟩
  rw [← hspan, Submodule.mem_bot] at hmem
  exact hx (hinj (by rw [hmem, Matrix.mulVec_zero]))

end Gen

section Triv

variable {K : Type} [Field K] [NumberField K] [StarRing K]

end Triv

end Formalism.L2.GlobalTheoryTheory.DivPassage2
