module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.TowU

section Coord

variable {R : Type} [CommRing R] {κ κ₁ : Type}

variable [Fintype κ] [Fintype κ₁] {W W₁ : Type} [AddCommGroup W] [Module R W] [AddCommGroup W₁] [Module R W₁]
  {B : W → W → R} {B₁ : W₁ → W₁ → R}

end Coord

section Frame

variable {R : Type} [CommRing R] {A : Type} [CommRing A] [Algebra R A] (c : A →ₐ[R] A)
  {α α₁ ν : Type} [Fintype α] [DecidableEq α] [Fintype α₁] [DecidableEq α₁] [Fintype ν] [DecidableEq ν]

structure IsFrame (J : Matrix α α A) (C D : Matrix α ν A) (ι : Matrix α α₁ A) : Prop where
  cc : Cᵀ * J * C.map c = 0
  dd : Dᵀ * J * D.map c = 0
  cd : Cᵀ * J * D.map c = 1
  ic : ιᵀ * J * C.map c = 0
  ci : Cᵀ * J * ι.map c = 0
  id : ιᵀ * J * D.map c = 0
  di : Dᵀ * J * ι.map c = 0
  basis : ∃ M : Matrix ((ν ⊕ ν) ⊕ α₁) α A, Matrix.fromCols (Matrix.fromCols C D) ι * M = 1 ∧
    M * Matrix.fromCols (Matrix.fromCols C D) ι = 1

end Frame

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]


def IsRat {α β κ : Type} [Fintype κ] {B : Matrix α β (AE F E) → Matrix α β (AE F E) → AF F} (d : Darboux B κ) : Prop :=
  ∀ x : Matrix α β E, ∃ y z : κ → F, d.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))

variable (σ : E →ₐ[F] E)

variable {σ}


end GlobalTheory.TowU

end
