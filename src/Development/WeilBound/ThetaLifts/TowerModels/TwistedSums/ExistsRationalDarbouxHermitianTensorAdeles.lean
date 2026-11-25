module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalDarbouxHermitianTensorAdeles
@[expose] public section

noncomputable section

namespace Tw.RatDarboux
open _root_.GlobalTheory

section General

open scoped TensorProduct
open Matrix Module GlobalTheory.WeilM

variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]

variable (R : Type) [CommRing R] [Algebra F R]

theorem exists_darboux [CharZero F] [Invertible (2 : R)] (h2 : finrank F E = 2) (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) {JA : Matrix α α E} {JB : Matrix β β E}
    (hA : ∀ i j, σ (JA j i) = JA i j) (hB : ∀ i j, σ (JB j i) = -JB i j) (hA' : JA.det ≠ 0) (hB' : JB.det ≠ 0) :
    ∃ co : Darboux (symp (R := R) (Algebra.TensorProduct.map (AlgHom.id R R) σ) (-1)
      (JA.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) R)) (JB.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) R))) (α × β),
      ∀ x : Matrix α β E, ∃ y z : α × β → F, co.e (x.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) R)) =
        (fun k => algebraMap F R (y k), fun k => algebraMap F R (z k)) :=
  by apply _root_.GlobalTheory.RatDarboux.exists_darboux <;> assumption

theorem det_ne_zero_of_isCartan {n : ℕ} {M θ : Matrix (Fin n) (Fin n) ℂ} (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan M θ) :
    M.det ≠ 0 :=
  _root_.GlobalTheory.RatDarboux.det_ne_zero_of_isCartan h

end General

end Tw.RatDarboux

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

open GlobalTheory in
theorem Tw.RatDarboux.exists_rational_darboux : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s → Y.IsSkew σ B r' s' →
    ∃ co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J)) (Fin n × Fin d),
      ∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
        co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F x) = (fun k => algebraMap F (AF F) (y k), fun k => algebraMap F (AF F) (z k)) :=
  _root_.GlobalTheory.RatDarboux.exists_rational_darboux
