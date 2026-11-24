module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
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
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.WeylFour

variable {F : Type} [Field F] [NumberField F]

def IsSelfDualFor {v : Pl (F := F)} (χ : AddChar (Fv F v) ℂ) (ν : Measure (Fv F v)) : Prop :=
  ν.IsAddHaarMeasure ∧ ∀ f ∈ SB (Fv F v), ∫ y, (∫ x, f x * χ (x * y) ∂ν) ∂ν = f 0

open Classical in
def measV (ψ : AddChar (AF F) ℂ) (v : Pl (F := F)) : Measure (Fv F v) :=
  if h : ∃ ν, IsSelfDualFor (GlobalTheory.LatVac.psiAt ψ v) ν then h.choose else 0

def fourV (ψ : AddChar (AF F) ℂ) (v : Pl (F := F)) {κ : Type} [Fintype κ] (φ : (κ → Fv F v) → ℂ) (y : κ → Fv F v) : ℂ :=
  ∫ x, φ x * GlobalTheory.LatVac.psiAt ψ v (x ⬝ᵥ y) ∂(Measure.pi fun _ : κ => measV ψ v)


open Classical in
variable (F) in
def measI (κ : Type) [Fintype κ] : Measure (κ → mixedEmbedding.mixedSpace F) :=
  Measure.pi fun _ : κ => (Measure.pi fun _ : {w : InfinitePlace F // w.IsReal} => (volume : Measure ℝ)).prod
    (Measure.pi fun _ : {w : InfinitePlace F // w.IsComplex} => (volume : Measure ℂ))

def eInf {κ : Type} [Fintype κ] (x y : κ → mixedEmbedding.mixedSpace F) : ℂ :=
  Complex.exp (-(2 * Real.pi * Complex.I) * (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (x ⬝ᵥ y) : ℝ))

end GlobalTheory.WeylFour

end
