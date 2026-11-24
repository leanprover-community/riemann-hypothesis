module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussZero
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField

namespace GlobalTheory.HeckePoisson

variable {K : Type} [Field K] [NumberField K] {I : Type}

def embA (φ : I → K →+* ℂ) : 𝓞 K →+ EuclideanSpace ℂ I where
  toFun α := WithLp.toLp 2 (GlobalTheory.HeckeTheta.emb φ (α : K))
  map_zero' := by ext i; simp [GlobalTheory.HeckeTheta.emb]
  map_add' a b := by ext i; simp [GlobalTheory.HeckeTheta.emb]

def lat (φ : I → K →+* ℂ) (M : Ideal (𝓞 K)) : Submodule ℤ (EuclideanSpace ℂ I) :=
  AddSubgroup.toIntSubmodule (M.toAddSubgroup.map (embA φ))

theorem embA_apply (φ : I → K →+* ℂ) (α : 𝓞 K) (i : I) : embA φ α i = φ i (α : K) := rfl

theorem mem_lat {φ : I → K →+* ℂ} {M : Ideal (𝓞 K)} {x : EuclideanSpace ℂ I} :
    x ∈ lat φ M ↔ ∃ μ ∈ M, embA φ μ = x := by
  show x ∈ M.toAddSubgroup.map (embA φ) ↔ _
  rw [AddSubgroup.mem_map]
  rfl

def kappa [Fintype I] (n : I → ℤ) : ℂ := ((2 : ℂ) ^ Fintype.card I)⁻¹ * (-Complex.I) ^ (∑ i, (n i).natAbs)

end GlobalTheory.HeckePoisson
