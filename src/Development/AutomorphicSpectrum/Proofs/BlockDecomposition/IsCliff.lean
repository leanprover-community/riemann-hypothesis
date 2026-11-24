module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.IsMultZero
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
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.IsCoreMod
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLoc

@[expose] public section

noncomputable section

open Matrix Finset
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.RealCount

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD

variable {n : ℕ}

def m0Z (lam : Fin n → ℤ) : Fin n → ℤ := fun a => 2 * lam a + ((n : ℤ) - 1) - 2 * ((a : ℕ) : ℤ)

def wtR (μ : Fin n → ℤ) : Fin n → ℝ := fun a => (μ a : ℝ)

def DomLE (ν m : Fin n → ℝ) : Prop :=
  (∀ k : ℕ, ∑ a ∈ univ.filter (fun a : Fin n => (a : ℕ) < k), ν a ≤ ∑ a ∈ univ.filter (fun a : Fin n => (a : ℕ) < k), m a) ∧
    ∑ a, ν a = ∑ a, m a

def wtDual (E : KMod n) (μ : Fin n → ℤ) : Submodule ℂ (E.V →L[ℂ] ℂ) where
  carrier := {ξ | ∀ (k : Matrix.unitaryGroup (Fin n) ℂ) (z : Fin n → ℂ), k.1 = diagonal z →
    ξ ∘L E.ρ k⁻¹ = (∏ a, z a ^ μ a) • ξ}
  add_mem' {x y} hx hy k z hk := by
    rw [ContinuousLinearMap.add_comp, hx k z hk, hy k z hk, smul_add]
  zero_mem' k z _ := by simp
  smul_mem' c x hx k z hk := by
    rw [ContinuousLinearMap.smul_comp, hx k z hk, smul_comm]

def IsCliff {ι : Type} [Fintype ι] [DecidableEq ι] (c : Fin n → Fin n → Matrix ι ι ℂ) : Prop :=
  (∀ a b d e, c a b * c d e + c d e * c a b = if a = e ∧ b = d then (2 : Matrix ι ι ℂ) else 0) ∧
    ∀ a b, (c a b)ᴴ = c b a

def spinM {ι : Type} [Fintype ι] [DecidableEq ι] (c : Fin n → Fin n → Matrix ι ι ℂ) (a b : Fin n) : Matrix ι ι ℂ :=
  (1 / 2 : ℂ) • ∑ e, c a e * c e b - if a = b then ((n : ℂ) / 2) • (1 : Matrix ι ι ℂ) else 0

def yF {V : Type} [AddCommGroup V] [Module ℂ V] {ι : Type} [Fintype ι] [DecidableEq ι]
    (Kf : Fin n → Fin n → Module.End ℂ V) (c : Fin n → Fin n → Matrix ι ι ℂ) (a b : Fin n) :
    Module.End ℂ (ι → V) where
  toFun x := fun i => Kf a b (x i) + ∑ j, spinM c a b i j • x j
  map_add' x y := by
    funext i
    simp only [Pi.add_apply, map_add (f := _), smul_add, Finset.sum_add_distrib]
    abel
  map_smul' s x := by
    funext i
    simp only [Pi.smul_apply, map_smul, RingHom.id_apply, smul_add, Finset.smul_sum]
    congr 1
    exact Finset.sum_congr rfl fun j _ => smul_comm _ _ _

end GlobalTheory.CompanionTheory.RealCount
