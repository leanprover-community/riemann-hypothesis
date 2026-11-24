module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Mathlib.RingTheory.PiTensorProduct
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

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.RealLift

namespace GlobalTheory.KFixIrr

variable (ι : Type) [Fintype ι] (P Q R S : ℕ)

def degLE (k : ℕ) : Submodule ℂ (⨂[ℂ] _ : ι, Formalism.BasicNotions.TH.Pol P Q R S) :=
  Submodule.span ℂ {T | ∃ f : ι → Formalism.BasicNotions.TH.Pol P Q R S, ∑ w, (f w).totalDegree ≤ k ∧ T = PiTensorProduct.tprod ℂ f}

def chiPart [DecidableEq ι] (x : ι → ℚ) : Submodule ℂ (⨂[ℂ] _ : ι, Formalism.BasicNotions.TH.Pol P Q R S) :=
  ⨅ w : ι, ⨅ X : {X : Mat P Q // IsKC X},
    LinearMap.ker (atPl (V := fun _ : ι => Formalism.BasicNotions.TH.Pol P Q R S) w (fockAct1 P Q R S X.1) - ((x w : ℂ) * X.1.trace) • 1)

variable {ι P Q R S}

theorem mem_chiPart [DecidableEq ι] (x : ι → ℚ) (T : ⨂[ℂ] _ : ι, Formalism.BasicNotions.TH.Pol P Q R S) :
    T ∈ chiPart ι P Q R S x ↔ ∀ w (X : Mat P Q), IsKC X →
      atPl (V := fun _ : ι => Formalism.BasicNotions.TH.Pol P Q R S) w (fockAct1 P Q R S X) T = ((x w : ℂ) * X.trace) • T := by
  simp only [chiPart, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply, sub_eq_zero, Subtype.forall]

theorem degLE_mono : Monotone (degLE ι P Q R S) := fun _ _ h =>
  Submodule.span_mono fun _ ⟨f, hf, e⟩ => ⟨f, hf.trans h, e⟩

theorem tprod_mem_degLE (f : ι → Formalism.BasicNotions.TH.Pol P Q R S) {k : ℕ} (h : ∑ w, (f w).totalDegree ≤ k) :
    PiTensorProduct.tprod ℂ f ∈ degLE ι P Q R S k :=
  Submodule.subset_span ⟨f, h, rfl⟩

end GlobalTheory.KFixIrr

end
