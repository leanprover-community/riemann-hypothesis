module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
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
import Mathlib.Tactic.ReduceModChar

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoverRead.Test

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct

variable {D : D7} {T : CoreJ D} {j : ℕ} {σ : T.Q.c.F →+* ℂ}

theorem rd_apply (C : Cover T j σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f₂ : Rul C.d.Xo₂ C.d.c₂) (g : GA D (T.V j σ)) :
    C.rd a f₂ g = C.cc₂ (C.dict₂ g).1 * ((lieFac (T.Q.Dw j) (xiR D) a : ℂ) * T.mu j σ g *
      rdU C.U₂ f₂ (C.dict₂ g).1 (C.dict₂ g).2) := by
  simp only [Cover.rd, Pi.smul_apply, smul_eq_mul, adel_muPin]
  ring

theorem zero_mem_ratForms (C : Cover T j σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) : 0 ∈ C.ratForms a n := by
  refine ⟨0, ⟨Submodule.zero_mem _, by rw [map_zero]; exact Submodule.zero_mem _⟩, ?_⟩
  funext g
  rw [rd_apply, map_zero]
  simp

theorem add_mem_ratForms (C : Cover T j σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) {φ ψ : GA D (T.V j σ) → ℂ}
    (hφ : φ ∈ C.ratForms a n) (hψ : ψ ∈ C.ratForms a n) : φ + ψ ∈ C.ratForms a n := by
  obtain ⟨f, hf, rfl⟩ := hφ
  obtain ⟨f', hf', rfl⟩ := hψ
  refine ⟨f + f', ⟨Submodule.add_mem _ hf.1 hf'.1, by rw [map_add (f := _)]; exact Submodule.add_mem _ hf.2 hf'.2⟩, ?_⟩
  funext g
  simp only [Pi.add_apply, rd_apply, map_add (f := _)]
  ring

theorem smul_mem_ratForms (C : Cover T j σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (x : C.d.c₂.F)
    {φ : GA D (T.V j σ) → ℂ} (hφ : φ ∈ C.ratForms a n) : C.σ₂ x • φ ∈ C.ratForms a n := by
  obtain ⟨f, hf, rfl⟩ := hφ
  refine ⟨x • f, ⟨Submodule.smul_mem _ _ hf.1, by rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hf.2⟩, ?_⟩
  funext g
  simp only [Pi.smul_apply, rd_apply, map_smulₛₗ, smul_eq_mul]
  ring

end GlobalTheory.CoverRead.Test
