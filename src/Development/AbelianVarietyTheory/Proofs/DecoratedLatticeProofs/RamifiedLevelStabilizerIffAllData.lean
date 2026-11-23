module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SOnCols
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

theorem ramIff_all : ∀ D : D7, RamIff D := by
  intro D k _ _ _ _ p n _ _ S β P g hg φ
  letI := Fintype.ofFinite 𝓀[k]ˣ
  have rp : ∀ x (F : GA D S → ℂ), β.rep x F = rTrans (β.gl x) F := fun _ _ => rfl
  rw [finsum_eq_sum_of_fintype]
  constructor
  · rintro ⟨Φ, ⟨he, hr, hc⟩, rfl⟩
    refine ⟨hc P, fun x hx => ?_, ?_⟩
    · rw [← rp, ← he x P, hx]
    · rw [← (mem_Mram Φ).1 hr P]
      exact Finset.sum_congr rfl fun s _ => by rw [← rp, ← he, hg]
  · rintro ⟨hc, hs, h0⟩
    let v : levelVec β.rep P := ⟨φ, fun x hx => hs x hx⟩
    have hv : ∀ x : GL n k, formOf β.rep P v (x • P) = β.rep x φ := formOf_smul β.rep P v
    refine ⟨formOf β.rep P v, ⟨formOf_mem _ _ _, (mem_Mram _).2 fun Q => ?_, fun Q => ?_⟩, by simpa using hv 1⟩
    · obtain ⟨h, rfl⟩ := MulAction.exists_smul_eq (GL n k) P Q
      have : ∀ s : 𝓀[k]ˣ, formOf β.rep P v (s • h • P) = β.rep h (rTrans (β.gl (g s)) φ) := by
        intro s
        rw [← smul_comm h s P, ← hg, smul_smul, hv, map_mul, Module.End.mul_apply, rp (g s)]

      rw [Finset.sum_congr rfl fun s _ => this s, ← map_sum, h0, map_zero]
    · obtain ⟨h, rfl⟩ := MulAction.exists_smul_eq (GL n k) P Q
      rw [hv, rp]
      exact ⟨fun γ hγ y => by simp only [rTrans]; rw [mul_assoc, hc.1 γ hγ], hc.2.comp (continuous_id.mul continuous_const)⟩

end GlobalTheory.SeeSaw

end
