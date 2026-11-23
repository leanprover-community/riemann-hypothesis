module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormPowLeNormFactorial

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKReal

theorem kummer_mem_Fq_of_mem_GKinf : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e]
    (ϖ : PiSys l e), e + 1 = l ^ a → ∀ k ∈ ϖ.GKinf, ∃ z : Fq l a, z ^ e = 1 ∧ ϖ.kummer k = Fq.val l a z := by
  intro l _ a e _ _ ϖ he k hk
  have hfix := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hk
  have hr : ∀ n, ϖ.ratio k n ^ e = 1 := fun n => by
    have hmem : ϖ.seq n ^ e ∈ ϖ.Kinf := IntermediateField.subset_adjoin _ _ ⟨n, rfl⟩
    refine Subtype.ext ?_
    rw [SubmonoidClass.coe_pow, PiSys.coe_ratio, ← map_pow, div_pow, ← map_pow, hfix _ hmem,
      div_self (pow_ne_zero _ (ϖ.seq_ne_zero n)), map_one]
    rfl
  have hK : ϖ.kummer k ^ e = 1 := Perfection.ext fun n => by
    erw [map_pow, map_one]
    change Ideal.Quotient.mk _ (ϖ.ratio k n) ^ e = 1
    rw [← map_pow, hr, map_one]
  have hmem : ϖ.kummer k ∈ resSub l a := by
    rw [mem_resSub, ← he, pow_succ, hK, one_mul]
  obtain ⟨z, hz⟩ : ∃ z : Fq l a, Fq.val l a z = ϖ.kummer k := ⟨(⟨ϖ.kummer k, hmem⟩ : ↥(resSub l a)), rfl⟩
  refine ⟨z, Fq.val_injective l a ?_, hz.symm⟩
  rw [map_pow, map_one, hz, hK]

end GlobalTheory.BKReal
