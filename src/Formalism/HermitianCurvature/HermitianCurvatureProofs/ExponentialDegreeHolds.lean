module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapRWordsOfParts
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

theorem exponential_degree_holds : FExpDeg := by
  intro k r gens
  induction gens with
  | nil =>
    intro _ t ht
    simp only [fexp, List.mem_singleton] at ht
    subst ht
    simp
  | cons gn gs ih =>
    intro hdeg t ht
    have hgn : gn.1.natDegree ≤ 1 := hdeg gn (by simp)
    have ih' := ih (fun g hg => hdeg g (List.mem_cons_of_mem _ hg))
    simp only [fexp, List.mem_append, List.mem_map, List.mem_flatMap] at ht
    rcases ht with ⟨t', ht', rfl⟩ | ⟨dX, hdX, t', ht', rfl⟩
    · obtain ⟨h1, h2⟩ := ih' t' ht'
      refine ⟨?_, ?_⟩
      · have := Polynomial.natDegree_mul_le (p := gn.1) (q := t'.1)
        simp only [List.length_cons]
        omega
      · intro X hX
        obtain ⟨g, hg, d, hd⟩ := h2 X hX
        exact ⟨g, List.mem_cons_of_mem _ hg, d, hd⟩
    · obtain ⟨h1, h2⟩ := ih' t' ht'
      refine ⟨?_, ?_⟩
      · have := Polynomial.natDegree_C_mul_le dX.1 t'.1
        simp only [List.length_cons]
        omega
      · intro X hX
        rcases List.mem_cons.1 hX with rfl | hX
        · exact ⟨gn, by simp, dX.1, hdX⟩
        · obtain ⟨g, hg, d, hd⟩ := h2 X hX
          exact ⟨g, List.mem_cons_of_mem _ hg, d, hd⟩

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
