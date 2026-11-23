module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.MonoCount
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace PoleLengthBounds

theorem sum_mon_le (hM : MonoCount) (D : D7) (j T n : ℕ) :
    ∑ k ∈ Finset.range (a0 D j T), (mon D j k).card * n ≤ Nat.choose (T - 1) (WeightFamilies.dimY D j) * n := by
  rw [← Finset.sum_mul]
  by_cases h : WeightFamilies.dimY D j < T
  · rw [show a0 D j T = T - WeightFamilies.dimY D j from rfl, hM _ _ h]
  · have h0 : a0 D j T = 0 := by
      show T - WeightFamilies.dimY D j = 0
      omega
    simp [h0]

theorem lenBase_of (hF : FiltLenGr) (hM : MonoCount) (hK : FkFilt) (hG : GrBound) :
    ∀ {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j},
      LenBase (X := X) (ka := ka) (wL := wL) (wF := wF) := by
  intro D B P j X ka wL wF G la Q S CRm T c hOk hth hw hI
  obtain ⟨hA, h0, hT⟩ := hK G la T
  obtain ⟨φ, Pk, Qk, hker, hP, hQ, hL⟩ := hG G la Q S CRm T c hOk hth hw hI
  have key := hF (Op X la G.N) (WK X la G.w wF (a0 D j T)) (Fk G la T) (a0 D j T) hA h0 hT
    (fun _ => Vg G la) φ hker (Q.AA T) (firstLength_le_prime_bound G la T ⊓ Q.AA T) Pk Qk inf_le_right hP hQ
  have e : (firstLength_le_prime_bound G la T ⊓ Q.AA T).comap (Q.AA T).subtype = (firstLength_le_prime_bound G la T).comap (Q.AA T).subtype := by
    ext x
    simp [x.2]
  rw [e] at key
  refine key.trans ?_
  calc ∑ k ∈ Finset.range (a0 D j T), Module.length (Op X la G.N) (↥(Pk k) ⧸ (Qk k).comap (Pk k).subtype)
      ≤ ∑ k ∈ Finset.range (a0 D j T), ((((mon D j k).card * Q.Ila.toNat : ℕ)) : ℕ∞) :=
        Finset.sum_le_sum fun k hk => hL k (Finset.mem_range.1 hk)
    _ = ((∑ k ∈ Finset.range (a0 D j T), (mon D j k).card * Q.Ila.toNat : ℕ) : ℕ∞) := by
        push_cast; rfl
    _ ≤ _ := by exact_mod_cast sum_mon_le hM D j T Q.Ila.toNat

end PoleLengthBounds
