module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.GradedCoef
public import Formalism.PeriodIntegrals.LengthPoleInLift
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace PI.PoleLengthCount

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}

theorem AA_le_AAp' (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (Q : LocalPointData G la) (T : ℕ)
    (m : PtsG G la → ℕ) : Q.AA T ≤ Q.AAp T m := by
  refine Submodule.span_mono (Set.image_mono ?_)
  rintro x ⟨hx, hb⟩
  refine ⟨hx, fun β hβ ζ => le_trans (WithTop.coe_le_coe.2 ?_) (hb β hβ ζ)⟩
  dsimp only
  omega

theorem bound (hF : FiltStep) (hM : MonCount) (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO))
    (Q : LocalPointData G la) (T : ℕ) (m : PtsG G la → ℕ)
    (h1 : FiltOk G la T) (h2 : GradedCoef G la Q T m) (h3 : PiBallLen G la Q m) :
    Module.length (Op X la G.N) (↥(Q.AAp T m) ⧸ (Q.AA T).comap (Q.AAp T m).subtype) ≤
      ((Nat.choose (T - 1) (WeightFamilies.dimY D j) * ∑ᶠ ζ, m ζ * fdeg ζ : ℕ) : ℕ∞) := by
  obtain ⟨ψ, hker, hP, hQ⟩ := h2
  refine (hF (Op X la G.N) (WK X la G.w wF (a0 D j T)) (Fk G la T) (a0 D j T) h1.1 h1.2.1 h1.2.2
    (fun k => Vk G la k) ψ hker (Q.AAp T m) (Q.AA T) (fun k => Pk G la Q m k) (fun k => Qk G la Q k)
    (AA_le_AAp' G la Q T m) hP hQ).trans ?_
  refine (Finset.sum_le_sum (fun k _ => (h3 k).le)).trans ?_
  rw [← Nat.cast_sum, Nat.cast_le, ← Finset.sum_mul]
  refine Nat.mul_le_mul_right _ ?_
  by_cases hT : WeightFamilies.dimY D j < T
  · rw [show a0 D j T = T - WeightFamilies.dimY D j from rfl, hM _ _ hT]
  · rw [show a0 D j T = 0 from by simp only [a0]; omega]
    simp

theorem target (hF : FiltStep) (hM : MonCount) (hS : Steps) : PI.LengthPoleInLift := by
  intro D B P j X ka wL wF G la Q S CRm T e c hOk hw hL
  obtain ⟨h1, h2, h3⟩ := hS G la Q S CRm T e c hOk hw hL
  exact bound hF hM G la Q T _ h1 h2 h3

end PI.PoleLengthCount
