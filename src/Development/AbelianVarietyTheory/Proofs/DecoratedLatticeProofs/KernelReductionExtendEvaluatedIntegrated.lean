module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsRead
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LinearMapKillingPartialEvalIntegralKernelTranslaStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LinearMapKillsPartialEvalIntegralKernelOfLawsStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousCharactersLocallyConstantNonarchLocalF
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

namespace GlobalTheory.FlatFactor.KerRedStep

theorem mul_sum_law : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (m m' : Type) [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m'] (M : Type) [AddCommGroup M] [Module ℂ M] (l : SB (Matrix m m' k) →ₗ[ℂ] M) (β : Matrix m m' k) (S : Finset (m × m')), (∀ e ∈ S, ∀ (b : k) (Θ Θ' : SB (Matrix m m' k)), (∀ t, Θ'.1 t = (ψ (b * (t e.1 e.2 - β e.1 e.2)) : ℂ) * Θ.1 t) → l Θ' = l Θ) → ∀ (b : m × m' → k) (Θ Θ' : SB (Matrix m m' k)), (∀ t, Θ'.1 t = (ψ (∑ e ∈ S, b e * (t e.1 e.2 - β e.1 e.2)) : ℂ) * Θ.1 t) → l Θ' = l Θ := by
  intro k _ _ _ _ _ _ ψ ν hψc hψ1 hν m m' _ _ _ _ M _ _ l β S hS b
  have hlc := GlobalTheory.RootEx.OpenKernel.isLocallyConstant_coe_addChar ψ hψc
  induction S using Finset.induction_on with
  | empty =>
    intro Θ Θ' h
    congr 1
    exact Subtype.ext (funext fun t => by simp [h])
  | insert j S hj ih =>
    intro Θ Θ' h
    have hc : Continuous fun t : Matrix m m' k => ∑ e ∈ S, b e * (t e.1 e.2 - β e.1 e.2) :=
      continuous_finsetSum _ fun e _ => continuous_const.mul
        ((continuous_id.matrix_elem _ _).sub continuous_const)
    let Θm : SB (Matrix m m' k) := ⟨fun t => (ψ (∑ e ∈ S, b e * (t e.1 e.2 - β e.1 e.2)) : ℂ) * Θ.1 t,
      (hlc.comp_continuous hc).mul Θ.2.1, Θ.2.2.mul_left⟩
    have h1 : l Θ' = l Θm := hS j (Finset.mem_insert_self j S) (b j) Θm Θ' fun t => by
      rw [h t, Finset.sum_insert hj, AddChar.map_add_eq_mul, Circle.coe_mul, mul_assoc]
    rw [h1]
    exact ih (fun e he => hS e (Finset.mem_insert_of_mem he)) Θ Θm fun t => rfl

theorem trans_sum_law : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (m m' : Type) [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m'] (M : Type) [AddCommGroup M] [Module ℂ M] (l : SB (Matrix m m' k) →ₗ[ℂ] M) (β : Matrix m m' k) (S : Finset (m × m')), (∀ e ∈ S, ∀ (a : k) (Θ Θ' : SB (Matrix m m' k)), (∀ t, Θ'.1 t = Θ.1 (t + Matrix.single e.1 e.2 a)) → l Θ' = l Θ) → ∀ (a : m × m' → k) (Θ Θ' : SB (Matrix m m' k)), (∀ t, Θ'.1 t = Θ.1 (t + ∑ e ∈ S, Matrix.single e.1 e.2 (a e))) → l Θ' = l Θ := by
  intro k _ _ _ _ _ _ ψ ν hψc hψ1 hν m m' _ _ _ _ M _ _ l β S hS a
  induction S using Finset.induction_on with
  | empty =>
    intro Θ Θ' h
    congr 1
    exact Subtype.ext (funext fun t => by simp [h])
  | insert j S hj ih =>
    intro Θ Θ' h
    let c : Matrix m m' k := ∑ e ∈ S, Matrix.single e.1 e.2 (a e)
    let Θm : SB (Matrix m m' k) := ⟨fun t => Θ.1 (t + c),
      Θ.2.1.comp_continuous (continuous_id.add continuous_const),
      Θ.2.2.comp_homeomorph (Homeomorph.addRight c)⟩
    have h1 : l Θ' = l Θm := hS j (Finset.mem_insert_self j S) (a j) Θm Θ' fun t => by
      rw [h t, Finset.sum_insert hj, ← add_assoc]
    rw [h1]
    exact ih (fun e he => hS e (Finset.mem_insert_of_mem he)) Θ Θm fun t => rfl

theorem kerRed_extend : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (m m' : Type) [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m'] (M : Type) [AddCommGroup M] [Module ℂ M] (l : SB (Matrix m m' k) →ₗ[ℂ] M) (β : Matrix m m' k) (ev it ev' it' : Finset (m × m')), ev ⊆ ev' → it ⊆ it' → Disjoint ev' it' → GlobalTheory.FlatFactor.KerRed ν ev it β l → (∀ e ∈ ev', e ∉ ev → ∀ (b : k) (Θ Θ' : SB (Matrix m m' k)), (∀ t, Θ'.1 t = (ψ (b * (t e.1 e.2 - β e.1 e.2)) : ℂ) * Θ.1 t) → l Θ' = l Θ) → (∀ e ∈ it', e ∉ it → ∀ (a : k) (Θ Θ' : SB (Matrix m m' k)), (∀ t, Θ'.1 t = Θ.1 (t + Matrix.single e.1 e.2 a)) → l Θ' = l Θ) → GlobalTheory.FlatFactor.KerRed ν ev' it' β l := by
  intro k _ _ _ _ _ _ ψ ν hψc hψ1 hν m m' _ _ _ _ M _ _ l β ev it ev' it' hev hit hd hK hmul htr
  have hd0 : Disjoint ev it := Finset.disjoint_of_subset_left hev (Finset.disjoint_of_subset_right hit hd)
  have L1 : (∀ e ∈ ev, ∀ (b : k) (Θ Θ' : SB (Matrix m m' k)), (∀ t, Θ'.1 t = (ψ (b * (t e.1 e.2 - β e.1 e.2)) : ℂ) * Θ.1 t) → l Θ' = l Θ) := by
    intro e he b Θ Θ' h
    have he' : e ∉ it := Finset.disjoint_left.mp hd0 he
    have h0 : l (Θ' - Θ) = 0 := hK _ fun t => by
      unfold GlobalTheory.FlatFactor.red
      have hz : ∀ a, (Θ' - Θ).1 (GlobalTheory.FlatFactor.fill ev it β t a) = 0 := by
        intro a
        have hf : GlobalTheory.FlatFactor.fill ev it β t a e.1 e.2 = β e.1 e.2 := by
          simp [GlobalTheory.FlatFactor.fill, he, he']
        simp [h, hf]
      simp [hz]
    rwa [map_sub, sub_eq_zero] at h0
  have hM : (∀ e ∈ ev', ∀ (b : k) (Θ Θ' : SB (Matrix m m' k)), (∀ t, Θ'.1 t = (ψ (b * (t e.1 e.2 - β e.1 e.2)) : ℂ) * Θ.1 t) → l Θ' = l Θ) := by
    intro e he
    by_cases h : e ∈ ev
    · exact L1 e h
    · exact hmul e he h
  have hT : (∀ e ∈ it', ∀ (a : k) (Θ Θ' : SB (Matrix m m' k)), (∀ t, Θ'.1 t = Θ.1 (t + Matrix.single e.1 e.2 a)) → l Θ' = l Θ) := by
    intro e he
    by_cases h : e ∈ it
    · exact GlobalTheory.T.linearMap_killing_partialEvalIntegralKernel_translation_invariant k ψ ν hψc hψ1 hν m m' M l β ev it hd0 hK e h
    · exact htr e he h
  exact GlobalTheory.T.linearMap_kills_partialEvalIntegralKernel_of_laws k ψ ν hψc hψ1 hν m m' M l β ev' it' hd
    (mul_sum_law k ψ ν hψc hψ1 hν m m' M l β ev' hM) (trans_sum_law k ψ ν hψc hψ1 hν m m' M l β it' hT)

end GlobalTheory.FlatFactor.KerRedStep
