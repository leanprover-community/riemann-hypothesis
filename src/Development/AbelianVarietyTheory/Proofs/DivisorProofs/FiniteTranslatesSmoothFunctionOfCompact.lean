module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrowthOfTame
import GroundTheory.AutomorphicForms.LocallyProfinite
import GroundTheory.AutomorphicForms.ReductionBlock
import GroundTheory.GlobalFields.KummerTheory.LocalIndex

@[expose] public section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

namespace GlobalTheory

theorem finite_translates_of_isCompact (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]
    (a : ℕ) (φ : Sm E a) (h : IsOpen {k | finRep E a k φ = φ})
    (Kf : Set (GL (Fin a) (Af E))) (hK : IsCompact Kf) :
    ∃ S : Finset (GL (Fin a) (Af E)), ∀ f ∈ Kf, ∃ f' ∈ S,
      finRep E a f φ = finRep E a f' φ := by
  have hn : ∀ f ∈ Kf, {g | finRep E a g φ = finRep E a f φ} ∈ nhds f := by
    intro f _
    have hc : Continuous (fun g : GL (Fin a) (Af E) => f⁻¹ * g) :=
      continuous_const.mul continuous_id
    have ho := h.preimage hc
    refine Filter.mem_of_superset (ho.mem_nhds ?_) ?_
    · simp
    · intro g hg
      have hg' : finRep E a (f⁻¹ * g) φ = φ := hg
      have e : g = f * (f⁻¹ * g) := by simp
      show finRep E a g φ = finRep E a f φ
      calc finRep E a g φ = finRep E a (f * (f⁻¹ * g)) φ := by rw [← e]
        _ = finRep E a f (finRep E a (f⁻¹ * g) φ) := by rw [map_mul]; rfl
        _ = finRep E a f φ := by rw [hg']
  obtain ⟨t, -, ht⟩ := hK.elim_nhds_subcover (fun f => {g | finRep E a g φ = finRep E a f φ}) hn
  refine ⟨t, fun f hf => ?_⟩
  have := ht hf
  simp only [Set.mem_iUnion] at this
  obtain ⟨f', hf', h'⟩ := this
  exact ⟨f', hf', h'⟩

end GlobalTheory
