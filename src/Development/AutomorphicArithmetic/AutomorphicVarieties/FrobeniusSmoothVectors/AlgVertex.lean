module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AlgDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral
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

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.alg_vertex :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] {F : Frame l (ResidueField O)} {n : ℕ} (C : Type) [CommRing C] [Algebra O C] [IsCO O C] {K : Type} [CommRing K] [Algebra C K] (ρ : NRep F n K), Cone O C ρ → HasVertex (ρ.part C) := by
  intro l _ O _ _ F n C _ _ _ K _ _ ρ hC
  have off : ∀ (L : List (F.G0 × Fin n × Fin n)) (j : ℤ),
      (L.map (fun s => w n s.2.1 - w n s.2.2)).sum = j → j ≠ 0 → ∃ s ∈ L, s.2.1 ≠ s.2.2 := by
    intro L j hL hj
    by_contra h
    push_neg at h
    apply hj
    rw [← hL]
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hx
    rw [h s hs, sub_self]
  constructor
  · intro x hx
    have hle : ρ.mon 0 ⊆ (LinearMap.range (Algebra.linearMap C K) : Set K) := by
      rintro _ ⟨L, hL, rfl⟩
      by_cases hd : ∃ s ∈ L, s.2.1 ≠ s.2.2
      · obtain ⟨c, -, hc⟩ := hC.cyc L hL hd
        exact ⟨c, hc⟩
      · push_neg at hd
        have hm : (L.map (fun s => ρ.r s.1 s.2.1 s.2.2)).prod ∈ (algebraMap C K).rangeS := by
          apply list_prod_mem
          intro y hy
          obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hy
          rw [← hd s hs]
          obtain ⟨c, hc, -⟩ := hC.dg s.1 s.2.1
          exact ⟨c, hc⟩
        obtain ⟨c, hc⟩ := hm
        exact ⟨c, hc⟩
    obtain ⟨c, hc⟩ := Submodule.span_le.2 hle hx
    exact ⟨c, hc⟩
  · intro j hj x hx y hy
    open Pointwise in
    have hle : ρ.mon j * ρ.mon (-j) ⊆
        (Submodule.map (Algebra.linearMap C K) (maximalIdeal C) : Set K) := by
      rintro _ ⟨a, ⟨L1, h1, rfl⟩, b, ⟨L2, h2, rfl⟩, rfl⟩
      obtain ⟨s, hs, hne⟩ := off L1 j h1 hj
      obtain ⟨c, hc, hc'⟩ := hC.cyc (L1 ++ L2)
        (by rw [List.map_append, List.sum_append, h1, h2]; ring) ⟨s, List.mem_append_left _ hs, hne⟩
      refine Submodule.mem_map.2 ⟨c, hc, ?_⟩
      rw [Algebra.linearMap_apply, hc', List.map_append, List.prod_append]
    open Pointwise in
    have hxy : x * y ∈ Submodule.span C (ρ.mon j * ρ.mon (-j)) := by
      rw [← Submodule.span_mul_span]
      exact Submodule.mul_mem_mul hx hy
    obtain ⟨c, hc, hc'⟩ := Submodule.mem_map.1 (Submodule.span_le.2 hle hxy)
    exact ⟨c, hc, hc'⟩
