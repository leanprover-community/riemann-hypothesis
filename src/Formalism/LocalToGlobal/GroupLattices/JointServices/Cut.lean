module

public import Formalism.LocalToGlobal.GroupLattices.JointServices
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Module NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.DV

noncomputable section

namespace Formalism.L2.G.ServJoint

theorem carrier_sum {O : Type} [CommRing O] {φ : O →+* ℂ} {V : Type} [AddCommGroup V] [Module ℂ V] (M : Rows.OLat O φ V)
    {ι : Type} (S : Finset ι) (f : ι → V) (h : ∀ i ∈ S, f i ∈ M.carrier) : ∑ i ∈ S, f i ∈ M.carrier := by
  classical
  simp only [Rows.OLat.carrier, Set.mem_setOf_eq] at h ⊢
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert a S ha ih =>
    rw [Finset.sum_insert ha]
    obtain ⟨c1, hc1⟩ := h a (Finset.mem_insert_self a S)
    obtain ⟨c2, hc2⟩ := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    refine ⟨c1 + c2, ?_⟩
    rw [hc1, hc2, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    simp [add_smul]

theorem gen_mem_carrier {O : Type} [CommRing O] {φ : O →+* ℂ} {V : Type} [AddCommGroup V] [Module ℂ V] (M : Rows.OLat O φ V)
    {v : V} (hv : v ∈ M.gen) : v ∈ M.carrier := by
  classical
  simp only [Rows.OLat.carrier, Set.mem_setOf_eq]
  refine ⟨fun w => if w = v then 1 else 0, ?_⟩
  rw [Finset.sum_eq_single v (fun b _ hb => by simp [hb]) (fun h => absurd hv h)]
  simp

theorem cutUp_of_stable (D : D7) (μ : D.what₂.Tup)
    (h : ∀ (a : 𝓞 D.what₂.LL), ∀ x ∈ (D.what₂.Mtilde μ).carrier, D.what₂.embLL (a : D.what₂.LL) • x ∈ (D.what₂.Mtilde μ).carrier) :
    CutUp D μ := by
  classical
  unfold CutUp
  rintro x ⟨c, hc⟩ hx0
  have hxM : x ∈ (D.what₂.Mtilde μ).carrier := by
    rw [hc]
    exact carrier_sum _ _ _ (fun w hw => h (c w) w (gen_mem_carrier _ hw))
  refine ⟨{x}, fun _ => 1, ?_, ?_⟩
  · rw [Finset.coe_singleton, Set.singleton_subset_iff]
    exact Set.mem_inter hxM hx0
  · simp

end Formalism.L2.G.ServJoint

end
