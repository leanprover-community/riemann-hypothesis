module

public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Mathlib.Basic.Complex.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL

namespace GlobalTheory.WordGrowth

variable {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
  {π : Representation ℂ G V} {J : Subgroup G}

theorem _root_.GlobalTheory.WordGrowth.exists_average
    {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V]
    [Module ℂ V] {π : Representation ℂ G V} {J : Subgroup G}
    (hπ : _root_.GlobalTheory.PRep.IsSmooth π) (hJ : IsCompact (↑J : Set G)) (u : V) :
          ∃ t ∈ _root_.GlobalTheory.PRep.fixed π J,
            ∀ (f : V →ₗ[ℂ] ℂ),
              (∀ j ∈ J, (f : V → ℂ) (((π : G → V →ₗ[ℂ] V) j : V → V) u) = (f : V → ℂ) u) →
                (f : V → ℂ) t = (f : V → ℂ) u := by

  have hK : IsOpen {g : G | π g u = u} := hπ u
  obtain ⟨F, hF⟩ := hJ.elim_finite_subcover
    (fun j : J => (fun g : G => (j : G)⁻¹ * g) ⁻¹' {g : G | π g u = u})
    (fun j => hK.preimage (continuous_const.mul continuous_id))
    (by
      intro g hg
      exact Set.mem_iUnion.2 ⟨⟨g, hg⟩, by simp⟩)
  have hfin : ((fun g : G => π g u) '' (J : Set G)).Finite := by
    apply (F.finite_toSet.image (fun j : J => π (j : G) u)).subset
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨j, hjF, hj⟩ := Set.mem_iUnion₂.1 (hF hg)
    refine ⟨j, hjF, ?_⟩
    simp only [Set.mem_preimage, Set.mem_setOf_eq] at hj
    show π j u = π g u
    calc π (j : G) u = π j (π ((j : G)⁻¹ * g) u) := by rw [hj]
      _ = π g u := by rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
  set O := hfin.toFinset with hO
  have hmem : ∀ v, v ∈ O ↔ ∃ g ∈ J, π g u = v := by
    intro v
    simp [O]
  have huO : u ∈ O := (hmem u).2 ⟨1, J.one_mem, by simp⟩
  have hcard : (O.card : ℂ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.2 ⟨u, huO⟩).ne'
  refine ⟨(O.card : ℂ)⁻¹ • ∑ v ∈ O, v, ?_, ?_⟩
  · simp only [_root_.GlobalTheory.PRep.fixed, _root_.GlobalTheory.PRep.eig]
    simp
    intro a ha
    congr 1
    apply Finset.sum_nbij' (fun v => π a v) (fun v => π a⁻¹ v)
    · intro v hv
      obtain ⟨g, hg, rfl⟩ := (hmem v).1 hv
      exact (hmem _).2 ⟨a * g, J.mul_mem ha hg, by rw [map_mul, Module.End.mul_apply]⟩
    · intro v hv
      obtain ⟨g, hg, rfl⟩ := (hmem v).1 hv
      exact (hmem _).2 ⟨a⁻¹ * g, J.mul_mem (J.inv_mem ha) hg, by rw [map_mul, Module.End.mul_apply]⟩
    · intro v _
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    · intro v _
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    · intro v _
      rfl
  · intro f hf

    rw [map_smul, map_sum, smul_eq_mul]
    rw [Finset.sum_congr rfl (g := fun _ => f u) ?_]
    · rw [Finset.sum_const, nsmul_eq_mul]
      field_simp
    · intro v hv
      obtain ⟨g, hg, rfl⟩ := (hmem v).1 hv
      exact hf g hg

end GlobalTheory.WordGrowth
