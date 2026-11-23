module

public import Development.DiscreteGroups.GlobalIrreducibility.LocTypeOfSerParamLe
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NeZeroOfMemRoots
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

open Polynomial GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys

noncomputable section

namespace DiscreteGroups.sglob.DzType.Rt


open GlobalTheory.SerSys.LabLoc in
theorem actK_e_eq_self_le : ∀ (g : ℕ) [Fact g.Prime] (S : Sys g) (τ : Formalism.CyclotomicNorms.Fbar g →* ℂ) (ine : ∀ n, QRep g n → ℂ[X]) (b : ℕ), Set.InjOn τ {x | x ≠ 0} → DiscreteGroups.sglob.DzType.Rt.SerParamLe b S.e τ ine → ∀ (n : ℕ), n ≤ b → ∀ (π : QRep g n), IrrSm π → ∀ f : (ZMod g)[X], f.Monic → f.coeff 0 ≠ 0 → ine n π = ((Formalism.CyclotomicNorms.rootsBar f).map fun x => X - C (τ x)).prod → ∀ v ∈ fixK1 π.ρ, actK π.ρ (S.e n f) v = v := by
  intro g _ S τ ine b hτ hP n hn π hπ f hm h0 hine v hv
  have key : ∀ f', actK π.ρ (S.e n f') v ≠ 0 → f' = f := by
    intro f' hf'
    have hne : S.e n f' ≠ 0 := fun e => hf' (by rw [e]; simp [actK])
    obtain ⟨hm', -, h0'⟩ := S.label n f' hne
    have e1 := (hP n hn π hπ f' ⟨v, hv, hf'⟩).symm.trans hine
    have e1' : (((Formalism.CyclotomicNorms.rootsBar f').map τ).map fun a => X - C a).prod =
        (((Formalism.CyclotomicNorms.rootsBar f).map τ).map fun a => X - C a).prod := by
      rw [Multiset.map_map, Multiset.map_map]; exact e1
    have e2 := congrArg Polynomial.roots e1'
    rw [roots_multiset_prod_X_sub_C, roots_multiset_prod_X_sub_C] at e2
    exact eq_of_roots_eq hm' hm (map_eq_map hτ (fun x hx => ne_zero_of_mem_roots h0' hx)
      (fun x hx => ne_zero_of_mem_roots h0 hx) e2)
  obtain ⟨T, hT⟩ := S.sum n
  have hv1 : v = ∑ f' ∈ T, actK π.ρ (S.e n f') v := by
    conv_lhs => rw [← actK_one_of_mem π.ρ hv, ← hT, actK_finset_sum]
    simp
  have hv2 : ∑ f' ∈ T, actK π.ρ (S.e n f') v = if f ∈ T then actK π.ρ (S.e n f) v else 0 := by
    split_ifs with hfT
    · rw [Finset.sum_eq_single f]
      · intro f' _ h; by_contra h'; exact h (key f' h')
      · intro h; exact absurd hfT h
    · refine Finset.sum_eq_zero fun f' hf' => ?_
      by_contra h'; exact hfT (key f' h' ▸ hf')
  split_ifs at hv2 with hfT
  · exact (hv1.trans hv2).symm
  · have : v = 0 := hv1.trans hv2
    rw [this, map_zero]

end DiscreteGroups.sglob.DzType.Rt

end
