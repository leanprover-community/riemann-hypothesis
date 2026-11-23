module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StInterNumEventual
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StInterNumAdditive
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StInterNumCut
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StInterNumPointDeg
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistAlg
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.UniformSpace.Uniformizable
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

section Symmetry

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem tensorSub_eq_foldl_map {n : ℕ} (L : Fin n → SubSystem S x Ω) (T : Finset (Fin n)) :
    tensorSub L T = (((List.finRange n).filter (· ∈ T)).map L).foldl
      (fun F Q => F.twist Q) (twistSys S x 0) := by
  unfold tensorSub
  rw [List.foldl_map]

theorem tensorSub_comp_perm {n : ℕ} (L : Fin n → SubSystem S x Ω) (σ : Equiv.Perm (Fin n))
    (T : Finset (Fin n)) :
    tensorSub (fun i => L (σ i)) T = tensorSub L (T.map σ.toEmbedding) := by
  rw [tensorSub_eq_foldl_map, tensorSub_eq_foldl_map]
  have hp : (((List.finRange n).filter (· ∈ T)).map σ).Perm
      ((List.finRange n).filter (· ∈ T.map σ.toEmbedding)) := by
    rw [List.perm_ext_iff_of_nodup (((List.nodup_finRange n).filter _).map σ.injective)
      ((List.nodup_finRange n).filter _)]
    intro a
    simp only [List.mem_map, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq,
      Finset.mem_map_equiv]
    constructor
    · rintro ⟨b, hb, rfl⟩
      simpa using hb
    · intro ha
      exact ⟨σ.symm a, ha, by simp⟩
  have hfun : (fun i => L (σ i)) = L ∘ σ := rfl
  rw [hfun, ← List.map_map]
  exact (hp.map L).foldl_eq' (fun F _ P _ Q => by
    rw [SubSystem.twist_assoc, SubSystem.twist_comm F, ← SubSystem.twist_assoc]) _

theorem interSum_comp_perm (pp : Ideal (Poly S N)) {n : ℕ} (L : Fin n → SubSystem S x Ω)
    (σ : Equiv.Perm (Fin n)) (c : ℕ) :
    interSum pp (fun i => L (σ i)) c = interSum pp L c := by
  unfold interSum
  refine Fintype.sum_equiv (Equiv.finsetCongr σ) _ _ fun T => ?_
  rw [Equiv.finsetCongr_apply, Finset.card_map, tensorSub_comp_perm]

theorem interNum_comp_perm (pp : Ideal (Poly S N)) {n : ℕ} (L : Fin n → SubSystem S x Ω)
    (σ : Equiv.Perm (Fin n)) :
    interNum pp (fun i => L (σ i)) = interNum pp L := by
  unfold interNum
  congr 1
  funext c
  exact interSum_comp_perm pp L σ c

theorem interSum_eventually_eq_interNum (pp : Ideal (Poly S N)) {n : ℕ} (L : Fin n → SubSystem S x Ω)
    {m : ℤ} (h : ∀ᶠ c : ℕ in atTop, interSum pp L c = m) :
    ∀ᶠ c : ℕ in atTop, interSum pp L c = interNum pp L := by
  have ht : Tendsto (interSum pp L) atTop (nhds m) :=
    tendsto_const_nhds.congr' (h.mono fun _ hc => hc.symm)
  have hm : interNum pp L = m := ht.limUnder_eq
  rw [hm]
  exact h

end Symmetry

theorem GenericPointSectionInput.proof (hE : InterNumEventual.Statement.{u, w})
    (hA : InterNumAdditive.Statement.{u, w}) (hC : InterNumCut.Statement.{u, w})
    (hP : InterNumPointDeg.Statement.{u, w}) : GenericPointSectionInput.Statement.{u, w} := by
  intro k _ Ω _ _ N x
  refine ⟨fun n pp L hW => ?_, fun n pp L σ _ => ?_, fun n pp L i L' L'' hW => ?_,
    fun n pp L Lc s hW hs hne => ?_, fun pp hW => ?_⟩
  · obtain ⟨m, hm⟩ := hE k Ω N x n pp L hW
    exact interSum_eventually_eq_interNum pp _ hm
  · exact interNum_comp_perm pp (fun i => (L i).toSubSystem) σ
  · exact hA k Ω N x n pp L i L' L'' hW
  · exact hC k Ω N x n pp L Lc s hW hs hne
  · exact hP k Ω N x pp hW

end

end GroundTheory.Heights₂.Heights.Kleiman
