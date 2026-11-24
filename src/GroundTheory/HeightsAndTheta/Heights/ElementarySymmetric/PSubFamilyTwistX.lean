module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SubFamilyTwistSt
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSubFamilyTwistPow
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v w

section

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]


omit [Module S E] [IsScalarTower S Ω E] in
theorem SubSystem.twist_sub_fg (F : SubSystem S x E) (Q : SubSystem S x Ω) (I : Chart x)
    (hF : (F.sub I).FG) (hQ : (Q.sub I).FG) : ((F.twist Q).sub I).FG := by
  obtain ⟨sF, hsF⟩ := hF
  obtain ⟨sQ, hsQ⟩ := hQ
  classical
  refine ⟨Finset.image₂ (fun q y => q • y) sQ sF, ?_⟩
  apply le_antisymm
  · rw [Submodule.span_le]
    intro z hz
    rw [Finset.coe_image₂] at hz
    obtain ⟨q, hq, y, hy, rfl⟩ := hz
    exact Submodule.subset_span ⟨q, hsQ ▸ Submodule.subset_span hq, y, hsF ▸ Submodule.subset_span hy, rfl⟩
  · change Submodule.span _ _ ≤ _
    rw [Submodule.span_le]
    rintro _ ⟨q, hq, y, hy, rfl⟩
    rw [← hsQ] at hq
    rw [← hsF] at hy
    refine Submodule.span_induction (p := fun q _ => q • y ∈
      Submodule.span (chartRing S x I) ((Finset.image₂ (fun q y => q • y) sQ sF : Finset E) : Set E)) ?_ ?_ ?_ ?_ hq
    · intro q hq
      refine Submodule.span_induction (p := fun y _ => q • y ∈
        Submodule.span (chartRing S x I) ((Finset.image₂ (fun q y => q • y) sQ sF : Finset E) : Set E)) ?_ ?_ ?_ ?_ hy
      · intro y hy
        exact Submodule.subset_span (by rw [Finset.coe_image₂]; exact ⟨q, hq, y, hy, rfl⟩)
      · rw [smul_zero]; exact Submodule.zero_mem _
      · intro a b _ _ ha hb; rw [smul_add]; exact Submodule.add_mem _ ha hb
      · intro a z _ hz
        rw [Subalgebra.smul_def, smul_comm]
        exact Submodule.smul_mem _ a hz
    · rw [zero_smul]; exact Submodule.zero_mem _
    · intro a b _ _ ha hb; rw [add_smul]; exact Submodule.add_mem _ ha hb
    · intro a q _ hq
      rw [smul_assoc]
      exact Submodule.smul_mem _ a hq

end

theorem SubFamilyTwist.proof : SubFamilyTwist.Statement.{u, v, w} := by
  intro S _ Ω _ _ N x E _ _ _ _ F Q hF
  exact ⟨F.twistFam Q.toSubFamily, rfl, fun I =>
    SubSystem.twist_sub_fg F.toSubSystem Q.toSubSystem I (hF I) (Q.fg I)⟩

end

end GroundTheory.Heights₂.Heights.Kleiman
