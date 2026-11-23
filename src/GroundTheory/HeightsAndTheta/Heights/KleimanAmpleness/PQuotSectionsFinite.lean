module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Statements
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsIdealTwist
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.QuotSectionsFiniteSt
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TildeFiniteSt
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.QuotientH0FiniteHypothesesLine
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

attribute [local instance] MvPolynomial.gradedAlgebra

theorem QuotSectionsFinite.proof (hE : Extension.Statement.{u, w, w})
    (hI : IdealTwistFamily.Statement.{u, w}) (hT : TildeFinite.Statement.{u, w})
    (hQ : QuotientH0Finite.Statement.{u, w, w}) : QuotSectionsFinite.Statement.{u, w} := by
  intro k _ Ω _ _ N x Q J

  let J' : Ideal (Poly k N) := Ideal.span {f | f ∈ J ∧ ∃ e, f.IsHomogeneous e}
  have hJ'hom : ∀ p ∈ J', ∀ d : ℕ, homogeneousComponent d p ∈ J' := by
    have h : J'.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) k) :=
      Ideal.homogeneous_span _ _ fun f hf =>
        ⟨_, (mem_homogeneousSubmodule _ f).mpr hf.2.choose_spec⟩
    exact fun p hp d => homogeneousComponent_mem_of_mem h hp d
  have hforms : ∀ (f : Poly k N) (e : ℕ), f.IsHomogeneous e → (f ∈ J ↔ f ∈ J') := fun f e hf =>
    ⟨fun h => Ideal.subset_span ⟨h, e, hf⟩, fun h => (show J' ≤ J from Ideal.span_le.mpr (by
      intro g hg
      exact hg.1)) h⟩
  have hsys : idealSys x J = idealSys x J' := SubSystem.ext_sub fun I => by
    change idealMod J I = idealMod J' I
    unfold idealMod
    congr 1
    ext a
    constructor <;> rintro ⟨f, s, e, hf, hs, hfe, hse, rfl⟩
    · exact ⟨f, s, e, (hforms f e hfe).mp hf, hs, hfe, hse, rfl⟩
    · exact ⟨f, s, e, (hforms f e hfe).mpr hf, hs, hfe, hse, rfl⟩

  obtain ⟨F, hF, hFfg⟩ := hI k Ω N x Q J' hJ'hom
  obtain ⟨M, -, hM⟩ := hE k Ω N x Ω Q.toSubFamily Q.fg
  obtain ⟨M', -, hM'⟩ := hE k Ω N x Ω F hFfg
  have h0 : M.tildeSys 0 = Q.toSubSystem := SubSystem.ext_sub hM
  have h1 : M'.tildeSys 0 = Q.toSubSystem.twist (idealSys x J) := by
    rw [hsys, ← hF]
    exact SubSystem.ext_sub hM'

  have hle : ∀ I, (Q.toSubSystem.twist (idealSys x J)).sub I ≤ Q.toSubSystem.sub I := by
    intro I
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨q, hq, y, hy, rfl⟩
    refine Submodule.span_induction (p := fun q _ => q • y ∈ Q.sub I) ?_ ?_ ?_ ?_ hq
    · rintro _ ⟨f, s, e, _, hs, hf, hse, rfl⟩
      exact (Q.sub I).smul_mem ⟨_, ⟨f, s, e, hs, hf, hse, rfl⟩⟩ hy
    · rw [zero_smul]; exact Submodule.zero_mem _
    · intro a b _ _ ha hb; rw [add_smul]; exact Submodule.add_mem _ ha hb
    · intro a q _ hq'; rw [smul_assoc]; exact Submodule.smul_mem _ a hq'
  have hH0 : Module.Finite k (Q.toSubSystem.H 0) := by
    rw [← h0]; exact hT k Ω N x M 0 0
  have hH1 : Module.Finite k ((Q.toSubSystem.twist (idealSys x J)).H 1) := by
    rw [← h1]; exact hT k Ω N x M' 1 0
  exact hQ k Ω N x Ω Q.toSubSystem (Q.toSubSystem.twist (idealSys x J)) hle hH0 hH1

end

end GroundTheory.Heights₂.Heights.Kleiman
