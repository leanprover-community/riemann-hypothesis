module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchInverseOffHypersurface
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StInjectiveHolomorphicInverse
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StProjectionInjectiveOffHypersurface
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Linear

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial

theorem BranchInverseOffHypersurface.proof (hinv : InjectiveHolomorphicInverse.Statement)
    (hproj : ProjectionInjectiveOffHypersurface.Statement) :
    BranchInverseOffHypersurface.Statement := by
  intro σ _ I k hI hk
  obtain ⟨h', hh', hloc⟩ := hproj σ I k hI hk
  refine ⟨h', hh', fun U φ ψ hU hφd hφi hφZ hψ => ?_⟩
  rintro _ ⟨⟨t, ht, rfl⟩, hz⟩
  obtain ⟨W, hWo, hzW, A, hA⟩ := hloc (φ t) (hφZ ht) hz
  have hU'o : IsOpen (U ∩ φ ⁻¹' W) := hφd.continuousOn.isOpen_inter_preimage hU hWo
  have hfd : DifferentiableOn ℂ (fun s => A (φ s)) (U ∩ φ ⁻¹' W) :=
    A.differentiable.differentiableOn.comp (hφd.mono Set.inter_subset_left) (Set.mapsTo_univ _ _)
  have hfi : Set.InjOn (fun s => A (φ s)) (U ∩ φ ⁻¹' W) := fun s hs s' hs' hss' =>
    hφi hs.1 hs'.1 (hA ⟨hφZ hs.1, hs.2⟩ ⟨hφZ hs'.1, hs'.2⟩ hss')
  obtain ⟨hOo, g, hgd, hgf⟩ := hinv k _ _ hU'o hfd hfi
  refine ⟨W ∩ A ⁻¹' ((fun s => A (φ s)) '' (U ∩ φ ⁻¹' W)), hWo.inter (hOo.preimage A.continuous),
    ⟨hzW, t, ⟨ht, hzW⟩, rfl⟩, fun y => g (A y), ?_, ?_⟩
  · exact hgd.comp A.differentiable.differentiableOn fun y hy => hy.2
  · rintro _ ⟨⟨⟨s, hs, rfl⟩, -⟩, hsW, -⟩
    show ψ (φ s) = g (A (φ s))
    rw [hψ s hs, hgf s ⟨hs, hsW⟩]

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
