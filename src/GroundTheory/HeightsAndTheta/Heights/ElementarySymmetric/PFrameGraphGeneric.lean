module

public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StFrameGraphGeneric
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StFrameImplicitGraph
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

noncomputable section

open MvPolynomial

theorem FrameGraphGeneric.proof (hA : FrameJacobianGeneric.Statement) (hB : FrameImplicitGraph.Statement) :
    FrameGraphGeneric.Statement := by
  intro n d J hJ hd b
  obtain ⟨I₀, f, s, hcard, hfJ, hs, hM, hgen⟩ := hA n d J hJ hd b
  refine ⟨I₀, frameJacobianDet b I₀ f * s, hcard, fun h => (hJ.mem_or_mem h).elim hM hs, ?_⟩
  intro z hz hq
  rw [map_mul] at hq
  set W : Set (EuclideanSpace ℂ (Fin n)) := {x | eval (fun i => x i) s ≠ 0} with hWdef
  have hW : IsOpen W := isOpen_ne_fun ((MvPolynomial.continuous_eval s).comp
    (by fun_prop : Continuous fun x : EuclideanSpace ℂ (Fin n) => fun i => x i)) continuous_const
  obtain ⟨Ω, V, g, hΩ, hV, hzV, hVW, hg, hproj, hgraph⟩ :=
    hB n b I₀ f z (fun k => hz _ (hfJ k)) (left_ne_zero_of_mul hq) W hW (right_ne_zero_of_mul hq)
  refine ⟨Ω, V, g, hΩ, hV, hzV, hg, hproj, ?_⟩
  rw [← hgraph]
  ext x
  simp only [zeroSetEuc, Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hx, hxV⟩
    exact ⟨fun k => hx _ (hfJ k), hxV⟩
  · rintro ⟨hx, hxV⟩
    refine ⟨fun p hp => ?_, hxV⟩
    have hle : Ideal.span (Set.range f) ≤ RingHom.ker (eval fun i => x i) :=
      Ideal.span_le.mpr (by rintro _ ⟨k, rfl⟩; exact RingHom.mem_ker.mpr (hx k))
    have h0 := RingHom.mem_ker.mp (hle (hgen p hp))
    rw [map_mul] at h0
    exact (mul_eq_zero.mp h0).resolve_left (hVW hxV)

end

end GroundTheory.Heights₂.Heights
