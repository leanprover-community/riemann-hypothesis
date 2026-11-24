module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThetaModerateGrowth
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThetaSumRationalPairInvariant
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.ThetaSumAdmissibilityStatement
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section



section
noncomputable section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
namespace PositivityTheory.ThKF0
theorem thetaBasic_of_k (harch : _root_.PositivityTheory.ThKF0.ArchBd_k) : _root_.GlobalTheory.ThK.ThetaBasic_k := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP
  have hS := hP.weil.isUSplitting
  obtain ⟨l, hl, hlt⟩ := (GlobalTheory.T.theta_distribution_nonzero_admissible F (Fin n × Fin d)).2.1
  refine ⟨fun Φ hΦ => ⟨?_, ?_, _root_.PositivityTheory.ThKF0.norm_theta_le_mul_ht_pow_of_isPair harch F E σ B n d X W M χX χW om r s r' s' hP Φ hΦ⟩, ?_⟩
  · refine (hS.cont l hl Φ hΦ).congr fun x => ?_
    simp only [theta]
    exact hlt _ (hS.pres _ _ hΦ)
  · intro γ hγ γ' hγ' g h
    simp only [theta]
    have e : om (γ * g, γ' * h) Φ = om (γ, γ') (om (g, h) Φ) := by
      rw [← Module.End.mul_apply, ← map_mul]; rfl
    rw [e]
    exact _root_.PositivityTheory.ThKF0.thetaSum_rational_pair_invariant F E σ B n d X W M χX χW om r s r' s' hP γ hγ γ' hγ' _ (hS.pres _ _ hΦ)
  · intro φ hφ g h
    obtain ⟨T, hT⟩ := hS.adm (g, h) l hl φ hφ
    refine T.continuous.congr fun f => ?_
    simp only [theta]
    have hm : pureA F (f : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) φ ∈ schA F (Fin n × Fin d) :=
      Submodule.subset_span ⟨f, φ, hφ, rfl⟩
    rw [← hlt _ (hS.pres _ _ hm)]
    exact (hT f).symm
end PositivityTheory.ThKF0
end
end
