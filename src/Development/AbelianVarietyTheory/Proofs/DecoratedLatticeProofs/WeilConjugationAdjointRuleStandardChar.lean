module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConjugateAdjointDagger
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjWeilDatumViaAdjointExchangedPairStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HermitianAdjointSymplecticActionThetaHeisenbergStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsWeilDatumConjNegHermitianSpacesStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaHeisenbergConjugationNegHermitianSpaceStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumUniqueOnThetaFunctions
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.WeilConjAdjoint

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger GlobalTheory.ChiGrid

variable {D : D7} {S T : HSp D}

theorem conjTarget_cj (om : Rep S T) (g : GA D S) (h : GA D T) (f : WO S T → ℂ) :
    conjTarget om (g, negGA T h) (cj id f) = cj id (om (g, h) f) := by
  have := cjEnd_cj (Equiv.refl (WO S T)) (om (g, h)) f
  simpa [conjTarget] using this

theorem conjSource_cj (om : Rep S T) (g : GA D S) (h : GA D T) (f : WO S T → ℂ) :
    conjSource om (negGA S g, h) (cj id f) = cj id (om (g, h) f) := by
  have := cjEnd_cj (Equiv.refl (WO S T)) (om (g, h)) f
  simpa [conjSource] using this

theorem conjAdjoint_cj (om : Rep S T) (g : GA D S) (h : GA D T) (f : WO S T → ℂ) :
    conjAdjoint om (h, g) (cj (dagger T S) f) = cj (dagger T S) (om (g, h) f) :=
  cjEnd_cj (daggerEquiv S T) (om (g, h)) f

theorem conjAdjoint_holds : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ S T : HSp D, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.ConjAdjoint ψ S T := by
  intro D ψ hψ S T
  obtain ⟨hθ, hH⟩ := GlobalTheory.T.thetaHeisenberg_conjugation_negHermitianSpace D ψ hψ S T
  obtain ⟨d1, d2, d3, d4⟩ := GlobalTheory.T.hermitianAdjoint_symplectic_action_theta_heisenberg D ψ hψ S T
  refine ⟨hθ, hH, fun χS χT om H => ?_, fun χS χT om H => ?_, d1, d2, d3, d4, fun χS χT om H => ?_⟩
  · have H1 := (GlobalTheory.T.isWeilDatum_conj_negHermitianSpaces D ψ S T χS χT om H).1
    refine ⟨H1, fun om' H' g h f hf => ?_⟩
    rw [← conjTarget_cj]
    exact GlobalTheory.WeilUniq.weilDatum_unique D ψ hψ S (negSp T) _ _ om' _ H' H1 _ _ ((hθ f).1.2 hf)
  · have H1 := (GlobalTheory.T.isWeilDatum_conj_negHermitianSpaces D ψ S T χS χT om H).2
    refine ⟨H1, fun om' H' g h f hf => ?_⟩
    rw [← conjSource_cj]
    exact GlobalTheory.WeilUniq.weilDatum_unique D ψ hψ (negSp S) T _ _ om' _ H' H1 _ _ ((hθ f).2.2 hf)
  · have H1 := GlobalTheory.T.conj_weil_datum_via_adjoint_exchanged_pair D ψ S T χS χT om H
    refine ⟨H1, fun om' H' g h f hf => ?_⟩
    rw [← conjAdjoint_cj]
    exact GlobalTheory.WeilUniq.weilDatum_unique D ψ hψ T S _ _ om' _ H' H1 _ _ ((d3 f).2 hf)

end GlobalTheory.WeilConjAdjoint
