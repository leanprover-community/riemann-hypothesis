module

public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedSmooth
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ComplexDerivativeRightDerivativeCommutator
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspFormAvgTypeOtherPlace
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
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

namespace GlobalTheory.PlaceComm

theorem place_comm : ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D),
    IsInfFam (D := D) θ → ∀ τ τ' : D.what₂.Tau, τ ≠ τ' →
    (∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ h ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ'), ∀ f : GA D V → ℂ,
      rTr V (atTau θ V τ g) (rTr V (atTau θ V τ' h) f) = rTr V (atTau θ V τ' h) (rTr V (atTau θ V τ g) f)) ∧
    (∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ X ∈ lieAt V τ', ∀ f : GA D V → ℂ,
      Rder θ V τ' X (rTr V (atTau θ V τ g) f) = rTr V (atTau θ V τ g) (Rder θ V τ' X f)) ∧
    (∀ X ∈ lieAt V τ, ∀ Y ∈ lieAt V τ', ∀ f : GA D V → ℂ, IsAutFunSm θ V f →
      Rder θ V τ X (Rder θ V τ' Y f) = Rder θ V τ' Y (Rder θ V τ X f)) := by
  intro D θ V hθ τ τ' hne
  refine ⟨fun g hg h hh f => ?_, fun g hg X hX f => ?_, fun X hX Y hY f hf => ?_⟩
  · funext x
    simp only [rTr]
    rw [mul_assoc, mul_assoc, GlobalTheory.AvgOtherPlace.atTau_comm hθ (Ne.symm hne) hg hh]
  · rw [GlobalTheory.Mem.RealTranslate.Rder_rTr hθ (GlobalTheory.Mem.RealTranslate.isRealPt_atTau hθ τ hg) hX,
      GlobalTheory.AvgOtherPlace.adAt_atTau_of_ne hθ (Ne.symm hne) hg]
  · exact GlobalTheory.DerBracket.Rder_comm hθ hf.smooth hne hX hY

end GlobalTheory.PlaceComm

end
