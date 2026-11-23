module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatIndLastKerRow
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticePairCharacterIndicatorTransformEqCosetInd
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

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair cosetInd withRow)
open GlobalTheory.FinPl.ExtZero (colFun rowFun)

theorem _root_.GlobalTheory.T.latticePairCharacterIndicator_transform_eq_cosetIndicator : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (q : Unif k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → p.UnitAA → ∀ (χ : AddChar k Circle) (hχ : HasConductor χ 1), p.IsChar ψ χ → ∀ (n : Type) [Fintype n] [DecidableEq n] (L S L'' : HSp D) (ζ : Fin L.rank → D.host.E) (ζ₀ : Fin L''.rank → D.host.E), IsLineVec L ζ → IsLineVec L'' ζ₀ → ∀ (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (lam : D.host.E), Matrix.mulVec τ ζ₀ = lam • ζ → valuation k (p.pr (incA D lam)) = 1 → τ.conjTranspose * (L.gram * τ) = (-(D.host.xi0 * star D.host.xi0)) • L''.gram → ∃ ε : 𝓀[k]ˣ, ∀ (β : Frame p S n) (LS : Lat S), IsSelfDualC S LS → ∀ (Q : Pair k n) (g₁ : WO L S → ℂ) (T₁ : (WO L S → ℂ) →ₗ[ℂ] (WO L S → ℂ)), IsThetaFunO ψ L S g₁ → IsPlaceModel ψ (symplO L S) (heisO ψ L S) p.e (latO L S ((Submodule.span (NumberField.RingOfIntegers D.host.E) {ζ} : Lat L) : Set _) (LS : Set _) (· = p.v)) 1 g₁ T₁ → ∃ (g₃ : WO S L'' → ℂ) (T₃ : (WO S L'' → ℂ) →ₗ[ℂ] (WO S L'' → ℂ)), IsThetaFunO ψ S L'' g₃ ∧ IsPlaceModel ψ (symplO S L'') (heisO ψ S L'') p.e (latO S L'' (LS : Set _) ((Submodule.span (NumberField.RingOfIntegers D.host.E) {ζ₀} : Lat L'') : Set _) (· = p.v)) 1 g₃ T₃ ∧ T₃ (rowFun β ζ₀ (cosetInd q Q.lat (ε • Q).red)) = fun w => T₁ (colFun β ζ (charInd (resChar χ hχ q) Q)) (kap τ S w) := by
  first | exact @GlobalTheory.KapStep.kapStep | exact GlobalTheory.KapStep.kapStep | (intros; apply GlobalTheory.KapStep.kapStep <;> assumption)
