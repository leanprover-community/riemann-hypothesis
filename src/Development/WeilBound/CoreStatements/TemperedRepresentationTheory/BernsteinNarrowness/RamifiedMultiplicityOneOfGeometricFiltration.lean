module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.FinSplit
public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.RightOnto
public import Development.WeilBound.ThetaLifts.CartanFactorisation.CartanConj
public import Development.WeilBound.ThetaLifts.LocalTheory.UnramifiedDeterminedBySpherical
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinSplitOfNarrow
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Imports
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothCharOfCondLE
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KCoinvOfNarrow
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalMultiplicityOneIrreducibleGL
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SoCoinvOfNarrow
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

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL

namespace PositivityTheory.BernsteinRamification

def NarrowBern : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : ℕ)
    (χ₁ χ₂ : kˣ →* ℂˣ), IsSmoothChar χ₁ → IsSmoothChar χ₂ → IsUnitaryChar χ₁ → IsUnitaryChar χ₂ →
    (a ≠ b ∨ χ₁ ≠ χ₂) → (prod₂ (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).IsIrreducible

theorem narrowBern (hG : GlobalTheory.Published.GeometricLemmaFiltration) : NarrowBern :=
  GlobalTheory.CompanionTheory.SmGL.Bernstein.prod₂_detRep_isIrreducible hG

theorem kCoinv_of_geo (hG : GlobalTheory.Published.GeometricLemmaFiltration) (hD : PositivityTheory.KCo.DictSt) : GlobalTheory.ThK.KCoinv :=
  GlobalTheory.CompanionTheory.KCoNarrow.kCoinv_of_narrow (narrowBern hG) hD

theorem soCoinv_of_geo (hG : GlobalTheory.Published.GeometricLemmaFiltration) (hK : GlobalTheory.ThK.KFin) : PositivityTheory.ThKF.SoCoinv :=
  GlobalTheory.CompanionTheory.SoCoinvNarrow.soCoinv_of_narrow (narrowBern hG) hK

theorem ramifiedMultiplicityOne_of_geometricFiltration (hG : GlobalTheory.Published.GeometricLemmaFiltration) : PositivityTheory.ThKG.Loc.RamifiedMultiplicityOne :=
  GlobalTheory.CompanionTheory.BernNarrow.first_cohomology_ramified_narrow (narrowBern hG)

theorem finRam_of_geo (hG : GlobalTheory.Published.GeometricLemmaFiltration) : PositivityTheory.ThK.FinRam :=
  GlobalTheory.CompanionTheory.SplitNarrow.finRam_of_narrow (narrowBern hG)

theorem finSplit_of_geo (hG : GlobalTheory.Published.GeometricLemmaFiltration) : PositivityTheory.ThK.FinSplit :=
  GlobalTheory.CompanionTheory.BernBridge.Split.finSplit_of_narrow (narrowBern hG)

end PositivityTheory.BernsteinRamification
