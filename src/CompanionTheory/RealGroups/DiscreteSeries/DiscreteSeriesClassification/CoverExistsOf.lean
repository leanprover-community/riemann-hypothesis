module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesCoverExistsIff
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
public import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.DiscreteSeriesSU.GapInv
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HarishChandraModulesIndefiniteUnitaryGroupStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsOfIsDSPar
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam

@[expose] public section

noncomputable section

namespace CompanionTheory.RgDs

open Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.CoverDS GlobalTheory.Dec

theorem upqExists_of (hE : DSExists) : GlobalTheory.Published.DiscreteSeriesUpqExists :=
  GlobalTheory.Published.discreteSeriesUpqExists_iff_dsExists.2 hE

theorem exists_of (hE : DSExists) : GlobalTheory.Published.DiscreteSeriesExists :=
  GlobalTheory.Published.discreteSeriesExists_iff_upq.2 (upqExists_of hE)

theorem coverExists_of (hE : DSExists) : GlobalTheory.Published.DiscreteSeriesCoverExists :=
  GlobalTheory.Published.CoverSeries.of_upq (upqExists_of hE) (fun p q h T U hU => ((GlobalTheory.T.harishChandraModules_indefiniteUnitaryGroup.1 p q h T).1 U hU).2.1)

def ClassUsed : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam →
    ∃ (G : Type) (_ : NormedAddCommGroup G) (_ : InnerProductSpace ℂ G)
      (π : Matrix (Fin n) (Fin n) ℂ → (G →L[ℂ] G)), GlobalTheory.DSId.IsHCDS ε lam π ∧
      ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),
        Formalism.MainNotions.S.IsDS ε lam σ → UEquiv ε σ π

theorem classUsed_of (hE : DSExists) (hK : KTypesAbove) (hI : DSInfChar) : ClassUsed := by
  intro n ε lam hl
  obtain ⟨G, _, _, π, hπ⟩ := hE n ε lam hl
  refine ⟨G, _, _, π, ⟨⟨hπ.1, hπ.2.1, hπ.2.2.1, hπ.2.2.2.1, hπ.2.2.2.2.1⟩, hI n ε lam G π hl hπ, ?_,
    hK n ε lam G π hl hπ⟩, fun H _ _ σ hσ => CompanionTheory.DiscreteSeriesGap.GapInv.dsUnique_dec n ε lam H σ G π hl hσ hπ⟩
  obtain ⟨S, hS⟩ := hπ.2.2.2.2.2.1
  exact ⟨S, hS, fun S' hS' => CompanionTheory.DiscreteSeriesGap.GapInv.lowKMultOne_dec n ε lam G π hl hπ S' S hS' hS⟩

end CompanionTheory.RgDs
