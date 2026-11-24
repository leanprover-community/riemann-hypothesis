module

public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CoverDiscreteSeriesUnitarilyEquivOfSameParamStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsParamCoverDiscreteSeriesStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HarishChandraModulesIndefiniteUnitaryGroupStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasDiscreteSeriesKTypesOfHasParamCoverStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ConsequencesOfDsClass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsOfIsDSPar
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

open Formalism.BasicNotions.TH GlobalTheory.RealPar

noncomputable section

namespace GlobalTheory.CoverDS

theorem discreteSeriesCover_of_classification :
    GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.DiscreteSeriesCover := by
  intro hcl
  obtain ⟨hExists, hExhaust, hUnique, hInfChar, hLowK, hKTypes, -⟩ :=
    GlobalTheory.ClassificationConsequences.consequences_of_dsClass
      (GlobalTheory.Published.discreteSeriesClassification_iff.1 hcl)
  have hC : GlobalTheory.Published.DiscreteSeriesCoverExists :=
    GlobalTheory.Published.CoverSeries.of_upq
      (GlobalTheory.Published.discreteSeriesUpqExists_iff_dsExists.2 hExists)
      (fun p q h T U hU => ((GlobalTheory.T.harishChandraModules_indefiniteUnitaryGroup.1 p q h T).1 U hU).2.1)
  intro p q hn T
  choose D hD using fun lam : {lam : Ix p q → ℚ // IsParam lam} => hC p q T lam.1 lam.2
  refine ⟨D, ?_, ?_⟩
  · intro lam
    exact GlobalTheory.T.hasDiscreteSeriesKTypes_of_hasParam_cover
      hLowK hKTypes hInfChar p q hn T (D lam) lam.1 lam.2 (hD lam)
  · intro R
    obtain ⟨lam, hl, hR⟩ := GlobalTheory.T.exists_param_coverDiscreteSeries hExhaust p q hn T R
    exact ⟨⟨lam, hl⟩, GlobalTheory.T.coverDiscreteSeriesUnitarilyEquiv_of_sameParam
      hUnique p q hn T R (D ⟨lam, hl⟩) lam hl hR (hD ⟨lam, hl⟩)⟩

end GlobalTheory.CoverDS

end
