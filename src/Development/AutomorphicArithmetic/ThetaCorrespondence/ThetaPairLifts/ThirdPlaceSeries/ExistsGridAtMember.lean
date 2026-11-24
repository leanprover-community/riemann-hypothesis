module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
public import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlaceChoiceLiesOverPair
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallySizesCongruencesHostFactsColumnChoicesStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCharacterGridData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGridUnitGapFieldContainsValuesStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

@[expose] public section



section
section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.HeightCounting.Up.GridLg
theorem exists_large_grid_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ cDep : ℝ, AllSt fun K _ _ _ _ _ x =>
    ∃ G : GlobalTheory.ChiGrid.GridData x.m.z.R.toRealDat.toLevCh ⟨1, cDep, K.s.b⟩, GlobalTheory.BigTop.Fun.FieldHas G (embLL0 (Dof x)) ∧
      (GlobalTheory.BigTop.Fun.lamOf G).Ok ∧ (GlobalTheory.BigTop.Fun.lamOf G).C = cfOf x ∧ (GlobalTheory.BigTop.Fun.lamOf G).q0 = AbsolutelyIrreducibleSpan.q0 (Dof x) := by
  intro _ cDep
  have hd : AllSt fun K _ _ _ _ _ x => ∃ w0, GlobalTheory.LamTie.PlacesOk (Dof x).host (AbsolutelyIrreducibleSpan.q0 (Dof x)) w0 :=
    (Step.of_evLgG GlobalTheory.T.eventually_sizes_congruences_hostFacts_columnChoices).trans (Step.of_all fun K B f T _ hk _ H w _ P x => (H hk T w x.o.Z).2.2.2.2.2.2)
  refine (StepW.and (GlobalTheory.T.exists_grid_unit_gap_field_contains_values cDep) hd).trans (StepW.of_all fun K B f T w _ _ H P x => ?_)
  obtain ⟨G, hG⟩ := H.1 P x
  obtain ⟨w0, h0⟩ := H.2 P x
  exact ⟨G, hG, lamOf_ok _ _ _ _ G w0 h0, x.m.z.lev.C.trans rfl, rfl⟩
end GlobalTheory.HeightCounting.Up.GridLg
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

theorem _root_.GlobalTheory.T.exists_lam_grid_fieldHas_at_member : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ cDep : ℝ, AllSt fun K _ _ _ _ _ x => ∃ G : GlobalTheory.ChiGrid.GridData x.m.z.R.toRealDat.toLevCh ⟨1, cDep, K.s.b⟩, GlobalTheory.BigTop.Fun.FieldHas G (embLL0 (Dof x)) ∧ (GlobalTheory.BigTop.Fun.lamOf G).Ok ∧ (GlobalTheory.BigTop.Fun.lamOf G).C = cfOf x ∧ (GlobalTheory.BigTop.Fun.lamOf G).q0 = AbsolutelyIrreducibleSpan.q0 (Dof x) := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.GridLg.exists_large_grid_alt | exact _root_.GlobalTheory.HeightCounting.Up.GridLg.exists_large_grid_alt | (intros; apply _root_.GlobalTheory.HeightCounting.Up.GridLg.exists_large_grid_alt <;> assumption)
end
end
