module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyGrid
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallySizesCongruencesHostFactsColumnChoicesStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FcLargeOfSup
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar



namespace GlobalTheory.HeightCounting.Up

theorem nonempty_gridData_allSt : ∀ cDep : ℝ, AllSt fun K _ _ _ _ _ x => Nonempty (GlobalTheory.ChiGrid.GridData x.m.z.R.toRealDat.toLevCh ⟨1, cDep, K.s.b⟩) := by
  intro cDep
  unfold AllSt StepW Step
  refine EvG.imp GlobalTheory.T.eventually_sizes_congruences_hostFacts_columnChoices fun K _ _ _ _ H => large₂.mono (fun B f T _ h hk _ _ w _ P x => ?_) H
  obtain ⟨-, -, -, -, -, -, w0, hP⟩ := h hk T w x.o.Z
  refine GlobalTheory.HeightCounting.Up.ListModel.nonempty_grid w x.o.Z x.m.z ⟨1, cDep, K.s.b⟩ fun k e => ?_
  have hd := hP.distinct
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false] at hd
  fin_cases k
  · exact hd.1 (Or.inr (Or.inr (Or.inr e.symm)))
  · exact hd.2.1 (Or.inr (Or.inr e.symm))

end GlobalTheory.HeightCounting.Up
