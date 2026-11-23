module

public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.FarRegularity.LKTExists
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.DifferentialBoundedSupport
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.FilterAll
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.WtProj
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKTypeMultiplicityOneUnconditional
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsPowEqZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Finiteness.Lattice
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.DifferentialCommutesWeightOperator

@[expose] public section

open Finset

noncomputable section

namespace GlobalTheory.CompanionTheory.RgExhVanKG

open CompanionTheory.D.LK
open CompanionTheory.D.LK.Car
open CompanionTheory.RgExh.U
open Formalism.REAL (GlRel KHighest IsWeight CasK)
open PI.UpqRep (rhoC nsq)
open CompanionTheory.D.DSIC (KRel KUnit KStab)

theorem vanKG_of (hN : NumKG) : VanKG := by
  have hC : COK := cok_of hGenCO
  have hP : WtProj := GlobalTheory.CompanionTheory.LKWtProj.wtProj
  have hM : WtMajor := GlobalTheory.CompanionTheory.KWeightMajor.wtMajor_of CompanionTheory.D.DSIC.hLowSpan
  intro n ε γ lev V _ _ E hg hE hU hF hmin B j z hB hBU hz hwt hb
  set τ := xv ε γ with hτ
  apply exists_boundary_of_weight_obstruction hC hP hM ε E hE hU hF B j τ z hz hwt hb
  intro A hA ν y hy0 hy hd hc hnorm
  have hA1 := (hz A hA).1
  refine absurd (hmin ν y hy0 hy) (not_le.2 (hN n ε γ lev ν B (A.filter (cpt ε)) hg hB
    (fun i hi => ⟨(mem_filter.1 (hA1.symm ▸ hi :)).2, hBU i hi⟩) (fun i hi => (mem_filter.1 hi).2) hd (fun w hw' => ?_) ?_))
  · convert hc w hw' using 2
    funext c
    simp only [Pi.sub_apply, wt_split (ε := ε) A, hA1, hτ]
    ring
  · rw [← hnorm]
    congr 1
    abel

end GlobalTheory.CompanionTheory.RgExhVanKG
