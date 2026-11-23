module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyAlgebraMapMemIntegers
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsOpenIsCompactLevelOffFinEmpty
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NsmulProjectionXColumnsMemSelfDualLattice
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
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

@[expose] public section

noncomputable section

namespace GlobalTheory.Core.Rk.IP

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem measurableSet_openOff {D : D7} (A : HSp D) (L : Lat A) (hL : IsSelfDualC A L) (S : Finset (FinPl D)) :
    MeasurableSet (openOff A L S) := by
  have : BorelSpace (GA D A) := ⟨rfl⟩
  have : Countable (FinPl D) := GlobalTheory.AdelicUnitaryTop.countable_heightOneSpectrum D.host.F
  haveI := GlobalTheory.ProjXCols.selfDual_isFullLattice A L hL
  have e : openOff A L S = ⋂ v, ⋂ (_ : v ∉ S),
      (proj D.sp.cm.sig A.gram v) ⁻¹' (stabLoc D.sp.cm.sig A.gram L v : Set _) := by
    ext g; simp [openOff]
  rw [e]
  exact MeasurableSet.iInter fun v => MeasurableSet.iInter fun _ =>
    ((isOpen_stabLoc D.sp.cm.sig A.gram L v).preimage (continuous_proj D.sp.cm.sig A.gram v)).measurableSet

theorem monotone_openOff {D : D7} (A : HSp D) (L : Lat A) : Monotone (openOff A L) :=
  fun _ _ h _ hg v hv => hg v fun h' => hv (h h')

theorem iUnion_openOff {D : D7} (A : HSp D) (L : Lat A) (hL : IsSelfDualC A L) : ⋃ S, openOff A L S = Set.univ := by
  haveI := GlobalTheory.ProjXCols.selfDual_isFullLattice A L hL
  refine Set.eq_univ_of_forall fun g => ?_
  have h := Filter.eventually_cofinite.1 (eventually_proj_mem_stabLoc D.sp.cm.sig A.gram L g)
  exact Set.mem_iUnion.2 ⟨h.toFinset, fun v hv => by_contra fun h' => hv (h.mem_toFinset.2 h')⟩

theorem tendsto_setIntegral_openOff : ∀ (D : D7) (A : HSp D) (L : Lat A), IsSelfDualC A L → ∀ (m : Measure (GA D A)) (F : GA D A → ℂ), Integrable F m → Filter.Tendsto (fun S : Finset (FinPl D) => ∫ g in openOff A L S, F g ∂m) Filter.atTop (nhds (∫ g, F g ∂m)) := by
  intro D A L hL m F hF
  have : Countable (FinPl D) := GlobalTheory.AdelicUnitaryTop.countable_heightOneSpectrum D.host.F
  have h := tendsto_setIntegral_of_monotone (μ := m) (f := F) (measurableSet_openOff A L hL) (monotone_openOff A L)
    hF.integrableOn
  rwa [iUnion_openOff A L hL, Measure.restrict_univ] at h

end GlobalTheory.Core.Rk.IP

end
