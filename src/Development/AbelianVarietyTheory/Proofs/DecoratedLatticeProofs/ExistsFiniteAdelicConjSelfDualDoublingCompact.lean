module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledCompactSubgroupConjHermitianSpaceStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnitaryFiniteAdelicMapSelfDualCompletionsStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLocalLatticeIffOfFiniteAdelicCompletionMapStatement
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero

@[expose] public section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.LatMove

theorem exists_conj_KAd_of_selfDual : ∀ (D : D7) (A : HSp D) (L L' : Lat A), IsSelfDualC A L → IsSelfDualC A L' →
    ∃ k ∈ GfC A, ∀ (a : GL (Fin A.rank) (AE D)) (x : GA D (dblSp A)),
      x ∈ KAd D.sp.cm.sig (dblSp A).gram L' a ↔ (io A (k, k))⁻¹ * x * io A (k, k) ∈ KAd D.sp.cm.sig (dblSp A).gram L a := by
  intro D A L L' hL hL'
  obtain ⟨b, hb, hbL⟩ := GlobalTheory.T.exists_unitary_finiteAdelic_map_selfDual_completions D A L L' hL hL'
  let y : GFin D.sp.cm.sig A.gram := ⟨b, hb⟩
  have hk : ofFin D.sp.cm.sig A.gram y ∈ GfC A := by
    show infHom A (ofFin D.sp.cm.sig A.gram y) = 1
    have := projInf_ofFin D.sp.cm.sig A.gram y
    exact congrArg (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig A.gram) this
  refine ⟨ofFin D.sp.cm.sig A.gram y, hk, GlobalTheory.T.doubledCompactSubgroup_conj_hermitianSpace D A L L' _ hk ?_⟩
  intro v z
  rw [proj_ofFin]
  exact GlobalTheory.T.mem_localLattice_iff_of_finiteAdelic_completion_map D.host.F D.host.E A.rank L L' hL.1.fg hL'.1.fg b hbL v z

end GlobalTheory.Core.Rk.LatMove
