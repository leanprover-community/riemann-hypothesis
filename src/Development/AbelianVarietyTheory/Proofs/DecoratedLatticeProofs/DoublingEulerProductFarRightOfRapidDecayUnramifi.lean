module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingEulerProductFarRight
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingSphericalFactorizationOfWeilDualPairStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SphericalParameterBoundNonsplitPlacesStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SphericalParameterBoundSplitPlace
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedDoublingIntegralInertAdelic
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedDoublingIntegralSplitPlaceAdelic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnramifiedDoublingIntegralInertPlace
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PrinInf
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ParamsEx

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh

namespace GlobalTheory.Core.Rk.IP

theorem eulerRight_of_unramifiedDoubling : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.UnramifiedDoublingGL →
    ∀ D : D7, GlobalTheory.Core.Rk.IP.EulerRight D := by
  intro p2 p6 D
  have hU := GlobalTheory.InertZeta.unramDoublingInert
  have hPBi : ParamBoundOn D fun v => ¬ Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v := GlobalTheory.T.sphericalParameterBound_nonsplit_places hU D
  have hPB : ParamBoundOn D (fun _ => True) := by
    intro A L hL v _
    by_cases h : Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v
    · exact GlobalTheory.Core.Rk.BdSplit.paramBound_split D A L hL v h
    · exact hPBi A L hL v h
  have hLZ : LocalZetaOn D (fun _ => True) := by
    intro A L hL χ b hχ hr v _
    by_cases h : Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v
    · exact GlobalTheory.Core.Rk.IP.localZetaOn_split p6 D A L hL χ b hχ hr v h
    · exact GlobalTheory.LocZetaInertAd.localZetaOn_inert hU D hPBi A L hL χ b hχ hr v h
  exact GlobalTheory.Core.Rk.EulerProd.eulerRight p2 D (GlobalTheory.T.doublingSphericalFactorization_of_weilDualPair GlobalTheory.weilRepresentationUnitaryPair D) hLZ hPB

end GlobalTheory.Core.Rk.IP
