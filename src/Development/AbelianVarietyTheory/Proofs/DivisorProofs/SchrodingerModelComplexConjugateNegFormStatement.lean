module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerModelComplexConjugateNegForm
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsApprox
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCongLevelIntG

@[expose] public section

open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead


theorem _root_.GlobalTheory.T.schrodingerModel_complexConjugate_negForm : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A WW : HSp D) (e : AE D) (ΛA : Set (Fin A.rank → D.host.E))
  (ΛW : Set (Fin WW.rank → D.host.E)) (vac Φ f : WO A WW → ℂ),
  IsThetaAt ψ (symplO (GlobalTheory.Grid.neg A) WW) (heisO ψ (GlobalTheory.Grid.neg A) WW) e (latO (GlobalTheory.Grid.neg A) WW ΛA ΛW fun _ => True) 1 vac Φ f →
  ∃ Tm : (WO A WW → ℂ) →ₗ[ℂ] (WO A WW → ℂ),
    IsPlaceModel ψ (symplO A WW) (heisO ψ A WW) e (latO A WW ΛA ΛW fun _ => True) 1 (fun w => starRingEnd ℂ (vac w)) Tm ∧
      (fun w => starRingEnd ℂ (f w)) = Tm (fun w => starRingEnd ℂ (Φ w)) := by
  first | exact @GlobalTheory.ConjSchr.conj_schroedinger_neg | exact GlobalTheory.ConjSchr.conj_schroedinger_neg | (intros; apply GlobalTheory.ConjSchr.conj_schroedinger_neg <;> assumption)
