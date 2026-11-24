module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepKeepsSphericalOfLatticeStabilizer
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
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodModModT
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBottomTriIs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCongLevelIntG
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowBlockIndicatorFromLtIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacTheta

@[expose] public section

open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio


theorem _root_.GlobalTheory.T.weilRep_keeps_spherical_of_lattice_stabilizer : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (om : GlobalTheory.Core.Rk.IP.WRep A B),
  IsWeilDatumO ψ A B χA χB om → ∀ (LA : Lat A) (LB : Lat B), IsSelfDualC A LA → IsSelfDualC B LB →
  ∀ (Sf : Finset (FinPl D)) (g : GA D A), g ∈ openOff A LA Sf → ∀ f, IsThetaFunO ψ A B f → IsSphOff ψ A B LA LB Sf f →
    IsSphOff ψ A B LA LB Sf (om (g, 1) f) := by
  first | exact @GlobalTheory.SphMove.isSphOff_om | exact GlobalTheory.SphMove.isSphOff_om | (intros; apply GlobalTheory.SphMove.isSphOff_om <;> assumption)
