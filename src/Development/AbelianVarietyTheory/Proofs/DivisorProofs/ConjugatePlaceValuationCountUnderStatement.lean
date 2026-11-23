module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinPt
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugatePlaceValuationCountUnder
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodModModT
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IpEqZeroOfHeisEigen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCongLevelIntG
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
open scoped nonZeroDivisors
open GlobalTheory.CosetOrth


theorem _root_.GlobalTheory.T.conjugatePlace_valuation_count_under : ∀ (D : D7), ∀ w : HeightOneSpectrum (𝓞 D.host.E), ∃ w' : HeightOneSpectrum (𝓞 D.host.E), w'.asIdeal = D.host.conj • w.asIdeal ∧
    (∀ x : Formalism.MainNotions.StandardLatticesGL3.AE D, Valued.v (GlobalTheory.BotFormula.toFinE D (Formalism.MainNotions.StandardLatticesGL3.sgA D x) w') = Valued.v (GlobalTheory.BotFormula.toFinE D x w)) ∧
    (∀ 𝔞 : Ideal (𝓞 D.host.E), 𝔞 ≠ ⊥ → FractionalIdeal.count D.host.E w' ((D.host.conj • 𝔞 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) =
      FractionalIdeal.count D.host.E w (𝔞 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)) ∧
    ∀ w'' : HeightOneSpectrum (𝓞 D.host.E), w''.under (𝓞 D.host.F) = w.under (𝓞 D.host.F) ↔ w'' = w ∨ w'' = w' := by
  first | exact @GlobalTheory.ConjPlace.conj_place | exact GlobalTheory.ConjPlace.conj_place | (intros; apply GlobalTheory.ConjPlace.conj_place <;> assumption)
