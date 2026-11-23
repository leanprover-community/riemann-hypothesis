module

public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NotIsOfFinOrderUnitQuot
public import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfFiniteIndex
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SplitOffBadOfSuppSplitOff
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
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.IsHermForm
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.DatEqZero
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MovedOfSplitPl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesThird
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScalarOfIntertwinesUpToScalar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClsAt

@[expose] public section

set_option autoImplicit false


noncomputable section

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh.SerOne

open GlobalTheory.ClassScalarValue GlobalTheory.PtId

theorem guard_of_splitOffBad {D : D7} (V : HSp D) (hg : V.gram = 1) (hL : Bridge.hLat V 1 = Formalism.L2.Pj.stdLat D.host.E V.rank)
    {H : Geo.Tor.Host D.host.E} (l : Geo.Tor.Level H) {bad : ℕ} (h2 : 2 ∣ bad) (hM : l.M ∣ bad) {h : GA D V}
    (hs : SplitOffBad V bad h) : GlobalTheory.ClassScalarCompare.Guard H bad (Bridge.hLat V (fin V h)) := by
  obtain ⟨e, e1, e2, e3, e4⟩ := (GlobalTheory.RepsCompare.suppSplitOff_iff _ _ _).1
    (GlobalTheory.RepsCompare.suppSplitOff_of_splitOffBad _ _ _ hs)
  have hs' : GlobalTheory.UnRep.SuppSplit (GlobalTheory.Member.cF D) (bad * l.M) (finHom V h).1 := by
    refine ⟨e, e1, e2, fun v hv => ⟨(e3 v hv).1, fun hm => (e3 v hv).2 ?_⟩, e4⟩
    rw [Nat.cast_mul] at hm
    refine (v.isPrime.mem_or_mem hm).elim id fun h => ?_
    obtain ⟨u, rfl⟩ := hM
    rw [Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ h
  obtain ⟨-, c1, c2, -, -, c5⟩ := GlobalTheory.SplitReps.exists_conjLat V hg hL H l bad h2 h hs'
  have g := GlobalTheory.ClassScalarCompare.guard_conjLat (H := H)
    (L := (GlobalTheory.UnRep.FullReps.conjLat H (Bridge.hLat V (fin V h))).La) ⟨c1, c2, c5⟩
  have e2 : (GlobalTheory.ClassScalarCompare.conjLat (GlobalTheory.UnRep.FullReps.conjLat H (Bridge.hLat V (fin V h))).La).La =
    Bridge.hLat V (fin V h) := GlobalTheory.ClassScalarCompare.conjLat_conjLat _
  rwa [e2] at g

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {F : Face D A}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
  {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}



end GlobalTheory.AdTh.SerOne
