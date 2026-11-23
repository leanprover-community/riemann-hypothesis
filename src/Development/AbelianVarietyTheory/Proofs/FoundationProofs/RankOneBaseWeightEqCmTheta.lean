module

public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.HalfLevelCoefficients
public import Formalism.LocalToGlobal.UnitaryNorms.CharHost
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HalfOfPrimesIffLevelPb
public import Formalism.LocalToGlobal.ProjectiveLattices.LevelPb
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
import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.LocalToGlobal.Divisibility.LiftLat
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.TwistCoverDesign
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfOfBasePins
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrimeDvdAbsNormHalfDifferent
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector

@[expose] public section

noncomputable section

namespace GlobalTheory.HalfOnRecord

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Pj.LPb Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Lev
  Formalism.IndefR.FWT GlobalTheory.IndefiniteRowSideFullHecke.TwistCoverDesign GlobalTheory.HalfCompare GlobalTheory.CoverHalf
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Level)
open Formalism.L2.Host (PiBar)

variable {D : D7}

def designLevel (P : PiBar D.host) : Level (hostOfRecord D) :=
  IndefiniteRowSideFullHecke.HalfLevelCoefficients.levelAt D (IndefiniteRowSideFullHecke.HalfLevelCoefficients.halfOf D P.pb) ((ParAtCompare.levelPb_iff D P.pb).1 (levelPb_exists D P.pb P.pb_over))

theorem designLevel_Mb (P : PiBar D.host) :
    (designLevel P).Mb = ∏ k, (P.pb k).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) := rfl


variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]


end GlobalTheory.HalfOnRecord
