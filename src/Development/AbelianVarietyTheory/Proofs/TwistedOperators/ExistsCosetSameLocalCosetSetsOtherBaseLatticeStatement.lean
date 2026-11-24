module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCosetSameLocalCosetSetsOtherBaseLattice
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
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

theorem _root_.GlobalTheory.T.exists_coset_same_localCosetSets_other_baseLattice : ∀ {D : D7} {T T' : Type} {L : LevCh D T} {L' : LevCh D T'} {sc : Consts} (G : GridData L sc) (G' : GridData L' sc)
    (B : GlobalTheory.FunObj.Frames G) (B' : GlobalTheory.FunObj.Frames G'),
    IsSDFrame (Yc D 0) (L.βY 0) (L.ΛY 0) (D.host.g 0 * D.host.g 1) →
    IsSDFrame (Yc D 0) (L'.βY 0) (L'.ΛY 0) (D.host.g 0 * D.host.g 1) →
    G'.pl.v0 = G.pl.v0 → G'.pl.w = G.pl.w → G'.sp.Vs 1 0 = G.sp.Vs 1 0 → HEq (B'.βs 1 0) (B.βs 1 0) →
    ∀ (h : 0 < D.R.m) (κ' : G'.CosAt 0), ∃ κ : G.CosAt 0, ∀ (t : T') (t₀ : T) (w : Pl D.host.E),
      GlobalTheory.FunObj.cosetSet t w B' h κ' = GlobalTheory.FunObj.cosetSet t₀ w B h κ := by
  first | exact @GlobalTheory.FunObj.CosFlip.exists_cos_cosetSet_eq | exact GlobalTheory.FunObj.CosFlip.exists_cos_cosetSet_eq | (intros; apply GlobalTheory.FunObj.CosFlip.exists_cos_cosetSet_eq <;> assumption)
