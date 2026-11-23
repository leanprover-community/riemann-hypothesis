module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PhiOfDivOf
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParamAboveLDirectSumPotSemistableStatement
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PWDFacts
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TripleAtt

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.BlockSum (blockRep)
open PositivityTheory.AutomorphicGaloisHodgeTate.Div (DivWCoreLac SenWLac HTLac IsSSMat)
open UpperTheory.Gal.Int.Div

theorem UpperTheory.Gal.Int.Div.subLoc_of :
    SubSplit → InFacts → LocConj → LocSum → JumpCard → SubLoc := by
  intro hS hI hC hL _ E Ω _ _ _ _ _ l _ a d r ρ hss hin ι w P AI hT A h O _ _ _ Bw hj
  obtain ⟨had, -, -⟩ := hI _ _ a d r ρ hin
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le had
  obtain ⟨s, g, hg⟩ := hS _ _ a b r ρ hss hin
  have e : (sumRep r s).comp (Dec (F := E) A).subtype =
      sumRep (r.comp (Dec (F := E) A).subtype) (s.comp (Dec (F := E) A).subtype) := by
    ext; rfl
  have hiso : RepIso (ρ.comp (Dec (F := E) A).subtype)
      (sumRep (r.comp (Dec (F := E) A).subtype) (s.comp (Dec (F := E) A).subtype)) := by
    refine ⟨g, fun x => ?_⟩
    rw [← e]
    exact hg x
  have hconj := (hC l P AI hT E Ω A O Bw (a + b) (ρ.comp (Dec (F := E) A).subtype) _).2 hiso
  have hsum := hL l P AI hT E Ω A O Bw a b (r.comp (Dec (F := E) A).subtype) (s.comp (Dec (F := E) A).subtype)
  refine ⟨fun hc => ?_, fun τ J J' h1 h2 => hsum.2 τ J J' (hconj.2.2.1 τ J h1) h2⟩
  have hcS := hconj.1 hc
  obtain ⟨cr, cs⟩ := hsum.1 hcS
  refine ⟨cr, fun x => ?_⟩
  have pr := ((hC l P AI hT E Ω A O Bw a _ (r.comp (Dec (F := E) A).subtype)).1 cr).2
  have ps := ((hC l P AI hT E Ω A O Bw b _ (s.comp (Dec (F := E) A).subtype)).1 cs).2
  have pT := ((hC l P AI hT E Ω A O Bw (a + b) _ (ρ.comp (Dec (F := E) A).subtype)).1 hcS).2
  have hw := GlobalTheory.T.weilDeligneParamAboveL_directSum_potSemistable l P AI hT ι E Ω A w O Bw h hj a b _ _ pr ps pT
  rw [← hconj.2.2.2 ι w h hj hc, hw, (UpperTheory.Gal.TP.Sub.wDFacts_holds E Ω A w h _ _).2.1 x]
  exact Dvd.intro _ rfl
