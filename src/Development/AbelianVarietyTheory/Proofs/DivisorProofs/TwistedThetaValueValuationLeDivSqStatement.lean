module

public import Formalism.QuotientMetricDivisors.Statement
public import Formalism.SharpRestriction.LevelLetterCocycles.TwGood
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedThetaValueValuationLeDivSq
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlaceChoiceLiesOverPair
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop NumberField IsDedekindDomain
open GlobalTheory.FunObj.SqNum (nuH halfRank IsTor)
open GlobalTheory.CMVal GlobalTheory.HeckeGal

theorem _root_.GlobalTheory.T.twistedThetaValue_valuation_le_div_sq : ∀ {D : D7} (nch : NChoice D) (w : D.what₂.places.Pl) (N0 : D.ntw.Tw → ℕ) (lam : D.ntw.abelian₂ (nch.twI w)) (a : ℤ)
    (u : (nch.Oe w)ˣ) (z : D.what₂.LL),
    BlochKatoReduction.Gen.partC N0 (nch.twI w) (nch.Q w) (nch.k' w) (nch.psi' w ^ a) (twEps D (nch.twI w)) →
    nch.embW w z * nch.kMapE w (BlochKatoReduction.Gen.kMap D.ntw (nch.twI w) (nch.k' w) (∑ δ, D.ntw.th (nch.twI w) ∅ lam δ)) =
      algebraMap (nch.Oe w) (FractionRing (nch.Oe w)) (u : nch.Oe w) *
        nch.kMapE w (BlochKatoReduction.Gen.thEval D.ntw (nch.twI w) (nch.Q w) lam (nch.k' w)
          (BlochKatoReduction.Gen.psiAt (D.ntw.sideL (nch.twI w) lam) (nch.psi' w ^ a))) →
    (Formalism.DivisionValues.vw (D.plEq w) z : ℝ) ≤ (Formalism.DivisionValues.vw (D.plEq w) ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) : ℝ) / ((D.what₂.places.resChar w : ℕ) : ℝ) ^ 2 := by
  first | exact @GlobalTheory.TwistValBound.vw_le_of_bound | exact GlobalTheory.TwistValBound.vw_le_of_bound | (intros; apply GlobalTheory.TwistValBound.vw_le_of_bound <;> assumption)
