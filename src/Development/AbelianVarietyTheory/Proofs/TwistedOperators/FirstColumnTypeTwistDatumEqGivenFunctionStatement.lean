module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RankCol
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsPlaceModelProdHalf
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensorGiven
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstColumnTypeTwistDatumEqGivenFunction
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

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw


theorem _root_.GlobalTheory.T.first_column_type_twist_datum_eq_given_function : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (B : Frames G) {μ₀ : T}, L.Is μ₀ →
    ∀ (t : T) {e e' : AE D}, IsIdemSum e (locPl G t) → IsIdemSum e' (GlobalTheory.FlipTop.topPl L t) → (∀ w ∈ locPl G t, w ∉ GlobalTheory.FlipTop.topPl L t → ((∀ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) ≤ 1) ∧ ∃ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) = 1)) → ∀ (Φ : G.Datum) (j : ℕ) (hj : j < D.R.m),
    GlobalTheory.HalfProd.prodHalf e' (e - e') (halfInd (e - e') (latO (G.pS (.mu t 0 j)) (G.pT (.mu t 0 j)) (G.latS (.mu t 0 j) : Set _) (G.latT (.mu t 0 j) : Set _) fun _ => True)) (GlobalTheory.FlipTop.topFn B t e' j (GlobalTheory.FlipTop.rank_col G hj.le) (GlobalTheory.FlipTop.rank_col G hj)) =
      GlobalTheory.FlipStart.givenFn B t Φ e (.down t 0 j) := by
  first | exact @GlobalTheory.FlipTop.prodHalf_topFn_eq_givenFn | exact GlobalTheory.FlipTop.prodHalf_topFn_eq_givenFn | (intros; apply GlobalTheory.FlipTop.prodHalf_topFn_eq_givenFn <;> assumption)
