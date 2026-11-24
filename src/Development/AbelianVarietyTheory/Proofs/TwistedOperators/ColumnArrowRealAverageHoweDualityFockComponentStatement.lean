module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumProdPartialEqZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ColumnArrowRealAverageHoweDualityFockComponent
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairPtsClasses

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.columnArrow_realAverage_howeDuality_fockComponent : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T},
    t ∈ U → ∀ {Φ : G.Datum} {β : CosFam G t} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))),
    finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj → ∀ e : AE D, IsIdemSum e (locPl G t) →
    ∀ Tm : (WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) → ℂ) →ₗ[ℂ] (WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) → ℂ),
      IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) e (stdLatO S (.top t j)) 1 (S.Z.vac (.top t j)) Tm →
      ∃ c : ℂ, W.om (.top t j) (1, ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))) (S.Z.vac (.top t j)) =
        c • Tm fun x => halfInd e (stdLatO S (.top t j)) (actO _ _ 1⁻¹ ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))⁻¹ x) := by
  first | exact @GlobalTheory.ExpansionInvariance.vac_move_low | exact GlobalTheory.ExpansionInvariance.vac_move_low | (intros; apply GlobalTheory.ExpansionInvariance.vac_move_low <;> assumption)
