module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBcrisTensorLatticeEquivPeriodRing
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem _root_.GlobalTheory.T.exists_bcrisTensorLattice_equiv_periodRing :
    ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (T : GlobalTheory.BKGal.QLat LL)
      (Pl : LocPrime l) (AI : LocAinf l Pl), GlobalTheory.Per.IsStd Pl AI →
      ∃ β : TW (GlobalTheory.BKReal.OB l ↥(OL LL)) T ≃ₗ[↥(OL LL)] T.V ⊗[ℚ_[l]] Pl.R.B,
        (∀ x : ↥T.L.T,
          β ((1 : GlobalTheory.BKReal.OB l ↥(OL LL)) ⊗ₜ[↥(OL LL)] x) =
            (x : T.V) ⊗ₜ[ℚ_[l]] (1 : Pl.R.B)) ∧
        (∀ g b, β (GlobalTheory.BKGal.actB (GlobalTheory.BKGal.sQ l) T g b) =
          actVB (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g (β b)) ∧
        (∀ b, β (TWmap (GlobalTheory.BKReal.frobOB l ↥(OL LL)) T b) =
          φVB (LL := ↥LL.1) (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (β b)) ∧
        ∀ c ∈ continuousCocycles T.ρ,
          c ∈ finiteCocycles (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ ↔
            ∃ b, GlobalTheory.BKGal.IsCobOf (GlobalTheory.BKGal.sQ l) T b c := by
  exact @GlobalTheory.BKGal.CrisTensor.exists_equiv
