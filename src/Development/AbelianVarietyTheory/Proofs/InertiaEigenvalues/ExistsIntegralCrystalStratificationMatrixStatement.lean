module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralCrystalStratificationMatrix
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

theorem _root_.GlobalTheory.T.exists_integral_crystal_stratification_matrix : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T), IsBK (T := resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) → ∀ (sh : (↥LL.1)⟦X⟧ →+* (↥LL.1)⟦X⟧⟦X⟧) (φ₂ : (↥LL.1)⟦X⟧⟦X⟧ →+* (↥LL.1)⟦X⟧⟦X⟧), (∀ (f : (↥LL.1)⟦X⟧) (i : ℕ), (i.factorial : (↥LL.1)⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative (R := ↥LL.1))^[i] f) → (∀ f : (↥LL.1)⟦X⟧, φ₂ (PowerSeries.C f) = PowerSeries.C (frob (↥LL.1) l f)) → (∀ f : (↥LL.1)⟦X⟧, φ₂ (sh f) = sh (frob (↥LL.1) l f)) → ∃ ε : ZMod a → Matrix ι ι (↥LL.1)⟦X⟧⟦X⟧, (∀ τ, (ε τ).map PowerSeries.constantCoeff = 1) ∧ (∀ τ, ε τ * ((P.mx (τ - 1)).map (frob (↥LL.1) l)).map sh = ((P.mx (τ - 1)).map (frob (↥LL.1) l)).map PowerSeries.C * (ε (τ - 1)).map φ₂) ∧ ∀ (τ : ZMod a) (i j : ι) (k : ℕ), (k.factorial : (↥LL.1)⟦X⟧) * coeff k (ε τ i j) ∈ S (↥(OL LL)) (↥LL.1) e := by
  first | exact @GlobalTheory.CrysStrat.exists_stratification | exact GlobalTheory.CrysStrat.exists_stratification | (intros; apply GlobalTheory.CrysStrat.exists_stratification <;> assumption)
