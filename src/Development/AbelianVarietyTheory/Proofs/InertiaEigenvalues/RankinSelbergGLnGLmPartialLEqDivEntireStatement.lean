module

public import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside
public import GroundTheory.GlobalFields.TateThesis.AdelicChar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergGLnGLmPartialLEqDivEntire
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.JSW Filter Topology Formalism.UG

theorem _root_.GlobalTheory.T.rankinSelberg_GLn_GLm_partialL_eq_div_entire : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n m : ℕ) (σ : CG E n) (σ' : CG E m), 1 ≤ m → m < n → σ.IsUnitary → σ'.IsUnitary → ∀ T : Finset (HeightOneSpectrum (𝓞 E)), (∀ w ∉ T, ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w (x * y))) : ℂ) = 1) ↔ x ∈ Ov E w) → UnrOutside T σ → UnrOutside T σ' → ∃ F H : ℂ → ℂ, Differentiable ℂ F ∧ Differentiable ℂ H ∧ (∀ x : ℝ, 0 < (H x).re ∧ (H x).im = 0) ∧ ∀ x : ℝ, 1 < x → HasProd (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => locL (Ideal.absNorm w.1.asIdeal) (sat σ w.1) ((sat σ' w.1).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ)) (F x / H x) := by
  first | (exact @GlobalTheory.RSnmUnf.rs_nm_partialL_eq_div) | (exact GlobalTheory.RSnmUnf.rs_nm_partialL_eq_div) | (intros; apply GlobalTheory.RSnmUnf.rs_nm_partialL_eq_div  <;> assumption)
