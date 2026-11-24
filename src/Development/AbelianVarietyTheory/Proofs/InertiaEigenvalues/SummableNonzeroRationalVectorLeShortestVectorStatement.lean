module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MeasurePreservingToMixedPiSymm
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SummableNonzeroRationalVectorLeShortestVector
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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

@[expose] public section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.ThetaPoisson GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped ComplexConjugate nonZeroDivisors ContDiff

theorem _root_.GlobalTheory.T.summable_nonzeroRationalVector_le_shortestVector : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (N : ℕ), Module.finrank ℝ (Fin a → Cinf E) ≤ N → ∃ (M : ℕ) (C : ℝ), ∀ (h : GA E a) (A : ℝ) (c : (Fin a → E) → ℂ), 0 ≤ A → (∀ ξ : Fin a → E, (fun i => pFin E (((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* h.val) i)) ∉ latt a J → c ξ = 0) → (∀ ξ ξ' : Fin a → E, ξ' ≠ 0 → (fun i => pFin E (((fun j => algebraMap E (Ad E) (ξ' j)) ᵥ* h.val) i)) ∈ latt a J → ‖c ξ‖ * (1 + ‖fun i => pInf E (((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* h.val) i)‖) ^ M ≤ A * ‖fun i => pInf E (((fun j => algebraMap E (Ad E) (ξ' j)) ᵥ* h.val) i)‖ ^ N) → Summable (fun ξ : {ξ : Fin a → E // ξ ≠ 0} => ‖c ξ‖) ∧ ∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, ‖c ξ‖ ≤ C * A := by
  first | exact @GlobalTheory.RSTheta.summable_tsum_norm_le_of_le_shortest | exact GlobalTheory.RSTheta.summable_tsum_norm_le_of_le_shortest | (intros; apply GlobalTheory.RSTheta.summable_tsum_norm_le_of_le_shortest <;> assumption)
