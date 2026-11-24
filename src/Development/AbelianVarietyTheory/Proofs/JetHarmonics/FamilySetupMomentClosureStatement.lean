module

public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FamilySetupMomentClosure
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.wedge_raising_scalar_sq_mul_degree_ratio_le : Hyps → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (l : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ), Setup lam u b bv ga h q0 z π μW μN μG νq R l dg → ∀ ν, n1 ν + (r + 1) * (r + 2) ≤ q0 → ∀ io pr ep, TensH (cmp (r + 1)) (cmp (r + 1) (Formalism.QuantumDeterminants.Hpk k r)) (R ν) (fun I : Sub (2 * r + k + 1) (r + 1) => R (ν + eZ I.1)) io pr ep → NzOn (R ν) (l ν) → ∀ (I : Sub (2 * r + k + 1) (r + 1)) (κ₀ : ℂ), NzOn (R (ν + eZ I.1)) (l (ν + eZ I.1)) → (∀ v ∈ (R ν).sm, l (ν + eZ I.1) (∑ c, pr I c (tm (R ν) (wedge (Formalism.QuantumDeterminants.fvec k r z)) v c)) = κ₀ • l ν v) → ‖κ₀‖ ^ 2 * dg ν / dg (ν + eZ I.1) ≤ Hsq r (Formalism.QuantumDeterminants.Tz k r z) b ^ (r + 1) := by
  first | exact @GlobalTheory.WedgeKappa.kappa_bound | exact GlobalTheory.WedgeKappa.kappa_bound | (intros; apply GlobalTheory.WedgeKappa.kappa_bound <;> assumption)
