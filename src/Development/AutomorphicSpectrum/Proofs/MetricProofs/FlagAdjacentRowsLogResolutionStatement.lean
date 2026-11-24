module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.PullbackPullback
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentRowsLogResolution
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
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

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

theorem _root_.GlobalTheory.T.flag_adjacent_rows_log_resolution : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ (d + 2)) (q : Fin 2 → RW.X → FA.S.X), (∀ i, HoloMap RW.A FA.S.A (q i)) → (∀ x x₀, FA.Re.π x₀ = q 0 x → SameOrbit (FA.Re.R.lift x₀ x₀) (fstPt k₀ (RW.lift x x))) → (∀ x x₀, FA.Re.π x₀ = q 1 x → SameOrbit (FA.Re.R.lift x₀ x₀) (sndPt k₀ (RW.lift x x))) → ∀ (L' : LocPot RW.X) (v : RW.X → RW.X → ℂ) (cst : ℝ), IsNormFn M τ a k₀ ca cb RW (fun x => logNormSec L' v x + cst) → ∀ (U : ℕ → Set (Fin d → ℂ)) (G : ℕ → (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (ΦY : ℕ → (Fin (d + 1) → ℂ) → FA.S.X) (ΦW : ℕ → (Fin (d + 2) → ℂ) → RW.X), (∀ m, IsOpen (U m)) → (∀ m, IsFibreChart FA τ a ca cb q (U m) (G m) (ΦY m) (ΦW m)) → ∃ α : ℕ → Ψ × Fin N → (Fin d → ℂ) → ℝ, (∀ m, ∀ w ∈ U m, (G m w).PosDef) ∧ (∀ m r s, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => G m w r s) (U m)) ∧ (∀ m p, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (α m p) (U m)) ∧ (∀ m (z : Fin (d + 1) → ℂ), Fin.tail z ∈ U m → ∃ Hh : (Fin (d + 1) → ℂ) → ℂ, AnalyticAt ℂ Hh z ∧ ∀ᶠ z' in 𝓝 z, ∑ p, (xiCoef τ a p : ℝ) * ((FA.S.comap some).potH p).φ (ΦY m z) (ΦY m z') = xiPot (G m (Fin.tail z')) (z' 0) + (Hh z').re) ∧ (∀ m p, p ≠ (τ, a) → ∀ z : Fin (d + 1) → ℂ, Fin.tail z ∈ U m → ∃ Hh : (Fin (d + 1) → ℂ) → ℂ, AnalyticAt ℂ Hh z ∧ ∀ᶠ z' in 𝓝 z, ((FA.S.comap some).potH p).φ (ΦY m z) (ΦY m z') = α m p (Fin.tail z') + (Hh z').re) ∧ ∀ m (z : Fin (d + 2) → ℂ), Fin.tail (Fin.tail z) ∈ U m → z 0 ≠ z 1 → logNormSec L' v (ΦW m z) + cst + (1 / 2) * ∑ p, (xiCoef τ a p : ℝ) * ((FA.S.comap some).ph p (q 0 (ΦW m z)) + (FA.S.comap some).ph p (q 1 (ΦW m z))) = logSin (G m (Fin.tail (Fin.tail z))) (z 0) (z 1) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.fibre_potentials | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.fibre_potentials | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.fibre_potentials <;> assumption)
