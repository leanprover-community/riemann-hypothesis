module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCliff
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.IsCoreMod
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SpinTensorHighestWeight
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

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount

theorem _root_.GlobalTheory.T.spin_tensor_highest_weight : ∀ {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (c : Fin n → Fin n → Matrix ι ι ℂ), IsCliff c →
    ∀ q : ι → ℂ, q ≠ 0 → (∀ a, spinM c a a *ᵥ q = ((-(rhoV n a) : ℝ) : ℂ) • q) →
    (∀ a b, a < b → spinM c b a *ᵥ q = 0) →
    ∀ {Z : Type} [AddCommGroup Z] [Module ℂ Z] (E : Fin n → Fin n → Module.End ℂ Z), Formalism.REAL.GlRel E →
    ∀ (ν : Fin n → ℝ) (z : Z), (∀ a, E a a z = ((ν a - rhoV n a : ℝ) : ℂ) • z) →
    (∀ i j : Fin n, (j : ℕ) = i + 1 → ((E i j) ^ 2) z = 0) →
    ∃ φ : (ι → ℂ) →ₗ[ℂ] Z, φ q = z ∧ (∀ a b, a < b → ∀ f, φ (spinM c a b *ᵥ f) = E a b (φ f)) ∧
      ∀ a f, φ (spinM c a a *ᵥ f) = E a a (φ f) - ((ν a : ℝ) : ℂ) • φ f := by
  first | exact @GlobalTheory.CompanionTheory.RealCount.SpinMap.exists_spin_map | exact GlobalTheory.CompanionTheory.RealCount.SpinMap.exists_spin_map | (intros; apply GlobalTheory.CompanionTheory.RealCount.SpinMap.exists_spin_map <;> assumption)
