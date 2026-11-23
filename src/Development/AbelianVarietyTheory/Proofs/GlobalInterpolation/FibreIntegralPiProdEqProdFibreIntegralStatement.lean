module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FibreIntegralPiProdEqProdFibreIntegral
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
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.DualExponentDensity
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke
open scoped ENNReal TensorProduct


theorem _root_.GlobalTheory.T.fibreIntegral_pi_prod_eq_prod_fibreIntegral : ∀ (T V : Type) [Fintype T] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ₀ : Measure V) [SigmaFinite μ₀] (q : V → ℝ), Continuous q → ∀ U : Set V, IsOpen U → ∀ fib : ℝ → Measure V, IsFibreFamily μ₀ q id U (volume : Measure ℝ) Set.univ fib → ∀ B : Set (T → ℝ), IsOpen B → ∀ Fib : (T → ℝ) → Measure (T → V), IsFibreFamily (Measure.pi fun _ : T => μ₀) (fun x ρ => q (x ρ)) id Set.univ (volume : Measure (T → ℝ)) B Fib → ∀ b ∈ B, ∀ φ : T → V → ℝ, (∀ ρ, Continuous (φ ρ) ∧ HasCompactSupport (φ ρ) ∧ tsupport (φ ρ) ⊆ U ∧ ∀ y, 0 ≤ φ ρ y) → ∫⁻ x, ∏ ρ, ENNReal.ofReal (φ ρ (x ρ)) ∂(Fib b) = ∏ ρ, ∫⁻ y, ENNReal.ofReal (φ ρ y) ∂(fib (b ρ)) := by
  first | exact @GlobalTheory.FibreProd.lintegral_fibre_prod | exact GlobalTheory.FibreProd.lintegral_fibre_prod | (intros; apply GlobalTheory.FibreProd.lintegral_fibre_prod <;> assumption)
