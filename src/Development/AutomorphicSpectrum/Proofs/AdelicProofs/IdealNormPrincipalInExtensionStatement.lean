module

public import Mathlib.Basic.Real.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Development.AutomorphicSpectrum.Proofs.AdelicProofs.IdealNormPrincipalInExtension
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
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice

@[expose] public section

open NumberField GroundTheory.Heights₂.Heights
open scoped nonZeroDivisors

theorem _root_.GlobalTheory.T.ideal_norm_principal_in_extension : ∀ (K : Type) [Field K] [NumberField K] (I : Ideal (𝓞 K)), I ≠ ⊥ → ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (_ : Algebra K K') (y : 𝓞 K'), y ≠ 0 ∧ y ∈ I.map (algebraMap (𝓞 K) (𝓞 K')) ∧ |((Algebra.norm ℚ (y : K') : ℚ) : ℝ)| = (I.absNorm : ℝ) ^ Module.finrank K K' := by
  first | exact @GlobalTheory.CompanionTheory.Lines.exists_principal_extension | exact GlobalTheory.CompanionTheory.Lines.exists_principal_extension | (intros; apply GlobalTheory.CompanionTheory.Lines.exists_principal_extension <;> assumption)
