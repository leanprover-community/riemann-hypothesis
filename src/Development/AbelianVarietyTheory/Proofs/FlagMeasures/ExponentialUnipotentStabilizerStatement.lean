module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OfRoots
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExponentialUnipotentStabilizer
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

open NumberField Module Matrix Formalism.MainNotions.S GlobalTheory.LoopV
open scoped ENNReal Classical

theorem _root_.GlobalTheory.T.exponential_unipotent_stabilizer : ∀ (K : Type) [Field K] [NumberField K] (N : ℕ) (Z : Matrix (Fin N) (Fin N) K) (I : Ideal (𝓞 K)), Z.det ≠ 0 → (∀ x ∈ lieU Z, EntIn (Ideal.span {(N.factorial : 𝓞 K)} * I) x → expT x ∈ stabU Z ∧ EntIn I (expT x - 1) ∧ expT x * expT (-x) = 1) ∧ ∀ x ∈ lieU Z, ∀ y ∈ lieU Z, EntIn (Ideal.span {(N.factorial : 𝓞 K)} * I) x → EntIn (Ideal.span {(N.factorial : 𝓞 K)} * I) y → ∃ z ∈ lieU Z, EntIn (Ideal.span {(N.factorial : 𝓞 K)} * I) z ∧ expT x * expT y = expT z := by
  first | exact @GlobalTheory.LoopV.ExpGroup.exp_group | exact GlobalTheory.LoopV.ExpGroup.exp_group | (intros; apply GlobalTheory.LoopV.ExpGroup.exp_group <;> assumption)
