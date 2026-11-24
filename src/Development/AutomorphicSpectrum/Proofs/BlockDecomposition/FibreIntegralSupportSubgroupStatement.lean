module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UMLeviMulUMLevi
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreIntegralSupportSubgroup
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

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

theorem _root_.GlobalTheory.T.fibre_integral_support_subgroup : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W) [MeasurableSpace (Fin t → k)] (μ : MeasureTheory.Measure (Fin t → k)) (c : kˣ) (K₁ : Subgroup (GL (Fin (i + t)) k)) (hK : K₁ ≤ GlobalTheory.SplitWeil.KO k (Fin (i + t))) (b : cIndSpace (HPG k i t) (hRep τ σ)), (∀ p : Mir k (i + t), (¬ ∃ h : HPG k i t, ∃ β ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.Bgrp (i + t) c K₁ hK, p = (h : Mir k (i + t)) * β) → b.1.1.1 p = 0) → ∀ g : GL (Fin (i + t)) k, (¬ ∃ q : Qp k i t, ∃ b' ∈ K₁, g = (q : GL (Fin (i + t)) k) * b') → fibInt μ b g = 0 := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.FibOffQ.main | exact GlobalTheory.CompanionTheory.BZPsiPG.FibOffQ.main | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.FibOffQ.main <;> assumption)
