module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
public import Formalism.LocalToGlobal.Divisibility.DivisionHeightBoundStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoupledClassSumCauchySchwarz
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopPlaceLogTheta

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.coupled_class_sum_cauchy_schwarz : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (Q : KerChain K) (v : InfinitePlace K) (t₁ t₂ h₀ h h₁ ny : ℝ), 0 ≤ t₁ → 0 ≤ t₂ → 0 ≤ h₀ → 0 ≤ h → 0 ≤ h₁ → 0 ≤ ny → (∀ b, PosAt ((Q.F Q.n).mem b) v) → PosAt Q.S v → PosAt Q.S₁ v → (∀ b, (Nat.card ((Q.F Q.n).mem b).Cl : ℝ) ≤ h₀) → (Nat.card Q.S.Cl : ℝ) ≤ h → (Nat.card Q.S₁.Cl : ℝ) ≤ h₁ → (∀ d, ((Q.Y.ys d).ncard : ℝ) ≤ ny) → (∀ b d₀ d, ∀ y ∈ Q.Y.ys d, OpLe ((Q.F Q.n).mem b) Q.S v ((Q.cp b).k1 d₀ d y) t₁) → (∀ b d d₁, ∀ y ∈ Q.Y.ys d, OpLe Q.S Q.S₁ v ((Q.cp b).k2 d y d₁) t₂) → ∀ φ : (Q.F Q.n).Forms, (Q.S₁.ipAt Q.hS₁ v (Q.cpl φ) (Q.cpl φ)).re ≤ (Fintype.card (Q.F Q.n).β : ℝ) * h₀ * h ^ 2 * h₁ * ny ^ 2 * t₁ * t₂ * (famIpAt (Q.F Q.n) (Q.hF Q.n) v φ φ).re := by
  first | exact @GlobalTheory.ColNorms.CplCS.cpl_le | exact GlobalTheory.ColNorms.CplCS.cpl_le | (intros; apply GlobalTheory.ColNorms.CplCS.cpl_le <;> assumption)
