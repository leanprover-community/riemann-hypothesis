module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwOrbEqFinsumTwTerm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralPointTermDoubleCosetInvari
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

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


theorem _root_.GlobalTheory.T.twistedOrbitalIntegralPointTerm_doubleCoset_invariant : ∀ {G : Type} [Group G] [TopologicalSpace G] (θ : G →* G) (K : Subgroup G) (δ : G) (f : G → ℂ), (∀ a ∈ twCent θ δ, ∀ b ∈ twCent θ δ, a * b = b * a) → (∀ y : G, (rStab fun k : K => f ((y * k)⁻¹ * δ * θ (y * k))).index ≠ 0) → ∀ t ∈ twCent θ δ, ∀ y, ∀ k ∈ K, GlobalTheory.EulerAbs.twTerm θ K δ f (t * y * k) = GlobalTheory.EulerAbs.twTerm θ K δ f y := by
  first | exact @GlobalTheory.EulerAbs.twTerm_inv | exact GlobalTheory.EulerAbs.twTerm_inv | (intros; apply GlobalTheory.EulerAbs.twTerm_inv <;> assumption)
