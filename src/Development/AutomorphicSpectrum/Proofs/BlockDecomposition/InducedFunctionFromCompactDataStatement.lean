module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.RepresentationTheory.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedFunctionFromCompactData
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
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EGPgTrueEqLastIff
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.EPGFalseEqLastIff
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipApplyCastSuccLast
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.ProdGPn

@[expose] public section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct

theorem _root_.GlobalTheory.T.induced_function_from_compact_data : ∀ {G : Type} [Group G] {W₁ : Type} [AddCommGroup W₁] [Module ℂ W₁] {Q P : Subgroup G} {x : G} (σ : Representation ℂ Q W₁) (φ : P → W₁) (C : Set P) (K : Subgroup G), (∀ c ∈ C, ∀ κ ∈ K, ∀ (q : Q) (p' : P), (q : G) * x * (c : G) * κ = x * (p' : G) → φ p' = σ q (φ c)) → (∀ p : P, φ p ≠ 0 → ∃ c ∈ C, ∃ q : Q, x * (p : G) = (q : G) * x * (c : G)) → ∃ f : G → W₁, (∀ (q : Q) (g : G), f ((q : G) * g) = σ q (f g)) ∧ (∀ (g : G), ∀ κ ∈ K, f (g * κ) = f g) ∧ (∀ p : P, f (x * (p : G)) = φ p) ∧ ∀ g : G, f g ≠ 0 → ∃ q : Q, ∃ c ∈ C, ∃ κ ∈ K, g = (q : G) * x * (c : G) * κ := by
  first | exact @GlobalTheory.CompanionTheory.BZRes.TwoOrbit.exists_equivariant_extension | exact GlobalTheory.CompanionTheory.BZRes.TwoOrbit.exists_equivariant_extension | (intros; apply GlobalTheory.CompanionTheory.BZRes.TwoOrbit.exists_equivariant_extension <;> assumption)
