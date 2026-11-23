module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EGPgTrueEqLastIff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionConstructedFromDoubleCoset
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.ProdGPn

@[expose] public section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct

theorem _root_.GlobalTheory.T.section_constructed_from_double_coset : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [NonarchimedeanGroup G] {W₁ : Type} [AddCommGroup W₁] [Module ℂ W₁] {Q P : Subgroup G} {x : G}, LocSec Q P x → ∀ (σ : Representation ℂ Q W₁), IsSmooth σ → ∀ (φ : P → W₁), (∀ (q : Q) (p p' : P), (q : G) * x * (p : G) = x * (p' : G) → φ p' = σ q (φ p)) → ∀ (K' : Subgroup P), IsOpen (K' : Set P) → (∀ (p : P), ∀ κ ∈ K', φ (p * κ) = φ p) → ∀ (C : Set P), IsCompact C → ∀ (Y : Set G), IsOpen Y → (∀ c ∈ C, x * (c : G) ∈ Y) → ∃ K : Subgroup G, IsOpen (K : Set G) ∧ (∀ c ∈ C, ∀ κ ∈ K, x * (c : G) * κ ∈ Y) ∧ ∀ c ∈ C, ∀ κ ∈ K, ∀ (q : Q) (p' : P), (q : G) * x * (c : G) * κ = x * (p' : G) → φ p' = σ q (φ c) := by
  first | exact @GlobalTheory.CompanionTheory.BZRes.exists_openSubgroup_consistent | exact GlobalTheory.CompanionTheory.BZRes.exists_openSubgroup_consistent | (intros; apply GlobalTheory.CompanionTheory.BZRes.exists_openSubgroup_consistent <;> assumption)
