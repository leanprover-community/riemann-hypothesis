module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PairFramesOnSet
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
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

theorem _root_.GlobalTheory.T.pair_frames_on_set : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (V : Type) [AddCommGroup V] [Module Ω V] (A B : Lat ξ V) (p q : ℕ) (Vp Vq : Submodule Ω V) (T : Set (Cpt ξ)) (b₁ v₁ : Fin p → V) (b₂ v₂ : Fin q → V) (x : Cpt ξ), x ∈ T → A.IsVBOn T p Vp → B.IsVBOn T q Vq → LinearIndependent Ω b₁ → Submodule.span Ω (Set.range b₁) = Vp → LinearIndependent Ω b₂ → Submodule.span Ω (Set.range b₂) = Vq → A.IsFrameAt v₁ x → B.IsFrameAt v₂ x → ∃ α κ : Ω, α ≠ 0 ∧ κ ≠ 0 ∧ exteriorPower.ιMulti Ω p v₁ = α • exteriorPower.ιMulti Ω p b₁ ∧ exteriorPower.ιMulti Ω q v₂ = κ • exteriorPower.ιMulti Ω q b₂ ∧ (lineLat A B p q (exteriorPower.ιMulti Ω p b₁) (exteriorPower.ιMulti Ω q b₂)).IsGenAt x (α / κ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.LineGenerator.isGenAt_div | exact GlobalTheory.CompanionTheory.Ar.Flat.LineGenerator.isGenAt_div | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.LineGenerator.isGenAt_div <;> assumption)
