module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsFundOne
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnimodularLatticeFundamentalSetVolume
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

open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.unimodular_lattice_fundamentalSet_volume : ∀ (K W : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup W] [Module K W] [FiniteDimensional K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (HW : HermSpace K W), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (k : ℕ) (ι : Type) [Fintype ι] (σ : ι → (K →+* ℂ)) (Ψ : ι → W → Fin (k + 1) → ℂ), IsPlaces σ → Module.finrank K W = k + 1 → (∀ v x y, Ψ v (x + y) = Ψ v x + Ψ v y) → (∀ v (c : K) x, Ψ v (c • x) = σ v c • Ψ v x) → (∀ v x y, herm (Hb k) (Ψ v x) (Ψ v y) = σ v (HW.B x y)) → ∀ (L : Submodule (𝓞 K) W) (𝔡 : Ideal (𝓞 K)) (n : ℤ) (ρ : ℝ), IsUnimod HW L → 𝔡 ≠ ⊥ → 0 < ρ → ∃ F : Set (ι → Fin (k + 1) → ℂ), MeasurableSet F ∧ (∀ a : ι → Fin (k + 1) → ℂ, ∃! x : W, x ∈ ipow 𝔡 n • L ∧ ((fun v => (ρ : ℂ) • Ψ v x) + a) ∈ F) ∧ volume F = ENNReal.ofReal ((Formalism.HermitianLatticesTheory.vInv K ^ Fintype.card ι * (Ideal.absNorm 𝔡 : ℝ) ^ n * ρ ^ (2 * Fintype.card ι)) ^ (k + 1)) := by
  first | exact @GlobalTheory.UnimodCov.unimod_fund | exact GlobalTheory.UnimodCov.unimod_fund | (intros; apply GlobalTheory.UnimodCov.unimod_fund <;> assumption)
