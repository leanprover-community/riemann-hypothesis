module

public import Formalism.HermitianLattices.StatementMass
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnimodularHermitianMassMulLeMass
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Formalism.FlagUnipotentLattices.MemOfOrthogonalAnisotropic

@[expose] public section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.unimodularHermitianMass_mul_le_mass : Formalism.HermitianLatticesTheory.SiegelMassRatio → ∀ (K : Type) [Field K] [NumberField K] [StarRing K], Formalism.HermitianLatticesTheory.IsCMUnram K → 1 ≤ Formalism.HermitianLatticesTheory.vInv K → ∀ (k s : ℕ) (Mb : ℝ) (ms : ℕ → ℝ), 3 ≤ k → 1 ≤ s → s < k → (∀ (n : ℕ) (W : Type) [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (h : W →ₗ⋆[K] W →ₗ[K] K) (I : Submodule (𝓞 K) W), h.IsSymm → Formalism.HermitianLatticesTheory.IsOrthoLattice h I n → Formalism.HermitianLatticesTheory.mass h I = ms n) → ms 1 ≤ Mb → ms 2 ≤ Mb → 1 ≤ Mb → ms s * ms (k - s) ≤ ms k * (Mb * (2 * Formalism.HermitianLatticesTheory.vInv K) ^ (Formalism.HermitianLatticesTheory.fDeg K) * 16 ^ (s * k * (Formalism.HermitianLatticesTheory.fDeg K))) := by
  first | exact @GlobalTheory.MassRatioBound.mass_mul_mass_le | exact GlobalTheory.MassRatioBound.mass_mul_mass_le | (intros; apply GlobalTheory.MassRatioBound.mass_mul_mass_le <;> assumption)
