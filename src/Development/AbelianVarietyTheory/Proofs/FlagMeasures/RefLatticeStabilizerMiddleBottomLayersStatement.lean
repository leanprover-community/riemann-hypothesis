module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RefLatticeStabilizerMiddleBottomLayers
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsFundOne
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff
import Formalism.FormalDegreeBessel.StatementWR
import Formalism.SharpRestriction.CuspSpanNormBounds.Point

@[expose] public section

open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.refLatticeStabilizer_middle_bottom_layers : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ), ∀ (N : NF H r), ∀ L : Submodule (𝓞 K) V, IsUnimodMod H L (uPerp N.F N.F') (II N.F N.F') → N.F.z ∈ L → (∀ s ∈ N.Gam (N.Ref L), (∀ a : Fin r, s (N.F.e a.castSucc) = N.F.e a.castSucc) → ∀ b : Fin r, N.j ≤ b.val → ∃ ρ ∈ ipow N.𝔡 (-((r : ℤ) - b.val)) • (L ⊓ rs (𝓞 K) N.Wn), s (N.ist b) - N.ist b - ρ ∈ II N.F N.F') ∧ (∀ ρ : Fin r → V, (∀ b : Fin r, ρ b ∈ ipow N.𝔡 (-((r : ℤ) - b.val)) • (L ⊓ rs (𝓞 K) N.Wn)) → ∃ s ∈ N.Gam (N.Ref L), (∀ a : Fin r, s (N.F.e a.castSucc) = N.F.e a.castSucc) ∧ ∀ b : Fin r, N.j ≤ b.val → s (N.ist b) - N.ist b - ρ b ∈ II N.F N.F') ∧ (∀ s ∈ N.Gam (N.Ref L), (∀ a : Fin r, s (N.F.e a.castSucc) = N.F.e a.castSucc) → (∀ b : Fin r, N.j ≤ b.val → s (N.ist b) - N.ist b ∈ II N.F N.F') → ∀ a b : Fin r, N.j ≤ a.val → N.j ≤ b.val → H.B (s (N.ist b)) (N.ist a) ∈ ipow N.𝔡 (-((r : ℤ) - a.val) - ((r : ℤ) - b.val)) ∧ H.B (s (N.ist b)) (N.ist a) + star (H.B (s (N.ist a)) (N.ist b)) = 0) ∧ ∀ S : Fin r → Fin r → K, (∀ a b, S a b ∈ ipow N.𝔡 (-((r : ℤ) - a.val) - ((r : ℤ) - b.val)) ∧ S a b + star (S b a) = 0) → ∃ s ∈ N.Gam (N.Ref L), (∀ a : Fin r, s (N.F.e a.castSucc) = N.F.e a.castSucc) ∧ ∀ b : Fin r, N.j ≤ b.val → s (N.ist b) = N.ist b + ∑ a : Fin r, (if N.j ≤ a.val then S a b else 0) • N.F.e a.castSucc := by
  first | exact @GlobalTheory.RowStab.middle_bottom_layers | exact GlobalTheory.RowStab.middle_bottom_layers | (intros; apply GlobalTheory.RowStab.middle_bottom_layers <;> assumption)
