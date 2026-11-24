module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasHermitianSignatureHyperbolicPlaneOrthCompleme
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLowLat

@[expose] public section

open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.PlaneSkew

theorem _root_.GlobalTheory.T.hasHermitianSignature_hyperbolicPlane_orthComplement : ∀ (n₁ : ℕ) (M : Matrix (Fin (n₁ + 2)) (Fin (n₁ + 2)) ℂ) (X Y : Fin (n₁ + 2) → ℂ)
    (ι : Matrix (Fin (n₁ + 2)) (Fin n₁) ℂ) (r s : ℕ), HasSig M r s → 1 ≤ r → 1 ≤ s →
    X ⬝ᵥ M *ᵥ star X = 0 → Y ⬝ᵥ M *ᵥ star Y = 0 → X ⬝ᵥ M *ᵥ star Y ≠ 0 →
    (∀ u, (ι *ᵥ u) ⬝ᵥ M *ᵥ star X = 0 ∧ (ι *ᵥ u) ⬝ᵥ M *ᵥ star Y = 0) → Function.Injective ι.mulVec →
    HasSig (ιᵀ * M * ι.map star) (r - 1) (s - 1) := by
  first | exact @GlobalTheory.PlaneSkewSig.hasSig_complement | exact GlobalTheory.PlaneSkewSig.hasSig_complement | (intros; apply GlobalTheory.PlaneSkewSig.hasSig_complement <;> assumption)
