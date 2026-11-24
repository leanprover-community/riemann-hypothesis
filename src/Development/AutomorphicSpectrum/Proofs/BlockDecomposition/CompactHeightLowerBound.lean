module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RatVInjective
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CvecSurjective
import GroundTheory.AutomorphicForms.ReductionMahler
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZeroMemBoxF

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GlobalTheory.CompanionTheory.RedCov.Simple
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.RedCov.Simple

theorem exists_one_le_mul_hgt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (D : Set (GAd σ J)), IsCompact D → ∃ P : ℝ, 0 < P ∧ ∀ g ∈ D, ∀ v : Fin n → E, v ≠ 0 → 1 ≤ P * hgt σ J g v := by
  intro F E _ _ _ _ _ σ hCM n J D hD
  obtain ⟨-, -, h2, -⟩ := hCM
  haveI : Algebra.IsQuadraticExtension F E := ⟨h2⟩
  obtain ⟨P, hP, h⟩ := GroundTheory.Automorphic.Reduction.exists_adelicNorm_vecMul_le_mul
    (hD.image (Bridge.continuous_trG σ J).inv)
  refine ⟨P, hP, fun g hg v hv => ?_⟩
  have hc := Bridge.cvec_ne_zero (F := F) hv
  have e : GroundTheory.Automorphic.Reduction.ratVec (Bridge.cvec F v) ᵥ*
        (Bridge.trG σ J g).1 ᵥ* ((Bridge.trG σ J g)⁻¹).1 =
      GroundTheory.Automorphic.Reduction.ratVec (Bridge.cvec F v) := by
    rw [Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one]
  have h3 : GroundTheory.Automorphic.Reduction.adelicNorm (GroundTheory.Automorphic.Reduction.ratVec (Bridge.cvec F v) ᵥ*
        (Bridge.trG σ J g).1 ᵥ* ((Bridge.trG σ J g)⁻¹).1) ≤
      P * GroundTheory.Automorphic.Reduction.height (Bridge.trG σ J g) (Bridge.cvec F v) :=
    h _ ⟨g, hg, rfl⟩ _ (GroundTheory.Automorphic.Reduction.hasFiniteContent_height (Bridge.trG σ J g) hc)
  rw [e] at h3
  rw [Bridge.hgt_eq]
  exact (GroundTheory.Automorphic.Reduction.one_le_adelicNorm_ratVec hc).trans h3

end GlobalTheory.CompanionTheory.RedCov.Simple

end
