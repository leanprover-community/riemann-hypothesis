module

public import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactUnipFlag
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsUniqueIsProdMeasureFinAway
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GoodConstOfAniso
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore

@[expose] public section

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal Topology

namespace GlobalTheory.CompanionTheory.RapidDecay

theorem norm_le_of_unipRad_variation : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ φ : GAd σ J → ℂ, (∀ γ ∈ ratPts σ J, ∀ g, φ (γ * g) = φ g) → Continuous φ → IsCuspidal σ J φ → ∀ (k : ℕ) (Cc : Matrix (Fin n) (Fin k) E), 0 < k → GlobalTheory.UAut.IsIsoCols σ J Cc → ∀ (g : GAd σ J) (e : ℝ), (∀ m ∈ unipRad σ J Cc, ‖φ (m * g) - φ g‖ ≤ e) → ‖φ g‖ ≤ e := by
  intro F E _ _ _ _ _ σ hCM n J hJ φ hleft hcont hcusp k Cc hk hC g e he
  haveI := GlobalTheory.UAut.locallyCompact_unipRad hCM hJ hC
  have hc : GlobalTheory.Cusp.Cocompact (ratPts σ J) (unipRad σ J Cc) := GlobalTheory.UAut.cocompact_unipRad hCM hJ hC
  haveI hP := hc.isProbabilityMeasure
  have hL : GlobalTheory.AutomorphicL2Unitary.LeftInv (ratPts σ J) φ := hleft
  have h0 : GlobalTheory.Cusp.constTermOn (ratPts σ J) (unipRad σ J Cc) φ g = 0 :=
    (hc.constTermOn_eq_zero_iff (GlobalTheory.AutomorphicL2Unitary.isFundamentalDomain_stdDom _ Measure.haar) hL g).2
      (hcusp k Cc ⟨hk, hC.1, hC.2⟩ _ _ inferInstance (GlobalTheory.AutomorphicL2Unitary.isFundamentalDomain_stdDom _ _) g)
  have hI := hc.integrable hL hcont g
  have key : φ g = ∫ q, (φ g - φ ((q.out : unipRad σ J Cc) * g))
      ∂GlobalTheory.Cusp.probMeasure (ratPts σ J) (unipRad σ J Cc) := by
    rw [integral_sub (integrable_const _) hI]
    have h0' : ∫ q, φ ((q.out : unipRad σ J Cc) * g)
        ∂GlobalTheory.Cusp.probMeasure (ratPts σ J) (unipRad σ J Cc) = 0 := h0
    rw [h0', integral_const]
    simp
  rw [key]
  have hb := norm_integral_le_of_norm_le_const (μ := GlobalTheory.Cusp.probMeasure (ratPts σ J) (unipRad σ J Cc))
    (f := fun q => φ g - φ ((q.out : unipRad σ J Cc) * g)) (C := e)
    (.of_forall fun q => by rw [norm_sub_rev]; exact he _ (q.out : unipRad σ J Cc).2)
  simpa using hb

end GlobalTheory.CompanionTheory.RapidDecay

end
