module

import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasDensityAtIdentityLieAlgebraOfOmegaDensity
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
public import Formalism.PeriodIntegrals.QuotInv
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MatGroupHaarUniqueFiniteCompactOpenPos
public import Formalism.FormalDegreeBessel.FinalG
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HaarUniquenessConjugation
public import Formalism.RealPlaceAnalysis.FinalF
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped ENNReal

noncomputable section

namespace GlobalTheory.HaarTransport

theorem isMatGroup_UH_of_sq {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ) (hH : H * H = 1) : PI.IsMatGroup (UH H) := by
  apply GlobalTheory.OmegaFrobenius.isMatGroup_UH <;> assumption

theorem haar_transport : ∀ (k r : ℕ) (μG : Measure (Mt k r)) (ε : Fin (2 * r + k + 1) → Bool) (P : Mat k r),
    IsHaarOn (GG k r) μG → IsUnit P.det → Pᴴ * Formalism.REAL.Jm ε * P = Hpk k r →
    ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ ∀ φ : Mt k r → ℝ≥0∞, Measurable φ →
      ∫⁻ y, φ (Matrix.of.symm (P⁻¹ * umat y * P)) ∂(Formalism.REAL.muG ε) = c * ∫⁻ x, φ x ∂μG := by
  intro k r μG ε P hμ hP hH
  have hce := Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.phi_closedEmbedding (ε := ε) (P := P) Formalism.REAL.uJEmb hP
  have hm := hce.continuous.measurable
  have hme := hce.measurableEmbedding
  have hG : PI.IsMatGroup (GG k r) := isMatGroup_UH_of_sq _ (hpkFacts k r).2.1
  have hmem : ∀ y, Matrix.of (Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.phi ε P y) ∈ GG k r := fun y =>
    (Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.phi_range_iff Formalism.REAL.uJEmb uHConj hP hH _).1 ⟨y, rfl⟩
  have hν : PI.IsHaarOnM (GG k r) ((Formalism.REAL.muG ε).map (Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.phi ε P)) := by
    refine ⟨hme.sigmaFinite_map, ?_, ?_, ?_⟩
    · exact (Measure.map_ne_zero_iff hm.aemeasurable).2 (NeZero.ne _)
    · have hcl : IsClosed {x : PI.MtM (2 * r + k + 1) | Matrix.of x ∈ GG k r} := hG.1
      show (Measure.map _ _) {x : PI.MtM (2 * r + k + 1) | Matrix.of x ∈ GG k r}ᶜ = 0
      rw [Measure.map_apply hm hcl.measurableSet.compl]
      have : Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.phi ε P ⁻¹' {x : PI.MtM (2 * r + k + 1) | Matrix.of x ∈ GG k r}ᶜ = ∅ := by
        ext y; simpa using hmem y
      rw [this, measure_empty]
    · intro a ha
      obtain ⟨u, hu⟩ := (Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.phi_range_iff Formalism.REAL.uJEmb uHConj hP hH a).2 ha
      subst hu
      have hl : Measurable (PI.lmulQ (m := 2 * r + k + 1) (Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.phi ε P u)) :=
        (Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.lmul_cont (k := k) (r := r) (Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.phi ε P u)).measurable
      rw [Measure.map_map hl hm]
      have e : PI.lmulQ (m := 2 * r + k + 1) (Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.phi ε P u) ∘ Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.phi ε P =
          Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.phi ε P ∘ (fun v => u * v) := by
        funext v; exact Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.lmul_phi hP u v
      rw [e, ← Measure.map_map hm (measurable_const_mul u), map_mul_left_eq_self]
  have hμ' : PI.IsHaarOnM (GG k r) μG := hμ
  obtain ⟨c, -, hct, hc⟩ := (GlobalTheory.MatHaar.haar_unique_locFinite_openPos _ _ μG hG hμ').1 _ hν
  refine ⟨c, hct.ne, fun φ hφ => ?_⟩
  have h1 : ∫⁻ y, φ (Matrix.of.symm (P⁻¹ * umat y * P)) ∂(Formalism.REAL.muG ε) =
      ∫⁻ y, φ (Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.phi ε P y) ∂(Formalism.REAL.muG ε) := rfl
  rw [h1, ← lintegral_map hφ hm, hc, lintegral_smul_measure, smul_eq_mul]

end GlobalTheory.HaarTransport

end
