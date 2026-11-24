module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsNormalFormStabilizerMeasure
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabilizerDilationWeightsDualIsotropicVector
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabilizerHaarUnimodularNormalStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabilizerMeasureNormalisationSymm
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MatGroupHaarUniqueFiniteCompactOpenPos
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsFundOne

@[expose] public section

open NumberField MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.Amp.StabHaar

theorem normalFormStabilizerMeasure_eq_any_normalForm : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (n₁ n₂ g₀ : Mat k r) (β : Fin r → ℕ) (c : ℂ) (μR : Measure (Mt k r)), n₁ ∈ Nset k r → n₂ ∈ Nset k r → IsNormal0 k r hj β c z z' g₀ → IsNormalFormStabilizerMeasure k r hj z z' (n₁ * g₀ * n₂) 1 μR → μR = (lebR0 k r j β).map (conjM n₂⁻¹) ∧ SigmaFinite (lebR0 k r j β) := by
  intro k r j hj z z' n₁ n₂ g₀ β c μR hn₁ hn₂ hg₀ hR
  obtain ⟨hz, hz', hT, -⟩ := id hR

  have hN : IsNormalFormStabilizerMeasure k r hj z z' (n₁ * g₀ * n₂) 1 ((lebR0 k r j β).map (conjM n₂⁻¹)) := by
    unfold IsNormalFormStabilizerMeasure
    exact ⟨hz, hz', hT, n₁, hn₁, n₂, hn₂, g₀, β, c, hg₀, rfl, by rw [ENNReal.ofReal_one, one_smul]⟩
  obtain ⟨-, hcl, hHaar, -⟩ := GlobalTheory.Amp.StabMeas.stabilizer_measure_normalisation k r j hj z z' _ 1 _ one_pos hN
  obtain ⟨-, -, hHaarR, -⟩ := GlobalTheory.Amp.StabMeas.stabilizer_measure_normalisation k r j hj z z' _ 1 μR one_pos hR

  obtain ⟨huniq, -, -⟩ := GlobalTheory.MatHaar.haar_unique_locFinite_openPos (2 * r + k + 1)
    (Rset k r (n₁ * g₀ * n₂)) ((lebR0 k r j β).map (conjM n₂⁻¹)) (matGroup hcl) hHaar
  obtain ⟨t, -, htop, ht⟩ := huniq μR hHaarR

  have hNt : IsNormalFormStabilizerMeasure k r hj z z' (n₁ * g₀ * n₂) t.toReal μR := by
    unfold IsNormalFormStabilizerMeasure
    exact ⟨hz, hz', hT, n₁, hn₁, n₂, hn₂, g₀, β, c, hg₀, rfl, by
      rw [ht, ENNReal.ofReal_toReal htop.ne, Measure.map_smul]
      exact (conj_cont n₂⁻¹).measurable.aemeasurable⟩
  have h1 := normalFormStabilizerMeasure_scalar_le hj z z' _ 1 t.toReal μR hR hNt
  have h2 := normalFormStabilizerMeasure_scalar_le hj z z' _ t.toReal 1 μR hNt hR
  rw [ENNReal.ofReal_one, ENNReal.ofReal_toReal htop.ne] at h1 h2
  have ht1 : t = 1 := le_antisymm h2 h1
  obtain ⟨hH, -⟩ := GlobalTheory.T.stabilizer_haar_unimodular_normal k r j hj z z' g₀ β c hz hz' hT hg₀
  obtain ⟨hσ, -⟩ := hH
  exact ⟨by rw [ht, ht1, one_smul], hσ⟩

end GlobalTheory.Amp.StabHaar
