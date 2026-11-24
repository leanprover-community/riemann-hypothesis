module

public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsContDiffExtensionOfIsClosed
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace ContDiff

namespace GlobalTheory

theorem smoothOnG_exists_contDiff_compactSupport_extension :
    ∀ (n : ℕ) (ε : Fin n → Bool) (β : Matrix (Fin n) (Fin n) ℂ → ℂ), SmoothOnG ε β →
      HasCompactSupport (fun g : UJ ε => β (umat g)) →
      ∃ F : (Fin n → Fin n → ℂ) → ℂ, ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧
        ∀ g : UJ ε, β (umat g) = F (fun i j => umat g i j) := by
  intro n ε β hβ hc
  obtain ⟨F₀, hF₀, hF₀eq⟩ := smoothOnG_exists_contDiff_extension n ε β hβ

  have hp : Continuous (fun g : UJ ε => (fun i j => umat g i j : Fin n → Fin n → ℂ)) := by
    have hu : Continuous (fun g : UJ ε => umat g) :=
      Units.continuous_val.comp continuous_subtype_val
    exact continuous_pi fun i => continuous_pi fun j => hu.matrix_elem i j

  have hK : IsCompact ((fun g : UJ ε => (fun i j => umat g i j : Fin n → Fin n → ℂ)) ''
      tsupport (fun g : UJ ε => β (umat g))) := hc.isCompact.image hp
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0

  let χ : ContDiffBump (0 : Fin n → Fin n → ℂ) :=
    ⟨max R 0 + 1, max R 0 + 2, by positivity, by linarith⟩
  refine ⟨fun x => (χ x : ℂ) * F₀ x, ?_, ?_, ?_⟩
  · exact (Complex.ofRealCLM.contDiff.comp χ.contDiff).mul hF₀
  · exact (χ.hasCompactSupport.comp_left Complex.ofReal_zero).mul_right
  · intro g
    have h₀ : F₀ (fun i j => umat g i j) = β (umat g) := hF₀eq (umat g) g.2
    by_cases hz : β (umat g) = 0
    · show β (umat g) = (χ (fun i j => umat g i j) : ℂ) * F₀ (fun i j => umat g i j)
      rw [h₀, hz, mul_zero]
    · have hmem : (fun i j => umat g i j : Fin n → Fin n → ℂ) ∈ Metric.closedBall 0 χ.rIn := by
        refine Metric.closedBall_subset_closedBall ?_ (hR ⟨g, subset_tsupport _ hz, rfl⟩)
        show R ≤ max R 0 + 1
        linarith [le_max_left R 0]
      show β (umat g) = (χ (fun i j => umat g i j) : ℂ) * F₀ (fun i j => umat g i j)
      rw [χ.one_of_mem_closedBall hmem, h₀, Complex.ofReal_one, one_mul]

end GlobalTheory
