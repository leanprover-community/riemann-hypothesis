module

public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleySignature
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Mathlib.Analysis.CStarAlgebra.Matrix
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.CoefLocGap
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.CoefWeightedG

@[expose] public section

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

def CoefWeightedLoc : Prop :=
  ∀ (k r : ℕ) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ),
    Formalism.QuantumDeterminants.IsHCParam (Formalism.MainNotions.CayleySignature.lam48 k r v b) → Formalism.MainNotions.CayleySignature.GapBig k r b →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)),
      Formalism.MainNotions.S.IsDS (Formalism.MainNotions.CayleySignature.eps48 k r) (Formalism.MainNotions.CayleySignature.lam48 k r v b) σ →
      ∀ w : H, Formalism.MainNotions.S.IsLowUnit (Formalism.MainNotions.CayleySignature.eps48 k r) (Formalism.MainNotions.CayleySignature.lam48 k r v b) σ w →
        ∫⁻ g, ‖⟪w, σ (Formalism.MainNotions.S.uMat g) w⟫_ℂ‖ₑ *
            ENNReal.ofReal (‖Matrix.toEuclideanCLM (𝕜 := ℂ) (Formalism.MainNotions.S.uMat g)‖ ^
              (4 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 * Real.sqrt (2 * ((r + 1 : ℕ) : ℝ))))
          ∂(Formalism.REAL.muG (Formalism.MainNotions.CayleySignature.eps48 k r)) < ⊤

theorem coefWeightedLoc : CoefWeightedLoc := by
  intro k r v b hlam hgap H _ _ σ hDS w hw
  obtain ⟨h, hg, hthr⟩ := cayley_weight_gap k r v b hlam hgap
  exact coefWeightedN (Formalism.MainNotions.CayleySignature.eps48 k r) (Formalism.MainNotions.CayleySignature.lam48 k r v b) σ hlam hDS w hw h hg _
    (by positivity) hthr _

end ReciprocityTheory.ChartRestriction.DS
