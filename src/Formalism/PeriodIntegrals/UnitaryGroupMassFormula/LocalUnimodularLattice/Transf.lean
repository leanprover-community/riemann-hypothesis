module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnimodularLattice.Development
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.KoszulLowersPower
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory Matrix Topology

noncomputable section

namespace PI.NUnimodLoc.UnitaryGroupMassFormula.TR

open PI Formalism.REAL

variable {m : ℕ}

def conjH (P Q : Matrix (Fin m) (Fin m) ℂ) (hQP : Q * P = 1) (hPQ : P * Q = 1) : MtM m ≃ₜ MtM m where
  toFun x := fun i j => (Q * Matrix.of x * P) i j
  invFun x := fun i j => (P * Matrix.of x * Q) i j
  left_inv x := by
    funext i j
    show (P * (Q * Matrix.of x * P) * Q) i j = x i j
    rw [show P * (Q * Matrix.of x * P) * Q = (P * Q) * Matrix.of x * (P * Q) by
      simp only [Matrix.mul_assoc], hPQ, Matrix.one_mul, Matrix.mul_one]
    rfl
  right_inv x := by
    funext i j
    show (Q * (P * Matrix.of x * Q) * P) i j = x i j
    rw [show Q * (P * Matrix.of x * Q) * P = (Q * P) * Matrix.of x * (Q * P) by
      simp only [Matrix.mul_assoc], hQP, Matrix.one_mul, Matrix.mul_one]
    rfl
  continuous_toFun := by
    show Continuous fun x : Matrix (Fin m) (Fin m) ℂ => Q * x * P
    exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  continuous_invFun := by
    show Continuous fun x : Matrix (Fin m) (Fin m) ℂ => P * x * Q
    exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

lemma continuous_lmulQ (a : Matrix (Fin m) (Fin m) ℂ) : Continuous (lmulQ (m := m) a) := by
  show Continuous fun x : Matrix (Fin m) (Fin m) ℂ => a * x
  exact continuous_const.matrix_mul continuous_id

lemma continuous_rmulQ (a : Matrix (Fin m) (Fin m) ℂ) : Continuous (rmulQ (m := m) a) := by
  show Continuous fun x : Matrix (Fin m) (Fin m) ℂ => x * a
  exact continuous_id.matrix_mul continuous_const

theorem transfer_holds : Transfer := by
  intro m ε T S P Q hQP hPQ hS hR μ hσ h0 hcar hl s hs
  set Φ : UJ ε → MtM m := fun g => fun i j => (Q * uMat g * P) i j with hΦdef
  have hΦc : Φ = conjH P Q hQP hPQ ∘ coeMatrixAlt ε := rfl
  have hemb : MeasurableEmbedding Φ := by
    rw [hΦc]
    exact ((conjH P Q hQP hPQ).isClosedEmbedding.comp (isClosedEmbeddingMatrix m ε).1).measurableEmbedding
  have hΦm : Measurable Φ := hemb.measurable

  have hH : IsHaarOnM S (μ.map Φ) := by
    refine ⟨hemb.sigmaFinite_map, (Measure.map_ne_zero_iff hΦm.aemeasurable).2 h0, ?_, ?_⟩
    · rw [hemb.map_apply]
      refine measure_mono_null (fun g hg => ?_) hcar
      intro hT
      exact hg ((hS _).1 ⟨g.2, hT⟩)
    · intro s' hs'
      have ht : inUJ ε (P * s' * Q) ∧ P * s' * Q ∈ T := by
        refine (hS _).2 ?_
        rw [show Q * (P * s' * Q) * P = (Q * P) * s' * (Q * P) by simp only [Matrix.mul_assoc], hQP,
          Matrix.one_mul, Matrix.mul_one]
        exact hs'
      have hr : P * s' * Q ∈ Set.range (coeMatrixAlt ε) := by rw [range_coeMatrix]; exact ht.1
      obtain ⟨t, htt⟩ := hr
      have hcomm : lmulQ s' ∘ Φ = Φ ∘ (fun x => t * x) := by
        funext g
        show s' * Matrix.of (fun i j => (Q * uMat g * P) i j) = fun i j => (Q * uMat (t * g) * P) i j
        have hu : uMat (t * g) = coeMatrixAlt ε t * uMat g := rfl
        rw [hu, htt]
        funext i j
        show (s' * (Q * uMat g * P)) i j = (Q * (P * s' * Q * uMat g) * P) i j
        rw [show Q * (P * s' * Q * uMat g) * P = (Q * P) * s' * (Q * uMat g * P) by
          simp only [Matrix.mul_assoc], hQP, Matrix.one_mul]
      have htT : t ∈ {g : UJ ε | uMat g ∈ T} := by
        show coeMatrixAlt ε t ∈ T
        rw [htt]; exact ht.2
      rw [Measure.map_map (continuous_lmulQ s').measurable hΦm, hcomm,
        ← Measure.map_map hΦm (continuous_const_mul t).measurable, hl t htT]
  have hRI := hR _ hH
  have hs' : Q * uMat s * P ∈ S := (hS _).1 ⟨s.2, hs⟩
  have hcomm : Φ ∘ (fun x => x * s) = rmulQ (Q * uMat s * P) ∘ Φ := by
    funext g
    show (fun i j => (Q * uMat (g * s) * P) i j) = Matrix.of (fun i j => (Q * uMat g * P) i j) * (Q * uMat s * P)
    have hu : uMat (g * s) = uMat g * uMat s := rfl
    rw [hu]
    funext i j
    show (Q * (uMat g * uMat s) * P) i j = ((Q * uMat g * P) * (Q * uMat s * P)) i j
    rw [show (Q * uMat g * P) * (Q * uMat s * P) = Q * uMat g * (P * Q) * uMat s * P by
      simp only [Matrix.mul_assoc], hPQ, Matrix.mul_one]
    simp only [Matrix.mul_assoc]
  have hmap : (μ.map (fun x => x * s)).map Φ = μ.map Φ := by
    rw [Measure.map_map hΦm (continuous_mul_const s).measurable, hcomm,
      ← Measure.map_map (continuous_rmulQ _).measurable hΦm, hRI _ hs']
  rw [← hemb.comap_map (μ.map (fun x => x * s)), hmap, hemb.comap_map]

end PI.NUnimodLoc.UnitaryGroupMassFormula.TR

open PI.NUnimodLoc.UnitaryGroupMassFormula.TR in
#print axioms transfer_holds
