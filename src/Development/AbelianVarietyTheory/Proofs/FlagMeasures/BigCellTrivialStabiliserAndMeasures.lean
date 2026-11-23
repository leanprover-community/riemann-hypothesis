module

public import Formalism.PeriodIntegrals.BesselPeriodGGP
public import Formalism.SharpRestriction.CuspSpanNormBounds.RootMeasBig
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.CellDataExists
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UniformBesselConstant
import Formalism.FormalDegreeBessel.FinalBF
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp

namespace GlobalTheory.AmpTK

theorem bigCell_data : ∀ (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (μG : MeasureTheory.Measure (Formalism.QuantumDeterminants.Mt k r)), 1 ≤ k → L.κN ≠ ⊤ → 0 < L.κN → L.c ≠ 0 → IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) μG → ∀ (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ), (∀ a, c a ≠ 0) → μᴴ * Formalism.QuantumDeterminants.Hb k * μ = Formalism.QuantumDeterminants.Hb k → Formalism.QuantumDeterminants.bigCell k r c μ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) ∧ Formalism.MainNotions.S.IsRelStab L (Formalism.QuantumDeterminants.bigCell k r c μ) ∧ IsHaarOn (Formalism.MainNotions.S.RStab k r (Formalism.QuantumDeterminants.bigCell k r c μ)) (MeasureTheory.Measure.dirac (fun i j => (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) i j)) ∧ Formalism.MainNotions.S.IsOrbQuot L (Formalism.QuantumDeterminants.bigCell k r c μ) (MeasureTheory.Measure.dirac (fun i j => (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) i j)) (Formalism.MainNotions.S.pairMeas L) ∧ PI.BesselPeriodGGP.IsQuotMeas μG ((MeasureTheory.Measure.dirac (fun i j => (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) i j)).map (fun x => fun i j => ((Formalism.QuantumDeterminants.bigCell k r c μ)⁻¹ * Matrix.of x * Formalism.QuantumDeterminants.bigCell k r c μ) i j)) μG := by
  intro k r L μG hk hκt hκ hc hG c μ hca hμ
  have hg : bigCell k r c μ ∈ UH (Hpk k r) := Formalism.QuantumDeterminants.bigCellMem k r c μ hca hμ
  have hinv : (bigCell k r c μ)⁻¹ * bigCell k r c μ = 1 :=
    Matrix.nonsing_inv_mul _ (Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hg)
  have hR := GlobalTheory.AmpNorm.rStab_bigCell c μ hca hg
  set g := bigCell k r c μ
  have h1 : (Matrix.of fun i j => (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) i j) = 1 := rfl
  refine ⟨hg, ?_, ⟨inferInstance, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro a ha
    rw [hR, Set.mem_singleton_iff] at ha
    rw [ha, mul_one, hinv]
    unfold psi
    rw [Model.ell_one k r L.z L.hz.1, Model.ell_one k r L.z' L.hz'.1]
  · exact IsProbabilityMeasure.ne_zero _
  · rw [Measure.dirac_apply]
    have : (fun i j => (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) i j) ∉
        {x : Mt k r | Matrix.of x ∉ RStab k r g} := by
      intro h
      apply h
      rw [h1, hR]; rfl
    simp [Set.indicator_of_notMem this]
  · intro s hs
    rw [hR, Set.mem_singleton_iff] at hs
    subst hs
    have : (lmulM (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Mt k r → Mt k r) = id := by
      funext x; simp [lmulM]; rfl
    rw [this, Measure.map_id]
  · intro f hf
    have e : ∀ x : PairSp k r,
        (∫⁻ a, f (stabAct g (Matrix.of a) x) ∂(Measure.dirac
          (fun i j => (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) i j))) = f x := by
      intro x
      rw [lintegral_dirac, h1]
      have : stabAct g 1 x = x := by
        unfold stabAct
        rw [mul_one, hinv]
        simp only [one_mul]
        rfl
      rw [this]
    simp_rw [e]
  · intro f hf
    rw [Measure.map_dirac, h1, mul_one, hinv]
    refine lintegral_congr fun x => ?_
    rw [lintegral_dirac, h1, one_mul]
    rfl

end GlobalTheory.AmpTK
