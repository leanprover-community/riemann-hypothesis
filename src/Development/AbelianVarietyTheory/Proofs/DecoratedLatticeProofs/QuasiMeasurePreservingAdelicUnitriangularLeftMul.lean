module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf



namespace GlobalTheory.LeftUniQmp

theorem qmp_left_uni : ∀ (D : D7) (ρ n : ℕ) (μ : Measure (Mx D ρ n)), μ.IsAddHaarMeasure → ∀ u : UX D ρ, Measure.QuasiMeasurePreserving (fun b : Mx D ρ n => u.1.1 ⬝ b) μ μ := by
  intro D ρ n μ hμ u
  obtain ⟨i1, i2, i3, i4, -⟩ := lattice_Mx D ρ n
  haveI : BorelSpace (Mx D ρ n) := ⟨rfl⟩
  have hc : Continuous (fun b : Mx D ρ n => u.1.1 ⬝ b) := continuous_const.matrix_mul continuous_id
  have hc' : Continuous (fun b : Mx D ρ n => (u.1⁻¹).1 ⬝ b) := continuous_const.matrix_mul continuous_id
  let T : Mx D ρ n ≃+ Mx D ρ n :=
    { toFun := fun b => u.1.1 ⬝ b
      invFun := fun b => (u.1⁻¹).1 ⬝ b
      left_inv := fun b => by
        show (u.1⁻¹).1 ⬝ (u.1.1 ⬝ b) = b
        rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
      right_inv := fun b => by
        show u.1.1 ⬝ ((u.1⁻¹).1 ⬝ b) = b
        rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
      map_add' := fun a b => Matrix.mul_add _ _ _ }
  haveI : (μ.map T).IsAddHaarMeasure := AddEquiv.isAddHaarMeasure_map μ T hc hc'
  refine ⟨hc.measurable.aemeasurable, ?_⟩
  have e := Measure.isAddLeftInvariant_eq_smul (μ.map T) μ
  show μ.map T ≪ μ
  rw [e]
  exact Measure.smul_absolutelyContinuous

end GlobalTheory.LeftUniQmp
