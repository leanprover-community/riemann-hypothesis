module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GinfCSecondCountable
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.HalfTwist

theorem integral_comp_addEquiv_eq_smul {G : Type*} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (ν : Measure G) [ν.IsAddHaarMeasure] (T : G ≃+ G) (hc : Continuous T) (hc' : Continuous T.symm) :
    ∃ r : ℝ, 0 < r ∧ ∀ φ : G → ℂ, ∫ x, φ (T x) ∂ν = r * ∫ x, φ x ∂ν := by
  haveI : (ν.map T).IsAddHaarMeasure := AddEquiv.isAddHaarMeasure_map ν T hc hc'
  let hT : G ≃ₜ G := { toEquiv := T.toEquiv, continuous_toFun := hc, continuous_invFun := hc' }
  have hemb : MeasurableEmbedding T := hT.measurableEmbedding
  refine ⟨((ν.map T).addHaarScalarFactor ν : ℝ), NNReal.coe_pos.2 (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _), ?_⟩
  intro φ
  have e := Measure.isAddLeftInvariant_eq_smul (ν.map T) ν
  rw [← hemb.integral_map φ]
  refine (congrArg (fun μ : Measure G => ∫ y, φ y ∂μ) e).trans ?_
  show ∫ y, φ y ∂(((ν.map T).addHaarScalarFactor ν) • ν) = _
  rw [integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]

theorem isClosed_fix (D : D7) (m n : ℕ) (c : AE D) : IsClosed {x : Mx D m n | ∀ i j, c * x i j = x i j} := by
  obtain ⟨i1, i2, -⟩ := Formalism.IndefR.Eqv.ae_facts D
  have : {x : Mx D m n | ∀ i j, c * x i j = x i j} = ⋂ i, ⋂ j, {x : Mx D m n | c * x i j = x i j} := by
    ext x; simp
  rw [this]
  refine isClosed_iInter fun i => isClosed_iInter fun j => isClosed_eq ?_ ?_
  · exact continuous_const.mul ((continuous_apply j).comp (continuous_apply i))
  · exact (continuous_apply j).comp (continuous_apply i)

theorem integral_twist_fix_eq_smul : ∀ (D : D7) (m n : ℕ) (c : AE D) (H : AddSubgroup (Mx D m n)), (∀ x, x ∈ H ↔ ∀ i j, c * x i j = x i j) → ∀ [MeasurableSpace H] [BorelSpace H] (ν : Measure H) [ν.IsAddHaarMeasure] (h : GL (Fin m) (AE D)) (a : GL (Fin n) (AE D)), ∃ r : ℝ, 0 < r ∧ ∀ φ : Mx D m n → ℂ, ∫ x : H, φ (h.1 ⬝ x.1 ⬝ a.1) ∂ν = r * ∫ x : H, φ x.1 ∂ν := by
  intro D m n c H hH _ _ ν _ h a
  obtain ⟨i1, i2, i3, i4, -⟩ := lattice_Mx D m n
  have key : ∀ y : Mx D m n, y ∈ H ↔ c • y = y := by
    intro y
    rw [hH]
    constructor
    · intro hy; ext i j; simpa using hy i j
    · intro hy i j; simpa using congrFun (congrFun hy i) j
  have mem : ∀ (g : GL (Fin m) (AE D)) (b : GL (Fin n) (AE D)) (y : Mx D m n), y ∈ H → g.1 ⬝ y ⬝ b.1 ∈ H := by
    intro g b y hy
    rw [key] at hy ⊢
    show c • (g.1 * y * b.1) = g.1 * y * b.1
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, hy]
  have hcl : IsClosed (H : Set (Mx D m n)) := by
    have : (H : Set (Mx D m n)) = {x : Mx D m n | ∀ i j, c * x i j = x i j} := by
      ext x; exact hH x
    rw [this]; exact isClosed_fix D m n c
  haveI : LocallyCompactSpace H := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology H := Topology.IsInducing.subtypeVal.secondCountableTopology
  let T : H ≃+ H :=
    { toFun := fun x => ⟨h.1 ⬝ x.1 ⬝ a.1, mem h a x.1 x.2⟩
      invFun := fun x => ⟨(h⁻¹).1 ⬝ x.1 ⬝ (a⁻¹).1, mem h⁻¹ a⁻¹ x.1 x.2⟩
      left_inv := fun x => by
        apply Subtype.ext
        show (h⁻¹).1 * (h.1 * x.1 * a.1) * (a⁻¹).1 = x.1
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc, Units.mul_inv,
          Matrix.mul_one]
      right_inv := fun x => by
        apply Subtype.ext
        show h.1 * ((h⁻¹).1 * x.1 * (a⁻¹).1) * a.1 = x.1
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc, Units.inv_mul,
          Matrix.mul_one]
      map_add' := fun x y => by
        apply Subtype.ext
        show h.1 * (x.1 + y.1) * a.1 = h.1 * x.1 * a.1 + h.1 * y.1 * a.1
        rw [Matrix.mul_add, Matrix.add_mul] }
  have hc : Continuous T := by
    show Continuous fun x : H => (⟨h.1 ⬝ x.1 ⬝ a.1, mem h a x.1 x.2⟩ : H)
    exact Continuous.subtype_mk ((continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const) _
  have hc' : Continuous T.symm := by
    show Continuous fun x : H => (⟨(h⁻¹).1 ⬝ x.1 ⬝ (a⁻¹).1, mem h⁻¹ a⁻¹ x.1 x.2⟩ : H)
    exact Continuous.subtype_mk ((continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const) _
  obtain ⟨r, hr, hφ⟩ := integral_comp_addEquiv_eq_smul ν T hc hc'
  exact ⟨r, hr, fun φ => hφ (fun x : H => φ x.1)⟩

end GlobalTheory.HalfTwist
