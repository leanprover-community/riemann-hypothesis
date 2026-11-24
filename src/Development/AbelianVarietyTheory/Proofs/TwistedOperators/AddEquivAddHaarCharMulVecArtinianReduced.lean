module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MulVecCEApply
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VectorTupleProductMeasureTwoSidedAction
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.ModuLR
open scoped NNReal ENNReal TensorProduct

noncomputable section

namespace GlobalTheory.ModuArtin

theorem addEquivAddHaarChar_mulVecCE (B : Type) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [LocallyCompactSpace B] [T2Space B] [SecondCountableTopology B] [MeasurableSpace B] [BorelSpace B] :
    IsArtinianRing B → IsReduced B → ∀ (κ : Type) [Fintype κ] [DecidableEq κ] [MeasurableSpace (κ → B)]
      [BorelSpace (κ → B)] (M : Matrix κ κ B) (hM : IsUnit M.det),
      addEquivAddHaarChar (mulVecCE M hM) = modu B M.det := by
  intro hA hR κ _ _ inst hB M hM
  have heq : inst = MeasurableSpace.pi := by
    exact hB.measurable_eq.trans (@BorelSpace.measurable_eq (κ → B) _ MeasurableSpace.pi Pi.borelSpace).symm
  subst heq
  set ν : Measure B := Measure.addHaar
  set μ : Measure (κ → B) := Measure.pi fun _ : κ => ν
  have h1 := addEquivAddHaarChar_smul_map μ (mulVecCE M hM)
  have h2 : (modu B M.det : ℝ≥0∞) • Measure.map M.mulVec μ = μ :=
    GlobalTheory.GaugeEx.ModDet.smul_map_mulVec_pi ν M hM
  have hfun : ⇑(mulVecCE M hM) = M.mulVec := funext fun x => mulVecCE_apply M hM x
  rw [hfun] at h1
  obtain ⟨K⟩ := (inferInstance : Nonempty (TopologicalSpace.PositiveCompacts (κ → B)))
  have hpos : μ K ≠ 0 := ((isOpen_interior.measure_pos μ K.interior_nonempty).trans_le
    (measure_mono interior_subset)).ne'
  have hfin : μ K ≠ ⊤ := K.isCompact.measure_lt_top.ne
  set m := (Measure.map M.mulVec μ) (K : Set (κ → B))
  have e1 : (addEquivAddHaarChar (mulVecCE M hM) : ℝ≥0∞) * m = μ K := by
    conv_rhs => rw [← h1]
    rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  have e2 : (modu B M.det : ℝ≥0∞) * m = μ K := by
    conv_rhs => rw [← h2]
    rw [Measure.smul_apply, smul_eq_mul]
  have hm0 : m ≠ 0 := by
    intro h; rw [h, mul_zero] at e1; exact hpos e1.symm
  have hmt : m ≠ ⊤ := by
    intro h
    rw [h] at e1
    have hc : (addEquivAddHaarChar (mulVecCE M hM) : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast (addEquivAddHaarChar_pos (mulVecCE M hM)).ne'
    rw [ENNReal.mul_top hc] at e1
    exact hfin e1.symm
  have := (ENNReal.mul_left_inj hm0 hmt).1 (e1.trans e2.symm)
  exact_mod_cast this

end GlobalTheory.ModuArtin
