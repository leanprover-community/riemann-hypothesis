module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EquivOfISupRange
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

theorem exists_split_loc : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (w : HeightOneSpectrum (𝓞 E)) (g : GA E a), ∃ (h : GA E a) (gw : GL (Fin a) (w.adicCompletion E)),
      g = h * finGL E a (locGL E a w gw) ∧
        ∀ u : GL (Fin a) (w.adicCompletion E),
          h * finGL E a (locGL E a w u) = finGL E a (locGL E a w u) * h := by
  intro E _ _ _ a w g
  obtain ⟨gw, hgw⟩ : ∃ gw, gw = GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) g) := ⟨_, rfl⟩
  refine ⟨g * (finGL E a (locGL E a w gw))⁻¹, gw, by rw [inv_mul_cancel_right], fun u => ?_⟩
  have hk : GeneralLinearGroup.map (pLoc E w)
      (GeneralLinearGroup.map (pFin E) (g * (finGL E a (locGL E a w gw))⁻¹)) = 1 := by
    rw [map_mul, map_inv, pFin_finGL, map_mul, map_inv, pLoc_locGL, hgw, mul_inv_cancel]
  generalize g * (finGL E a (locGL E a w gw))⁻¹ = k at hk ⊢
  refine ga_ext ?_ ?_
  · rw [map_mul, map_mul, pInf_finGL, one_mul, mul_one]
  · rw [map_mul, map_mul, pFin_finGL]
    exact LocUniq.comm_locGL w hk u

end GlobalTheory.CuspGeneric
