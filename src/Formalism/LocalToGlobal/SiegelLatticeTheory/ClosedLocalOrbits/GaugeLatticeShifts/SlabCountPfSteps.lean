module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.KExpCut
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHCut

@[expose] public section

noncomputable section

open scoped Classical ComplexConjugate ENNReal NNReal
open MeasureTheory

namespace Formalism.L2.SG.Pf.SlabCount

open Formalism.L2.SG.FoldBound Formalism.L2.SG.PoincareSeriesSquareIntegrable NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermOp
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PoincareInHH.Cut Formalism.L2.SG.TermOp.KExpCut Formalism.L2.SG.Full

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def LeviFinC : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Full X) (u' : D.what₂.Word),
    ∃ F : Submodule (𝓞 D.host.E) (VS D).V → Submodule (𝓞 D.host.E) (VS D).V →
        Finset ((VS D).V ≃ₗ[D.host.E] (VS D).V),
      ∀ Λ₁ ∈ Y.what₂ u', ∀ Λ₂ ∈ Y.what₂ u', ∀ (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (s : X.B.I.GA),
        RatLink X s σ → σ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → s ∈ Srat X u' → Formalism.HermitianLatticesTheory.gmap σ Λ₂ = Λ₁ →
          ∃ f ∈ F Λ₁ Λ₂, f⁻¹ * σ ∈ NLam Λ₂ (lf D (X.Fu u'))

theorem tsum_comp_le_of_fibre {ι κ β : Type*} (φ : ι → κ) (g : κ → ℝ≥0∞) (M : ℕ)
    (hfib : ∀ k, ∃ (S : Finset β) (e : ι → β), S.card ≤ M ∧
      ∀ i, φ i = k → e i ∈ S ∧ ∀ j, φ j = k → e i = e j → i = j) :
    ∑' i, g (φ i) ≤ (M : ℝ≥0∞) * ∑' k, g k := by
  rw [← (Equiv.sigmaFiberEquiv φ).tsum_eq, ENNReal.tsum_sigma', ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun k => ?_
  obtain ⟨S, e, hS, he⟩ := hfib k
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  have hc : s.card ≤ M := by
    refine le_trans ?_ hS
    refine Finset.card_le_card_of_injOn (fun i => e (i : ι)) (fun i _ => (he i.1 i.2).1) ?_
    intro i _ j _ hij
    exact Subtype.ext ((he i.1 i.2).2 j.1 j.2 hij)
  calc ∑ i ∈ s, g (φ ((Equiv.sigmaFiberEquiv φ) ⟨k, i⟩))
      = ∑ i ∈ s, g k := Finset.sum_congr rfl fun i _ => by
          show g (φ i.1) = g k
          rw [i.2]
    _ = (s.card : ℝ≥0∞) * g k := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (M : ℝ≥0∞) * g k := by gcongr

end Formalism.L2.SG.Pf.SlabCount
