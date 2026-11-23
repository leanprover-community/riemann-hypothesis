module

public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DecGapOfFormula
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemUJsetOfKset
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormPosOfIsUnit
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

@[expose] public section

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder

namespace GlobalTheory.DecGapBound

theorem decGap_of_formulaGap : FormulaGap → DecGap := by
  intro hF n ε lam H _ _ σ hlam hDS h hgap hh g hg u hu v hv
  have hU := hDS.2.2.1
  have h1 : ‖⟪v, σ g u⟫_ℂ‖ ≤ decHS h (rkR ε) (dHS g) * ‖u‖ * ‖v‖ := by
    obtain ⟨k, X, hk, hX, hgk⟩ := (polar_decomposition_holds n ε).1 g hg
    have hs' := GlobalTheory.LowKProj.mem_UJset_of_Kset (Kset_star ε hk)
    have hkk : star k * k = 1 := hk.1.1
    have e1 : σ (NormedSpace.exp X) u = σ (star k) (σ g u) := by
      have h := hU.1.2 (star k) hs' g hg
      rw [show star k * g = NormedSpace.exp X by rw [hgk, ← Matrix.mul_assoc, hkk, Matrix.one_mul]] at h
      exact congrArg (fun F : H →L[ℂ] H => F u) h
    let L : H →ₗᵢ[ℂ] H := ⟨(σ (star k) : H →ₗ[ℂ] H), hU.2.1 _ hs'⟩
    have e2 : ⟪σ (star k) v, σ (star k) (σ g u)⟫_ℂ = ⟪v, σ g u⟫_ℂ := L.inner_map_map v (σ g u)
    have hb := dec_exp hF n ε lam H σ hlam hDS h hgap hh X hX u hu (σ (star k) v)
      (GlobalTheory.LowKProj.lowKSub_stable ε lam σ _ (Kset_star ε hk) v hv)
    rw [e1, e2, hU.2.1 _ hs' v, ← (GlobalTheory.Count.Cartan.cartan_distances n ε).1 k X hk hX, ← hgk] at hb
    exact hb
  refine ⟨h1, h1.trans ?_⟩
  have h0 : 0 ≤ h := le_trans (by positivity) hh
  obtain ⟨h2, h3⟩ := dOp_facts hg
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (decHS_le_decE _ h0 h2 h3) (norm_nonneg u)) (norm_nonneg v)

end GlobalTheory.DecGapBound
