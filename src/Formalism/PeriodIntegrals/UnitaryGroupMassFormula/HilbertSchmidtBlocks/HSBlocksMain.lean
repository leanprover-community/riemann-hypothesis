module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NormCore
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HilbertSchmidtBlocks.Change
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open scoped Classical ComplexConjugate

namespace NormHilbertSchmidtBlocks

open Formalism.L2.SG.NormCut

theorem hSBlocks_main : HSBlocks := by
  intro C C' V V' _ _ _ _ _ _ _ A B
  have hS : ∀ {W U : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
      [NormedAddCommGroup U] [InnerProductSpace ℂ U] (S T : W →L[ℂ] U),
      inner ℂ (hsV S) (hsV T) =
        ∑ i, inner ℂ (S (stdOrthonormalBasis ℂ W i)) (T (stdOrthonormalBasis ℂ W i)) := by
    intro W U _ _ _ _ _ S T
    simp [hsV, PiLp.inner_apply]
  have hblk : ∀ (T : PiLp 2 (fun _ : C' => V') →L[ℂ] PiLp 2 (fun _ : C => V)) (ρ : C) (ρ' : C') (v : V'),
      blockOf T ρ ρ' v = T (WithLp.toLp 2 (Pi.single ρ' v : C' → V')) ρ := by
    intro T ρ ρ' v
    rfl
  have hch := sum_inner_change (stdOrthonormalBasis ℂ (PiLp 2 (fun _ : C' => V')))
    (fun p : (Σ _ : C', Fin (Module.finrank ℂ V')) =>
      WithLp.toLp 2 (Pi.single p.1 (stdOrthonormalBasis ℂ V' p.2) : C' → V'))
    (parseval_single) A.toLinearMap B.toLinearMap
  simp only [ContinuousLinearMap.coe_coe] at hch
  rw [hS, ← hch, Fintype.sum_sigma]
  simp only [hS]
  simp only [hblk, PiLp.inner_apply]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ρ' _ => ?_
  rw [Finset.sum_comm]

end NormHilbertSchmidtBlocks
