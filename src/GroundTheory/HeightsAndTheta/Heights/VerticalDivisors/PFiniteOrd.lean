module

public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsOrd
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
public import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

theorem FiniteOrd.proof : FiniteOrd.Statement := by
  intro R B _ _ _ _ _ _ b hb 𝔫
  have : IsNoetherianRing B := IsNoetherianRing.of_finite R B

  have hB : ringKrullDim B ≤ ringKrullDim R :=
    Order.krullDim_le_of_strictMono
      (fun p : PrimeSpectrum B ↦
        (⟨Ideal.comap (algebraMap R B) p.asIdeal, inferInstance⟩ : PrimeSpectrum R))
      (fun p q hpq ↦ Ideal.IsIntegral.comap_lt_comap (R := R) (A := B) hpq)
  have hS : ringKrullDim (Localization.AtPrime 𝔫.asIdeal) ≤ 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height 𝔫.asIdeal (Localization.AtPrime 𝔫.asIdeal)]
    refine Ideal.height_le_ringKrullDim_of_isPrime.trans (hB.trans ?_)
    rw [IsDiscreteValuationRing.ringKrullDim_eq_one R]
  have : Ring.KrullDimLE 1 (Localization.AtPrime 𝔫.asIdeal) :=
    Ring.krullDimLE_iff.mpr (by exact_mod_cast hS)
  have hbB : b ∈ nonZeroDivisors B := by
    refine mem_nonZeroDivisors_iff.mpr ⟨fun x hx ↦ ?_, fun x hx ↦ hb (by simpa [mul_comm, mul_zero] using hx)⟩
    exact hb (by simpa [mul_comm, mul_zero] using hx)
  have hbS : algebraMap B (Localization.AtPrime 𝔫.asIdeal) b ∈
      nonZeroDivisors (Localization.AtPrime 𝔫.asIdeal) :=
    IsLocalization.map_nonZeroDivisors_le 𝔫.asIdeal.primeCompl _ ⟨b, hbB, rfl⟩
  exact Ring.ord_ne_top hbS

end GroundTheory.Heights₂.Heights.Vertical
