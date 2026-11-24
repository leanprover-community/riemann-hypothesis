module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLocalDimDomain
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PMaximalIdealHeightFG
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
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

theorem LocalDimDomain.proof : LocalDimDomain.Statement := by
  intro n e J hJ he q hq
  have := hJ
  set M : Ideal (MvPolynomial (Fin n) ℂ) := RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)
  have hJM : J ≤ M := fun f hf => RingHom.mem_ker.mpr (hq f hf)
  let m : Ideal (MvPolynomial (Fin n) ℂ ⧸ J) := M.map (Ideal.Quotient.mk J)
  have hm : m.IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact hJM)
  have hsub : Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) ℂ ⧸ J) M.primeCompl =
      m.primeCompl := by
    ext x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    constructor
    · rintro ⟨z, hz, hzy⟩
      change Ideal.Quotient.mk J y ∉ m
      rw [← hzy]
      change Ideal.Quotient.mk J z ∉ M.map (Ideal.Quotient.mk J)
      rw [Ideal.mem_quotient_iff_mem hJM]
      exact hz
    · intro h
      change Ideal.Quotient.mk J y ∉ M.map (Ideal.Quotient.mk J) at h
      rw [Ideal.mem_quotient_iff_mem hJM] at h
      exact ⟨y, h, rfl⟩
  have : m.IsPrime := hm.isPrime
  have : IsLocalization.AtPrime (localRingAt J q) m := by
    unfold IsLocalization.AtPrime
    rw [← hsub]
    unfold localRingAt
    infer_instance
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height m (localRingAt J q),
    NumbersDVR.MaximalIdealHeightFG.proof ℂ (MvPolynomial (Fin n) ℂ ⧸ J) m hm, he]

end GroundTheory.Heights₂.Heights
