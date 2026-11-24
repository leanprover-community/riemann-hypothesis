module

public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDegZeroLocLocal
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsConeVarUnit
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsConeVarSurj
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsConeVarInj
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
import Mathlib.RingTheory.Radical.NatInt
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

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR IsLocalRing

noncomputable section

universe u



theorem ConePolyLocalization.proof (h₀ : DegZeroLocLocal.Statement.{u}) (h₁ : ConeVarUnit.Statement.{u})
    (h₂ : ConeVarSurj.Statement.{u}) (h₃ : ConeVarInj.Statement.{u}) :
    ConePolyLocalization.Statement.{u} := by
  intro F _ K _ _ ι _ P hP W hW hPW v hv
  have := hP.isPrime
  have := hW.isPrime
  have hA : IsLocalRing (degZeroLoc P {W}) := h₀ F K ι P hP W hW hPW
  refine ⟨hA, ?_⟩
  let _ := (coneVarMap P W hPW v).toRingHom.toAlgebra
  have := isPrime_map_C_mvPolynomial K (maximalIdeal (degZeroLoc P {W}))
  have hQ : ∀ q : MvPolynomial K (degZeroLoc P {W}),
      q ∈ ((maximalIdeal (degZeroLoc P {W})).map
        (C : degZeroLoc P {W} →+* MvPolynomial K _)).primeCompl ↔ ∃ e, IsUnit (q.coeff e) := by
    intro q
    rw [Ideal.mem_primeCompl_iff, mem_map_C_iff]
    push Not
    simp only [mem_maximalIdeal, mem_nonunits_iff, not_not]
  refine (isLocalization_iff _ _).mpr ⟨fun y => ?_, fun z => ?_, fun {x y} hxy => ?_⟩
  · obtain ⟨e, he⟩ := (hQ y).mp y.2
    exact h₁ F K ι P hP W hW hPW v hv y e he
  · obtain ⟨p, q, e, he, hz⟩ := h₂ F K ι P hP W hW hPW v hv z
    exact ⟨⟨p, ⟨q, (hQ q).mpr ⟨e, he⟩⟩⟩, hz⟩
  · refine ⟨1, ?_⟩
    rw [h₃ F K ι P hP W hW hPW v hv hxy]

end

end GroundTheory.Heights₂.Heights.FieldNumbers
