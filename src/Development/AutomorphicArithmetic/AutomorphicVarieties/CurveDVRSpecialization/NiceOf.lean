module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.SecondThirdPrimeConditionTransferAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.NiceIrr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.NiceSpecializationTwistSatisfiesFirstCondition
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.NiceSpecializationTwistSatisfiesThirdCondition
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.NiceTypeE
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

theorem UpperTheory.V.Pr.niceOf :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [UpperTheory.V.Fr.IsCoef l O] [Algebra ℤ_[l] O] (F : UpperTheory.V.Fr.Frame l (IsLocalRing.ResidueField O)) (n : ℕ) (T : UpperTheory.V.Pr.Setup F n), T.NiceOf := by
  intro l _ O _ _ _ _ _ F n T x L y j hj hp h1 h2
  refine ⟨UpperTheory.V.Pr.nice_specialization_twist_satisfies_first_condition l O F n T x L y j hj hp h1 h2, UpperTheory.V.Pr.nice_specialization_twist_satisfies_third_condition l O F n T x L y j hj hp h1 h2,
    fun hI => ?_, fun hE => ?_⟩
  · have h := UpperTheory.V.Pr.niceIrr l O F n T x L y j hj hp h1 h2 hI ⊤ (by simp)
    rw [top_inf_eq] at h
    exact h
  · obtain rfl : n = 3 := hE.2.1
    exact UpperTheory.V.Pr.niceTypeE l O F T x L y j hj hp h1 h2 hE
