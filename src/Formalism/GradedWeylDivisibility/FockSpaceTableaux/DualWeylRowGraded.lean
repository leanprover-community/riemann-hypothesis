module

public import Formalism.GradedWeylDivisibility.StatementA
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem dualWeylModuleRowGraded : DualWeylRowGraded := by
  classical
  intro R _ r n ν μ f hf
  simp only [dualWeyl, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    AlgHom.toLinearMap_apply, sub_eq_zero, mem_weightedHomogeneousSubmodule] at hf ⊢
  obtain ⟨hcol, hadd⟩ := hf
  refine ⟨?_, fun l j hlj => ?_⟩
  · intro d hd
    rw [coeff_weightedHomogeneousComponent] at hd
    split_ifs at hd with h
    · exact hcol hd
    · exact absurd rfl hd
  · let w' : Option (Fin r × Fin n) → (Fin r → ℕ) := fun o => Option.elim o 0 (rowW r n)
    have key : ∀ F : Fin r × Fin n → MvPolynomial (Option (Fin r × Fin n)) R,
        (∀ v, IsWeightedHomogeneous w' (F v) (rowW r n v)) → ∀ φ : MvPolynomial (Fin r × Fin n) R,
        weightedHomogeneousComponent w' μ (aeval F φ) =
          aeval F (weightedHomogeneousComponent (rowW r n) μ φ) := by
      intro F hF φ
      refine MvPolynomial.induction_on' φ (fun u a => ?_) (fun p q hp hq => ?_)
      · have hm : IsWeightedHomogeneous w' (aeval F (monomial u a)) (Finsupp.weight (rowW r n) u) := by
          rw [aeval_monomial, Finsupp.prod, Finsupp.weight_apply, Finsupp.sum, algebraMap_eq]
          have := (isWeightedHomogeneous_C w' a).mul
            (IsWeightedHomogeneous.prod u.support (fun i => F i ^ u i) (fun i => u i • rowW r n i)
              fun i _ => (hF i).pow (u i))
          rwa [zero_add] at this
        have hm0 : IsWeightedHomogeneous (rowW r n) (monomial u a) (Finsupp.weight (rowW r n) u) :=
          isWeightedHomogeneous_monomial _ _ _ rfl
        rw [weightedHomogeneousComponent_of_mem ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr hm),
          weightedHomogeneousComponent_of_mem ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr hm0)]
        split_ifs <;> simp
      · simp only [map_add (f := _), hp, hq]
    let G : Fin r × Fin n → MvPolynomial (Option (Fin r × Fin n)) R := fun v =>
      if v.2 = j then X (some v) + X none * X (some (v.1, l)) else X (some v)
    have hG : ∀ v, IsWeightedHomogeneous w' (G v) (rowW r n v) := by
      intro v
      simp only [G]
      split_ifs
      · refine (isWeightedHomogeneous_X R w' (some v)).add ?_
        have := (isWeightedHomogeneous_X R w' none).mul (isWeightedHomogeneous_X R w' (some (v.1, l)))
        rw [show w' none = 0 from rfl, zero_add] at this
        exact this
      · exact isWeightedHomogeneous_X R w' (some v)
    have hGs : ∀ v, IsWeightedHomogeneous w' ((fun v : Fin r × Fin n =>
        (X (some v) : MvPolynomial (Option (Fin r × Fin n)) R)) v) (rowW r n v) :=
      fun v => isWeightedHomogeneous_X R w' (some v)
    have hA : colAddGen R (r := r) l j = aeval G := rfl
    have hB : (rename (R := R) (some : Fin r × Fin n → Option (Fin r × Fin n))) =
        aeval (fun v : Fin r × Fin n => (X (some v) : MvPolynomial (Option (Fin r × Fin n)) R)) := by
      ext v; simp
    have h1 := hadd l j hlj
    rw [hA, hB] at h1 ⊢
    rw [← key G hG, ← key _ hGs, h1]

end Formalism.GradedWeylDivisibility
