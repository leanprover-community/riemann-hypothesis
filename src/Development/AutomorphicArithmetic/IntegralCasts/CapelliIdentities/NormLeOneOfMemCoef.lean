module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

theorem UpperTheory.Reformulated.B.Rf3.norm_le_one_of_mem_coef :
    ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] (c : UpperTheory.V.HV.Coef l)
    {x : Formalism.ConjugateSelfDual.Qbar l},
    x ∈ c.O →
      ‖x‖ ≤
        (1 :
          ℝ) := by
  intro l inst c x hx
  let v : Valuation (PadicAlgCl l) NNReal := NormedField.valuation
  have hv : ∀ y, y ∈ v.integer ↔ ‖y‖ ≤ 1 := fun y => Iff.rfl
  have h1 : IsIntegral ℤ_[l] x :=
    (Algebra.IsIntegral.isIntegral (R := ℤ_[l]) (⟨x, hx⟩ : c.O)).map c.O.val
  have h2 : ∀ a : ℤ_[l], algebraMap ℤ_[l] (PadicAlgCl l) a ∈ v.integer := fun a => by
    rw [hv, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l), PadicAlgCl.norm_extends]
    exact a.2
  have h3 : IsIntegral v.integer x :=
    h1.map_of_comp_eq ((algebraMap ℤ_[l] (PadicAlgCl l)).codRestrict v.integer h2) (RingHom.id _) rfl
  exact (hv x).1 ((Valuation.integer.integers v).mem_of_integral h3)
