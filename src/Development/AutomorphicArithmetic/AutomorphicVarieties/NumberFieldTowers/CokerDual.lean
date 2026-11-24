module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.XTwApplyApply
public import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.DualKer
public import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.LenDual
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

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Tower

theorem UpperTheory.V.Tower.cokerDual :
    ∀ (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module ℤ_[l] M] (g : Module.End ℤ_[l] M) (t : Module.End ℤ_[l] (M →ₗ[ℤ_[l]] QZ l)), (∀ x φ, t x φ = x (g φ)) →
        cokerLen t = Module.length ℤ_[l] (LinearMap.ker g) := by
  intro l _ M _ _ g t h
  have ht : t = LinearMap.lcomp ℤ_[l] (QZ l) g := LinearMap.ext fun x => LinearMap.ext fun φ => h x φ
  obtain ⟨h1, h2⟩ := UpperTheory.V.Tower.dualKer l M M g
  have hr : LinearMap.range t
      = LinearMap.ker (LinearMap.lcomp ℤ_[l] (QZ l) (LinearMap.ker g).subtype) := by
    rw [ht]; exact h1
  rw [← UpperTheory.V.Tower.lenDual l (LinearMap.ker g)]
  exact ((Submodule.quotEquivOfEq _ _ hr).trans
    (LinearMap.quotKerEquivOfSurjective _ (h2 (LinearMap.ker g)))).length_eq
