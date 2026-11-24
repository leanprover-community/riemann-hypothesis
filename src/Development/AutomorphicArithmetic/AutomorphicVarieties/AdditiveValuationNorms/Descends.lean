module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.ABoundOfDescends
public import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.ExistsDescends
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open UpperTheory.V UpperTheory.V.PropA NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Tower

theorem UpperTheory.V.PropA.descends :
    ∀ (l : ℕ) [Fact l.Prime] (L₀ : Type) [Field L₀] [NumberField L₀], HasMuQ l L₀ →
      ∀ γ : G L₀ (AlgebraicClosure L₀), IsGen l ⊤ γ → Descends l L₀ γ := by
  intro l _ L₀ _ _ hmu γ hγ e he m L₁ _ _ _ hL
  have hne : (e : ℤ) ≠ 0 := by
    have : 0 < e := he
    exact_mod_cast this.ne'
  exact step0 hmu hγ hne m L₁ hL
