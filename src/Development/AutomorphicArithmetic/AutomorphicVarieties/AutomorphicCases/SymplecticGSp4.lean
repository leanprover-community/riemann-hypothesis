module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.DecompSigmaOrd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.IsAutQ
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.Top

namespace UpperTheory.V.Aut

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}

structure OfChar (D : Raw Ω c) (e : ℕ) {N : ℕ} [NeZero N] (ψ : DirichletCharacter c.O N) (n' p₁ m₀ : ℕ) : Prop where
  e_eq : D.e = e
  psi : D.ψ = Chr.dirG ℚ Ω ψ
  S_eq : D.S = (2 * l * N * p₁).primeFactors
  xi : ∃ (_ : NeZero p₁) (ξ' : DirichletCharacter c.O (2 ^ n')) (ξ₀ : DirichletCharacter c.O p₁), ξ'.IsPrimitive ∧ ξ' (-1) = -1 ∧
    orderOf ξ₀ = m₀ ∧ D.ξ = Chr.dirG ℚ Ω ξ₀ * Chr.dirG ℚ Ω ξ'

def OfCase (D : Raw Ω c) (h : Host) (e : ℕ) (ψ : DirichletCharacter c.O h.N) : Prop :=
  (h.CaseII l e ψ ∧ OfChar D e ψ (h.nII l ψ) 1 1) ∨ (h.CaseIII l e ψ ∧ OfChar D e ψ (h.nIII l ψ) (pOne h.chi) (orderOf ψ))

def IsAut4 (ι : PadicAlgCl l ≃+* ℂ) (r : G ℚ Ω →* M4 (PadicAlgCl l)) : Prop := Af.IsAutQ ι r.toHomUnits

end UpperTheory.V.Aut

end
