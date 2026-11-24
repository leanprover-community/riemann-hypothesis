module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ChSumSubCMul
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPrimitiveCharacterTwist
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLocallyConstantCycMod

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries GlobalTheory.KZ.Cmp

theorem _root_.GlobalTheory.T.exists_primitive_character_twist : ∀ (l : ℕ) [Fact l.Prime] (φ : DirichletCharacter (Qbar l) l) (e k : ℕ) (ζ : Qbar l), l ≠ 2 → 1 ≤ k → IsPrimitiveRoot ζ (l ^ k) → ∃ ψ : DirichletCharacter (Qbar l) (l ^ (k + 1)), ψ.IsPrimitive ∧ InComp φ e ψ ∧ ψ⁻¹ (1 + (l : ZMod (l ^ (k + 1)))) = ζ := by
  first | (exact @GlobalTheory.KZ.Cmp.PrimChar.exists_primitive_inComp) | (exact GlobalTheory.KZ.Cmp.PrimChar.exists_primitive_inComp) | (intros; apply GlobalTheory.KZ.Cmp.PrimChar.exists_primitive_inComp  <;> assumption)
