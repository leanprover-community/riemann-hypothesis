module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.CycFieldA
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsDvdQKPowSubOne
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.CycDefs

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization Formalism.L2.Host GlobalTheory.HeckeGal

namespace GlobalTheory.FrobEmb

theorem norm_le_one_of_isIntegral {C : Type*} [NormedField C] [IsUltrametricDist C] {x : C}
    (hx : IsIntegral ℤ x) : ‖x‖ ≤ 1 := by
  have h : x ∈ (NormedField.valuation (K := C)).integer :=
    (Valuation.integer.integers (NormedField.valuation (K := C))).mem_of_integral hx.tower_top
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h
  exact_mod_cast h

def compPerm {E C : Type} [Field E] [Field C] (f : C ≃+* C) : Equiv.Perm (E →+* C) where
  toFun τ := f.toRingHom.comp τ
  invFun τ := f.symm.toRingHom.comp τ
  left_inv τ := by ext x; simp
  right_inv τ := by ext x; simp

theorem exists_frobPerm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime], ¬ (l : ℤ) ∣ NumberField.discr E →
    ∃ σ : Equiv.Perm (E →+* PadicAlgCl l), IsFrobPerm σ ∧ ∀ τ, σ (cj τ) = cj (σ τ) := by
  intro E _ _ _ l _ _
  obtain ⟨Fr, hFr⟩ := ReciprocityTheory.DiscreteGroups.LocalClassField.exists_isFrob (p := l) (K := ReciprocityTheory.DiscreteGroups.LocalClassField.Q0 l) ReciprocityTheory.DiscreteGroups.LocalClassField.finiteDimensional_base_field
  refine ⟨compPerm Fr.toRingEquiv, ?_, fun τ => rfl⟩
  intro τ x
  have hx : ‖τ (x : E)‖ ≤ 1 := norm_le_one_of_isIntegral (map_isIntegral_int τ x.isIntegral_coe)
  have h := hFr (τ (x : E)) hx
  rw [ReciprocityTheory.DiscreteGroups.LocalClassField.residue_cardinality_base_field] at h
  exact h

end GlobalTheory.FrobEmb
