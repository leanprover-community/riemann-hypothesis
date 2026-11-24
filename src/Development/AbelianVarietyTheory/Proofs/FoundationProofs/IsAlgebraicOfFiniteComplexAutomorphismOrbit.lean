module

public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
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
public import Mathlib.FieldTheory.IsAlgClosed.Classification
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.ExpUpper
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Geometry.Manifold.StructureGroupoid
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
import Mathlib.NumberTheory.ModularForms.SlashActions
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FinOrbit

theorem exists_algEquiv_shift (E : Subfield ℂ) (z : ℂ) (hz : Transcendental E z) (k : ℕ) :
    ∃ g : ℂ ≃ₐ[E] ℂ, g z = z + k := by
  classical
  have hind : AlgebraicIndepOn E id ({z} : Set ℂ) := by
    rw [AlgebraicIndepOn, algebraicIndependent_unique_type_iff]
    simpa using hz
  obtain ⟨B, hzB, hB⟩ := exists_isTranscendenceBasis_superset hind
  have hzB' : z ∈ B := hzB rfl
  let := IsAlgClosed.isAlgClosure_of_transcendence_basis _ hB
  let b0 : B := ⟨z, hzB'⟩
  let f : B → MvPolynomial B E := fun i => if i = b0 then MvPolynomial.X i + (k : MvPolynomial B E)
    else MvPolynomial.X i
  let f' : B → MvPolynomial B E := fun i => if i = b0 then MvPolynomial.X i - (k : MvPolynomial B E)
    else MvPolynomial.X i
  let n : MvPolynomial B E ≃ₐ[E] MvPolynomial B E :=
    AlgEquiv.ofAlgHom (MvPolynomial.aeval f) (MvPolynomial.aeval f')
      (by ext i; by_cases h : i = b0 <;> simp [f, f', h])
      (by ext i; by_cases h : i = b0 <;> simp [f, f', h])
  let e := (hB.1.aevalEquiv.symm.trans (n.trans hB.1.aevalEquiv))
  let g0 := IsAlgClosure.equivOfEquiv ℂ ℂ e.toRingEquiv
  have hcomm : ∀ c : E, g0 (algebraMap E ℂ c) = algebraMap E ℂ c := by
    intro c
    rw [IsScalarTower.algebraMap_apply E (Algebra.adjoin E (Set.range ((↑) : B → ℂ))) ℂ,
      IsAlgClosure.equivOfEquiv_algebraMap]
    simp
  refine ⟨AlgEquiv.ofRingEquiv (f := g0) hcomm, ?_⟩
  have h1 : algebraMap _ ℂ (hB.1.aevalEquiv (MvPolynomial.X b0)) = z := by
    rw [hB.1.algebraMap_aevalEquiv, MvPolynomial.aeval_X]
  show g0 z = z + k
  conv_lhs => rw [← h1]
  rw [IsAlgClosure.equivOfEquiv_algebraMap]
  have : e.toRingEquiv (hB.1.aevalEquiv (MvPolynomial.X b0))
      = hB.1.aevalEquiv (MvPolynomial.X b0 + (k : MvPolynomial B E)) := by
    simp [e, n, f]
  rw [this, map_add (f := _), map_natCast, map_add (f := _), map_natCast, h1]

theorem isAlgebraic_of_finite_orbit :
    ∀ (E : Subfield ℂ) (x : ℂ), (Set.range fun g : ℂ ≃ₐ[E] ℂ => g x).Finite → IsAlgebraic E x := by
  intro E x hfin
  by_contra hx
  apply Set.infinite_of_injective_forall_mem (f := fun k : ℕ => x + (k : ℂ)) _ _ hfin
  · intro a b hab
    simpa using hab
  · intro k
    obtain ⟨g, hg⟩ := exists_algEquiv_shift E x hx k
    exact ⟨g, hg⟩

end GlobalTheory.FinOrbit
