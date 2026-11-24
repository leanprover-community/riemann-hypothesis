module

public import Formalism.ConjugateSelfDual.Statement
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Invariant.Profinite
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.GaloisValuations.GlobalB

@[expose] public section

open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open scoped Pointwise

namespace GlobalTheory

theorem conj_places_of_same_prime_below : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (K : IntermediateField E Ω) [FiniteDimensional E K] (A B : ValuationSubring Ω), (∀ x ∈ K, IsIntegral ℤ x → (A.valuation x < 1 ↔ B.valuation x < 1)) → ∃ ρ : G E Ω, (∀ x ∈ K, ρ x = x) ∧ ρ • A = B := by
  intro E Ω _ _ _ _ _ K _ A B h
  haveI : FiniteDimensional ℚ K := Module.Finite.trans E K
  haveI : NumberField K := ⟨⟩
  haveI : IsAlgClosure K Ω := ⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.tower_top (K := E) K⟩
  letI : TopologicalSpace (IntCl K Ω) := ⊥
  haveI : DiscreteTopology (IntCl K Ω) := ⟨rfl⟩
  haveI := continuousSMul_intCl K Ω
  haveI := isInvariant_intCl K Ω
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite (A := 𝓞 K)
    (G := Ω ≃ₐ[K] Ω) (primeBelow (F := K) A) (primeBelow (F := K) B) (by
      ext x
      rw [Ideal.under, Ideal.under, Ideal.mem_comap, Ideal.mem_comap, mem_primeBelow, mem_primeBelow]
      have hK : ((algebraMap (𝓞 K) (IntCl K Ω) x : IntCl K Ω) : Ω) = ((x : K) : Ω) := rfl
      rw [hK]
      refine h _ (x : K).2 ?_
      exact (x.2.map (IsScalarTower.toAlgHom ℤ K Ω)))
  have hgA : g • A = B := by
    refine eq_of_valuation_lt_one_iff K fun b hb => ?_
    let b' : IntCl K Ω := ⟨b, hb.tower_top⟩
    change b' ∈ primeBelow (F := K) (g • A) ↔ b' ∈ primeBelow (F := K) B
    rw [primeBelow_smul, hg]
  refine ⟨g.restrictScalars E, fun x hx => ?_, ?_⟩
  · show g x = x
    exact g.commutes ⟨x, hx⟩
  · rw [← hgA]
    ext y
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
      ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    rfl

end GlobalTheory
