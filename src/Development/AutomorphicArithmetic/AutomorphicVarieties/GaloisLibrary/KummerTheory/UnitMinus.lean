module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LengthEqAddEigen
public import Mathlib.RingTheory.DedekindDomain.SInteger
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

theorem UpperTheory.V.Kum.unitMinus :
    ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] (n : ℕ) (a : Kˣ),
      a ∈ (∅ : Set (HeightOneSpectrum (𝓞 K))).unit K →
      a * Units.map (UpperTheory.V.cE (E := K)).toMonoidHom a ∈ powK (K := K) n →
      a ^ 2 ∈ CommGroup.torsion Kˣ ⊔ powK (K := K) n ∧
        (Odd n → a ∈ CommGroup.torsion Kˣ ⊔ powK (K := K) n) := by
  intro K _ _ _ n a ha hc
  obtain ⟨x, hx⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one K (a : K)
    (fun v => (ha v (Set.notMem_empty v)).le)
  obtain ⟨y, hy⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one K ((a⁻¹ : Kˣ) : K)
    (fun v => ((Subgroup.inv_mem _ ha) v (Set.notMem_empty v)).le)
  have hxy : x * y = 1 := by
    apply IsFractionRing.injective (𝓞 K) K
    rw [map_mul, hx, hy, map_one, Units.mul_inv]
  let u : (𝓞 K)ˣ := Units.mkOfMulEqOne x y hxy
  let f : (𝓞 K)ˣ →* Kˣ := Units.map (algebraMap (𝓞 K) K).toMonoidHom
  have hu : f u = a := Units.ext hx
  have hcu : f (IsCMField.unitsComplexConj K u) = Units.map (UpperTheory.V.cE (E := K)).toMonoidHom a := by
    rw [← hu]
    exact Units.ext rfl
  have hfin : IsOfFinOrder (u * (IsCMField.unitsComplexConj K u)⁻¹) :=
    (IsCMField.unitsMulComplexConjInv K u).2
  have htor : a * (Units.map (UpperTheory.V.cE (E := K)).toMonoidHom a)⁻¹ ∈ CommGroup.torsion Kˣ := by
    have := f.isOfFinOrder hfin
    rw [map_mul, map_inv, hu, hcu] at this
    exact this
  have h2 : a ^ 2 ∈ CommGroup.torsion Kˣ ⊔ powK (K := K) n := by
    have e : a ^ 2 = (a * (Units.map (UpperTheory.V.cE (E := K)).toMonoidHom a)⁻¹) *
        (a * Units.map (UpperTheory.V.cE (E := K)).toMonoidHom a) := by
      rw [mul_mul_mul_comm, inv_mul_cancel, mul_one, pow_two]
    rw [e]
    exact Subgroup.mul_mem_sup htor hc
  refine ⟨h2, ?_⟩
  rintro ⟨k, rfl⟩
  have hn : a ^ (2 * k + 1) ∈ CommGroup.torsion Kˣ ⊔ powK (K := K) (2 * k + 1) :=
    Subgroup.mem_sup_right ⟨a, rfl⟩
  rw [pow_succ, pow_mul] at hn
  exact (Subgroup.mul_mem_cancel_left _ (Subgroup.pow_mem _ h2 k)).1 hn
