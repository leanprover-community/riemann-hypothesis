module

public import ReciprocityTheory.Hypotheses.GalCohDefs
import Mathlib.Algebra.AffineMonoid.Basic
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
public import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PairedDualFirstOrderDualMatrixSpace
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg

@[expose] public section

open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.sumDegF :
    ∀ (l : ℕ) [Fact l.Prime] (F : Type) [Field F] [NumberField F], ∑ᶠ v : {v : HeightOneSpectrum (𝓞 F) // ((l : ℕ) : 𝓞 F) ∈ v.asIdeal}, locDeg v.1 = Module.finrank ℚ F := by
  intro l _ F _ _
  classical
  have hl : l.Prime := Fact.out
  let p : Ideal ℤ := Ideal.span {(l : ℤ)}
  haveI hpmax : p.IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hl).irreducible
  have hp0 : p ≠ ⊥ := by
    simp only [p, ne_eq, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]
    exact hl.ne_zero
  let e1 : {v : HeightOneSpectrum (𝓞 F) // ((l : ℕ) : 𝓞 F) ∈ v.asIdeal} ≃
      {v : HeightOneSpectrum (𝓞 F) // v.asIdeal ∣ Ideal.map (algebraMap ℤ (𝓞 F)) p} :=
    Equiv.subtypeEquivRight (fun v => by
      rw [Ideal.dvd_iff_le, Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem,
        map_natCast])
  let e := e1.trans (HeightOneSpectrum.equivPrimesOver (𝓞 F) hp0)
  have h1 : ∑ᶠ v : {v : HeightOneSpectrum (𝓞 F) // ((l : ℕ) : 𝓞 F) ∈ v.asIdeal}, locDeg v.1
      = ∑ᶠ q : p.primesOver (𝓞 F), q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ := by
    rw [← finsum_comp_equiv e]
    rfl
  rw [h1, finsum_eq_sum_of_fintype, Ideal.sum_ramification_inertia_eq_finrank,
    NumberField.RingOfIntegers.rank]
