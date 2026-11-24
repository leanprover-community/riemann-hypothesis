module

public import Formalism.LocalRingCardinality.DataDIV
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
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain IsLocalRing Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.DegreeFormula

set_option linter.style.haveILetI false

namespace GlobalTheory.FrobEmb

theorem exists_frob_all (E : Type) [Field E] [NumberField E] [IsGalois ℚ E]
    (hc : ∀ a b : E ≃ₐ[ℚ] E, a * b = b * a) (p : ℕ) (hp : p.Prime) :
    ∃ σ : E ≃ₐ[ℚ] E, ∀ (P : Ideal (𝓞 E)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})], IsArithFrobAt ℤ σ P := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hpI : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hpZ.ne_zero).2 hpZ
  obtain ⟨⟨P, hPp, hPl⟩⟩ : Nonempty ((Ideal.span {(p : ℤ)}).primesOver (𝓞 E)) := inferInstance
  have hne : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot
    (p := Ideal.span {(p : ℤ)}) (by simpa using hp.ne_zero) P
  haveI : Finite (𝓞 E ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P hne
  obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant ℤ (E ≃ₐ[ℚ] E) P
  refine ⟨σ, fun Q _ _ => ?_⟩
  obtain ⟨t, rfl⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (Ideal.span {(p : ℤ)}) P Q (E ≃ₐ[ℚ] E)
  have := hσ.conj t
  rwa [hc t σ, mul_inv_cancel_right] at this

theorem isArithFrobAt_frobG (D : D7) (p : ℕ) (hp : p.Prime) (P : Ideal (𝓞 D.host.E)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})] : IsArithFrobAt ℤ (D.host.sigmaOf (frobG D p)) P := by
  haveI : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  have h : ∃ g : D.R.GG, ∀ (P : Ideal (𝓞 D.host.E)) [P.IsPrime]
      [P.LiesOver (Ideal.span {(p : ℤ)})], IsArithFrobAt ℤ (D.host.sigmaOf g) P := by
    obtain ⟨σ, hσ⟩ := exists_frob_all D.host.E (fun a b =>
      (D.host.gal).injective (by rw [map_mul, map_mul, mul_comm])) p hp
    obtain ⟨g, hg⟩ := (D.host.gal).symm.surjective σ
    have hg' : D.host.sigmaOf g = σ := hg
    exact ⟨g, hg' ▸ hσ⟩
  unfold frobG
  rw [dite_eq_left h]
  exact h.choose_spec P

end GlobalTheory.FrobEmb
