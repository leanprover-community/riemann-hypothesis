module

public import Formalism.LocalRingCardinality.DataGatTies
public import Formalism.LocalRingCardinality.HostCls
public import Formalism.FrobeniusOrbits.HostCorollaries
public import Formalism.LocalRingCardinality.SpanPowerMembership.GatRing

@[expose] public section

noncomputable section

namespace Formalism.BasicNotions.Examples₂.LevelValuationRings

open Formalism.MainNotions.G Formalism.FrobeniusOrbits NumberField QuadraticAlgebra

section Orbit

variable {G : Type} [Group G] [Finite G] (g : G)

end Orbit

variable {R : Ranks} (H : Host R) (p : ℕ)

theorem of_cls (h : H.cls p = .inertClass) : p ∉ H.small ∧ p ≠ H.q ∧ p ≠ H.d ∧
    jacobiSym (-(H.d : ℤ)) p ≠ 1 ∧ H.psAt p ≠ 1 := by
  unfold Host.cls primeClass at h
  by_cases h1 : p ∈ H.small
  · rw [if_pos h1] at h
    cases h
  rw [if_neg h1] at h
  by_cases h2 : p = H.q
  · rw [if_pos h2] at h
    cases h
  rw [if_neg h2] at h
  by_cases h3 : p = H.d
  · rw [if_pos h3] at h
    cases h
  rw [if_neg h3] at h
  by_cases h4 : jacobiSym (-(H.d : ℤ)) p = 1
  · rw [if_pos h4] at h
    cases h
  rw [if_neg h4] at h
  by_cases h5 : H.psAt p = 1
  · rw [if_pos h5] at h
    cases h
  exact ⟨h1, h2, h3, h4, h5⟩

private theorem coprime_of_cls (hp : p.Prime) (hc : H.cls p = .inertClass) : p.Coprime H.condN := by
  obtain ⟨h2, hq, hd, -, -⟩ := of_cls H p hc
  have h1 : ¬ p ∣ H.QS := fun h => h2 (Nat.mem_primeFactors.2 ⟨hp, h, H.QS_pos.ne'⟩)
  exact Nat.Coprime.mul_right (Nat.Coprime.mul_right (hp.coprime_iff_not_dvd.2 h1)
    ((Nat.coprime_primes hp H.hyp.1).2 hq)) ((Nat.coprime_primes hp H.hyp.2.1).2 hd)

def hOf : R.MA :=
  if h : p.Coprime H.condN then (H.art (ZMod.unitOfCoprime p h)).2 else 1

theorem hOf_of_coprime (h : p.Coprime H.condN) : hOf H p = (H.art (ZMod.unitOfCoprime p h)).2 := by
  rw [hOf, dite_eq_left h]

theorem unit_eq_neg_one (x : ℤˣ) (h : (x : ℤ) ≠ 1) : x = -1 := by
  rcases Int.units_eq_one_or x with hx | hx
  · rw [hx] at h
    exact absurd rfl h
  · exact hx

theorem frob_val (hp : p.Prime) (hc : H.cls p = .inertClass) (P : Ideal (𝓞 H.E)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})] (σ : H.E ≃ₐ[ℚ] H.E) (hσ : IsArithFrobAt ℤ σ P) :
    H.galE σ = (c0, hOf H p) := by
  have : Fact p.Prime := ⟨hp⟩
  have hco := coprime_of_cls H p hp hc
  obtain ⟨h2, hq, hd, hjd, hjq⟩ := of_cls H p hc
  obtain ⟨-, hiff, hval, -⟩ := H.der.frob p (hp.coprime_iff_not_dvd.1 hco) P
  obtain ⟨h1, h3, -⟩ := hval σ hσ
  have h4 := (hiff σ (ZMod.unitOfCoprime p hco) (ZMod.coe_unitOfCoprime p hco)).1 hσ
  refine Prod.ext (Prod.ext ?_ ?_) ?_
  · exact unit_eq_neg_one _ (by rw [h1]; exact hjq)
  · exact unit_eq_neg_one _ (by rw [h3]; exact hjd)
  · show (H.gal σ).2 = hOf H p
    rw [hOf_of_coprime H p hco, h4]

open Ideal in
theorem exists_frob (hp : p.Prime) (hc : H.cls p = .inertClass) :
    ∃ (P : Ideal (𝓞 H.E)) (_ : P.IsPrime) (_ : P.LiesOver (Ideal.span {(p : ℤ)}))
      (σ : H.E ≃ₐ[ℚ] H.E), IsArithFrobAt ℤ σ P := by
  have : Fact p.Prime := ⟨hp⟩
  have hco := coprime_of_cls H p hp hc
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hpI : (span {(p : ℤ)}).IsPrime := (span_singleton_prime hpZ.ne_zero).2 hpZ
  obtain ⟨⟨P, hPp, hPl⟩⟩ : Nonempty ((span {(p : ℤ)}).primesOver (𝓞 H.E)) := inferInstance
  obtain ⟨⟨σ, hσ⟩, -, -⟩ := H.der.frob p (hp.coprime_iff_not_dvd.1 hco) P
  exact ⟨P, hPp, hPl, σ, hσ⟩

instance (φ : Formalism.HC.Frame) : Finite ↥φ.Psi := inferInstance

variable {H p}

end Formalism.BasicNotions.Examples₂.LevelValuationRings

namespace Formalism.BasicNotions.Examples₂

open Formalism.MainNotions.G Formalism.FrobeniusOrbits NumberField LevelValuationRings

variable (D : D7) (h0 : ∀ u, Module.finrank ℂ (D.mem u).A.Mu0 = 0)
  (rOf : D.what₂.Word → ℕ → ℕ) (bs : D.what₂.Word → ℕ → Set ↥(D.R.Psi))

end Formalism.BasicNotions.Examples₂
