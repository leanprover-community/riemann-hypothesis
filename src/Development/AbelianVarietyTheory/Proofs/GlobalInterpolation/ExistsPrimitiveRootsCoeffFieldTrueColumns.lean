import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Formalism.LocalToGlobal.Columns.AbelianHostFieldConditions
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsPrimesOk

section
namespace GlobalTheory

theorem exists_isPrimitiveRoot_of_addChar_ne_one :
    ∀ (R K : Type) [CommRing R] [Field K] (p : ℕ), p.Prime → (p : R) = 0 →
      ∀ ψ : AddChar R K, ψ ≠ 1 → ∃ ζ : K, IsPrimitiveRoot ζ p := by
  intro R K _ _ p hp hpR ψ hψ
  obtain ⟨x, hx⟩ := AddChar.ne_one_iff.mp hψ
  have hpow : ψ x ^ p = 1 := by
    rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, hpR, zero_mul, AddChar.map_zero_eq_one]
  haveI : Fact p.Prime := ⟨hp⟩
  have hord : orderOf (ψ x) = p := orderOf_eq_prime hpow hx
  exact ⟨ψ x, hord ▸ IsPrimitiveRoot.orderOf (ψ x)⟩

end GlobalTheory
end

section
namespace GlobalTheory

theorem exists_isPrimitiveRoot_of_injective_character (K : Type) [Field K] (p : ℕ) (hp : p.Prime)
    (om : (ZMod p)ˣ →* Kˣ) (hom : Function.Injective om) :
    ∃ ζ : K, IsPrimitiveRoot ζ (p - 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod p)ˣ)
  rw [Nat.card_eq_fintype_card, ZMod.card_units] at hg
  refine ⟨(om g : K), ?_⟩
  rw [IsPrimitiveRoot.coe_units_iff, ← hg, ← orderOf_injective om hom g]
  exact IsPrimitiveRoot.orderOf _

end GlobalTheory
end

section
open Formalism.L2.Col NumberField IsDedekindDomain

namespace GlobalTheory

theorem colRoots_mem_of_mem_divs {A : Type} [CommRing A] [IsDedekindDomain A] {a : A}
    {P : HeightOneSpectrum A} (h : P ∈ divs a) : a ∈ P.asIdeal := by
  unfold divs at h
  split_ifs at h with hfin
  · exact (Set.Finite.mem_toFinset hfin).mp h
  · exact absurd h (Finset.notMem_empty P)

theorem colRoots_exists_primitiveRoots (X : Fields) (Pr : Primes X) (m : ℕ) (Ch : Chars X Pr m)
    (hf : 0 < X.f) (hP : Pr.Ok) (hC : Ch.Ok) (i : Fin 2) :
    (∃ ζ : X.K, IsPrimitiveRoot ζ (Pr.g i)) ∧ ∃ ζ : X.K, IsPrimitiveRoot ζ (Pr.g i - 1) := by
  refine ⟨?_, ?_⟩
  · have hcard : 0 < (Pr.vG i).card := by rw [hP.vG_card i]; exact hf
    obtain ⟨w, hw⟩ := Finset.card_pos.mp hcard
    have hwG : w ∈ Pr.vGs := by
      classical
      rw [Primes.vGs, Finset.mem_union]
      fin_cases i
      · exact Or.inl hw
      · exact Or.inr hw
    have hconj : X.conjO (Pr.piG i) ∈ w.asIdeal := colRoots_mem_of_mem_divs hw
    have hg : ((Pr.g i : ℕ) : 𝓞 X.E) ∈ w.asIdeal := by
      rw [← hP.piG_norm i]
      exact w.asIdeal.mul_mem_left _ hconj
    have hzero : ((Pr.g i : ℕ) : 𝓞 X.E ⧸ w.asIdeal) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk w.asIdeal)]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hg
    exact exists_isPrimitiveRoot_of_addChar_ne_one (𝓞 X.E ⧸ w.asIdeal) X.K (Pr.g i)
      (hP.g_prime i) hzero (Ch.psi0 ⟨w, hwG⟩) (hC.psi_zero_nontrivial_character _)
  · obtain ⟨om, hom, -⟩ := hC.chi_om i
    exact exists_isPrimitiveRoot_of_injective_character X.K (Pr.g i) (hP.g_prime i) om hom

end GlobalTheory
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem trueCols_exists_primitiveRoots : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (i : Fin 2), (∃ ζ : (I.rec7 l Z).what₂.LL, IsPrimitiveRoot ζ ((I.rec7 l Z).host.g i)) ∧ ∃ ζ : (I.rec7 l Z).what₂.LL, IsPrimitiveRoot ζ ((I.rec7 l Z).host.g i - 1) := by
  intro B X I h l Z i
  have hP := (base_fields_primes_ok B X).2.1
  have hf : 0 < B.fields.f := by
    have e : B.fields.f = 2 * B.R.ord := B.fields_f
    have := B.R.ord_pos
    rw [e]; omega
  exact colRoots_exists_primitiveRoots B.fields (B.primes X) B.R.m I.Ch hf hP h.ch_ok i

end GlobalTheory
end
