module

public import Formalism.LocalToGlobal.Columns.AbelianHostFieldConditions
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsIsPrimitiveRootOfAddCharNeOne
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsIsPrimitiveRootOfInjectiveCharacter
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

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
