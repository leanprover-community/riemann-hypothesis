module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.OrdReadOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankFiberEqCardSectionsMulLength
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section

namespace UpperTheory.Gal.crystallineComparison.Mod

private theorem exists_algHom_ker (κ B : Type) [Field κ] [IsAlgClosed κ] [CommRing B] [Algebra κ B]
    [Module.Finite κ B] (p : PrimeSpectrum B) :
    ∃ ε : B →ₐ[κ] κ, RingHom.ker ε.toRingHom = p.asIdeal := by
  haveI : IsArtinianRing B := IsArtinianRing.of_finite κ B
  haveI : p.asIdeal.IsMaximal := Ideal.isMaximal_of_isPrime p.asIdeal
  letI : Field (B ⧸ p.asIdeal) := Ideal.Quotient.field _
  have hb : Function.Bijective (algebraMap κ (B ⧸ p.asIdeal)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let e := AlgEquiv.ofBijective (Algebra.ofId κ (B ⧸ p.asIdeal)) hb
  refine ⟨(e.symm : (B ⧸ p.asIdeal) →ₐ[κ] κ).comp (Ideal.Quotient.mkₐ κ p.asIdeal), ?_⟩
  ext x
  change x ∈ RingHom.ker _ ↔ x ∈ p.asIdeal
  simp [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]

theorem ringHomog_of : RingHomog := by
  intro κ B _ _ _ _ _ ε₀ _ hτ
  haveI : IsArtinianRing B := IsArtinianRing.of_finite κ B
  haveI hfin : Module.Finite κ (Localization.AtPrime (RingHom.ker ε₀.toRingHom)) :=
    Module.Finite.of_surjective
      (Algebra.algHom κ B (Localization.AtPrime (RingHom.ker ε₀.toRingHom))).toLinearMap
      (IsArtinianRing.localization_surjective (RingHom.ker ε₀.toRingHom).primeCompl
        (Localization.AtPrime (RingHom.ker ε₀.toRingHom)))
  have hm : ∀ p : PrimeSpectrum B,
      Module.length (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal) =
        (Module.finrank κ (Localization.AtPrime (RingHom.ker ε₀.toRingHom)) : ℕ∞) := by
    intro p
    obtain ⟨ε, hε⟩ := exists_algHom_ker κ B p
    obtain ⟨τ, hτε⟩ := hτ ε
    rw [GlobalTheory.FinSchemeRank.finrank_eq_length_of_isLocalRing κ]
    have hmap : p.asIdeal.primeCompl.map τ.toRingEquiv.toMonoidHom =
        (RingHom.ker ε₀.toRingHom).primeCompl := by
      ext y
      simp only [Submonoid.mem_map, Ideal.mem_primeCompl_iff, ← hε, RingHom.mem_ker, ← hτε]
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact hx
      · intro hy
        refine ⟨τ.symm y, ?_, ?_⟩
        · simpa using hy
        · simp
    exact GlobalTheory.FinSchemeRank.length_self_eq_of_ringEquiv
      (IsLocalization.ringEquivOfRingEquiv (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime (RingHom.ker ε₀.toRingHom)) τ.toRingEquiv hmap)
  have h := GlobalTheory.FinSchemeRank.finrank_eq_card_mul κ B _ hm
  rw [← GlobalTheory.FinSchemeRank.card_algHom_eq_card_primeSpectrum κ B] at h
  exact_mod_cast h

end UpperTheory.Gal.crystallineComparison.Mod
