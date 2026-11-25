module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.StmtFields
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.ExplicitConstants.SplitCharY
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.HeckeCharacterChoice.ExistsSqEqNegOfDiscr
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Algebra.Algebra.Subalgebra.IsSimpleOrder
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

theorem UpperTheory.V.HV.kstar :
    ∀ p : ℕ, p.Prime → p % 4 = 3 → discr (Kstar p) = -(p : ℤ) ∧ IsTotallyComplex (Kstar p) ∧ Module.finrank ℚ (Kstar p) = 2 ∧ ∃ s : Kstar p, s ^ 2 = -(p : Kstar p) := by
  intro p hp h3
  obtain ⟨K, _, _, hK2, hd⟩ := KStar.Consta.exists_quadField hp h3
  obtain ⟨⟨δ, hδ⟩, -⟩ := KStar.Choice.exists_sq_eq_neg_of_discr hK2 hp.ne_zero hd
  haveI : Polynomial.IsSplittingField ℚ (Kstar p) (Polynomial.X ^ 2 + Polynomial.C (p : ℚ)) := by
    have h := Polynomial.IsSplittingField.splittingField (K := ℚ) (Polynomial.X ^ 2 + Polynomial.C (p : ℚ))
    have h' : Polynomial.IsSplittingField ℚ (Polynomial.SplittingField (Polynomial.X ^ 2 + Polynomial.C (p : ℚ)))
        (Polynomial.X ^ 2 + Polynomial.C (p : ℚ)) := by
      convert h
    exact h'
  let f : Polynomial ℚ := Polynomial.X ^ 2 + Polynomial.C (p : ℚ)
  have hf0 : f ≠ 0 := by
    intro h
    have := congrArg (fun q : Polynomial ℚ => q.coeff 2) h
    simp [f] at this
  have hfac : f.map (algebraMap ℚ K) =
      (Polynomial.X + Polynomial.C δ) * (Polynomial.X + Polynomial.C (-δ)) := by
    have hpK : (p : K) = -(δ ^ 2) := by rw [hδ, neg_neg]
    dsimp only [f]
    rw [Polynomial.map_add (f := _), Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_C, map_natCast, hpK]
    simp only [map_neg, map_pow]
    ring
  have : IsSimpleOrder (Subalgebra ℚ K) :=
    Subalgebra.isSimpleOrder_of_finrank_prime ℚ K (by rw [hK2]; exact Nat.prime_two)
  have : Polynomial.IsSplittingField ℚ K f := by
    refine ⟨hfac ▸ (Polynomial.Splits.X_add_C _).mul (Polynomial.Splits.X_add_C _),
      (IsSimpleOrder.eq_bot_or_eq_top _).resolve_left fun hbot => ?_⟩
    have hδr : δ ∈ f.rootSet K :=
      (Polynomial.mem_rootSet_of_ne hf0).2 (by simp [f, hδ])
    obtain ⟨q, hq⟩ := Algebra.mem_bot.1 (hbot ▸ Algebra.subset_adjoin hδr)
    have hq2 : q ^ 2 + (p : ℚ) = 0 := (algebraMap ℚ K).injective (by
      rw [map_add, map_pow, map_natCast, hq, hδ, neg_add_cancel, map_zero])
    have hpq : (0 : ℚ) < p := Nat.cast_pos.2 hp.pos
    linarith [sq_nonneg q]
  let e : Kstar p ≃ₐ[ℚ] K := (Polynomial.IsSplittingField.algEquiv (Kstar p) f).trans
    (Polynomial.IsSplittingField.algEquiv K f).symm
  have hfr : Module.finrank ℚ (Kstar p) = 2 := e.toLinearEquiv.finrank_eq.trans hK2
  have hdisc : discr (Kstar p) = -(p : ℤ) := by
    rw [NumberField.discr_eq_discr_of_algEquiv (Kstar p) e, hd]
  obtain ⟨hs, htc⟩ := KStar.Choice.exists_sq_eq_neg_of_discr hfr hp.ne_zero hdisc
  exact ⟨hdisc, htc, hfr, hs⟩
