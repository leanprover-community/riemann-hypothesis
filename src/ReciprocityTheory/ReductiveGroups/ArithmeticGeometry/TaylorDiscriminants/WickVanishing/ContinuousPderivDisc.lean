module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg

@[expose] public section

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ReciprocityTheory.ChartRestriction.G.TB

theorem constSt : ConstSt := by
  intro k _ d φ hφ g
  have ha : ∀ p : Fin 1 × Fin d, constantCoeff (![φ] p.1 p.2) = 0 := by
    rintro ⟨i, j⟩
    fin_cases i
    simpa using hφ j
  have hs : MvPowerSeries.HasSubst (fun p : Fin 1 × Fin d => ![φ] p.1 p.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  unfold ev
  rw [MvPowerSeries.constantCoeff_subst hs, finsum_eq_single _ 0]
  · simp
  · intro e he
    obtain ⟨p, hp⟩ : ∃ p, e p ≠ 0 := by
      by_contra h
      push_neg at h
      exact he (Finsupp.ext h)
    have h0 : constantCoeff (e.prod fun s n => (![φ] s.1 s.2) ^ n) = 0 := by
      rw [Finsupp.prod, map_prod]
      apply Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hp)
      rw [map_pow, ha p, zero_pow hp]
    rw [h0, smul_zero]

open scoped MvPowerSeries.WithPiTopology

end ReciprocityTheory.ChartRestriction.G.TB
