module

public import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor

noncomputable section

namespace GlobalTheory.Poinc

theorem nnnorm_le_of_mem_span {R K : Type} [CommRing R] [NormedField K] [IsUltrametricDist K] (v : R →+* K)
    (hv : ∀ r, ‖v r‖₊ ≤ 1) {s : Set R} {ρ : NNReal} (hs : ∀ c ∈ s, ‖v c‖₊ ≤ ρ) :
    ∀ c ∈ Ideal.span s, ‖v c‖₊ ≤ ρ := by
  intro c hc
  induction hc using Submodule.span_induction with
  | mem x hx => exact hs x hx
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add (f := _)]
    exact (IsUltrametricDist.nnnorm_add_le_max _ _).trans (max_le hx hy)
  | smul a x _ hx =>
    rw [smul_eq_mul, map_mul, nnnorm_mul]
    exact (mul_le_mul' (hv a) hx).trans (by rw [one_mul])

theorem nnnorm_le_pow_of_mem_pow {R K : Type} [CommRing R] [NormedField K] [IsUltrametricDist K] (v : R →+* K)
    (hv : ∀ r, ‖v r‖₊ ≤ 1) {I : Ideal R} {ρ : NNReal} (hI : ∀ c ∈ I, ‖v c‖₊ ≤ ρ) :
    ∀ k : ℕ, ∀ b ∈ I ^ k, ‖v b‖₊ ≤ ρ ^ k := by
  intro k
  induction k with
  | zero => intro b _; simpa using hv b
  | succ k ih =>
    intro b hb
    rw [pow_succ] at hb
    refine Submodule.mul_induction_on hb ?_ ?_
    · intro a ha c hc
      rw [map_mul, nnnorm_mul, pow_succ]
      exact mul_le_mul' (ih a ha) (hI c hc)
    · intro a c ha hc
      rw [map_add (f := _)]
      exact (IsUltrametricDist.nnnorm_add_le_max _ _).trans (max_le ha hc)

end GlobalTheory.Poinc

namespace GlobalTheory.Poinc

end GlobalTheory.Poinc
