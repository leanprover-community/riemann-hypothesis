module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CanonB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasisBaseChange

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Chart

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.Canon
open scoped CategoryTheory.Obj

variable {R : Type} [CommRing R] {σ τ : Type} [Finite σ] [Finite τ]

def pj (m : ℕ) (f : MvPowerSeries σ R) : JetR R σ m := Ideal.Quotient.mk _ (truncTotal (m + 1) f)

theorem pj_eq_mk {m : ℕ} {f : MvPowerSeries σ R} {q : MvPolynomial σ R} :
    pj m f = Ideal.Quotient.mk _ q ↔ ∀ e : σ →₀ ℕ, e.degree < m + 1 → coeff e f = q.coeff e := by
  rw [pj, Ideal.Quotient.eq, MvPolynomial.mem_pow_idealOfVars_iff']
  exact forall₂_congr fun e he => by rw [MvPolynomial.coeff_sub, coeff_truncTotal _ he, sub_eq_zero]

theorem pj_ext {f g : MvPowerSeries σ R} (h : ∀ m, pj m f = pj m g) : f = g := by
  ext e
  exact (pj_eq_mk.1 (h e.degree) e (Nat.lt_succ_self _)).trans (coeff_truncTotal _ (Nat.lt_succ_self _))

variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {d : ℕ} (x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin d) m) ⟶ G) {n l : ℕ}

variable {x} (hx : IsUnivChart G d x)
include hx

end ReciprocityTheory.ChartRestriction.G.Chart
