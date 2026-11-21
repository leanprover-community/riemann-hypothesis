import Mathlib
import Development.WeilBound.CoreStatements.HodgeTatePoints.CoeffEvPowOne
import BuildAid.ForwardExisting

section
namespace GlobalTheory.CompanionTheory.Ar.Conj

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

theorem pow_eq_ev_frobenius : ∀ (R : Type) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p] (d n : ℕ) (f : PS R n d),
    f ^ p = ev (fun j => ptPow R d p j) (MvPowerSeries.map (frobenius R p) f) :=
  PositivityTheory.HtPt.Cb.frob_subst

end GlobalTheory.CompanionTheory.Ar.Conj
end

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.power_series_pow_p_frobenius : ∀ (R : Type) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p] (d n : ℕ) (f : PS R n d), f ^ p = ev (fun j => ptPow R d p j) (MvPowerSeries.map (frobenius R p) f) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Conj.pow_eq_ev_frobenius
