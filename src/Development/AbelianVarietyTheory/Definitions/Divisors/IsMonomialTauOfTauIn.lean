import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBase

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Sep.Model

variable {V : Type} [CommRing V] [IsDomain V]

theorem exists_tauIn {Q : Data V} {N : ℕ} {s : Fin N → V} {ε : Fin N → LinearMap.BilinForm ℤ Q.X}
    (h : Q.IsMonomialTau s ε) : ∃ τ₀ : Gens Q, TauIn Q τ₀ s ε := by
  have h' : ∀ a b : Q.X, ∃ k : (FractionRing V)ˣ,
      (k : FractionRing V) = ∏ i, algebraMap V (FractionRing V) (s i) ^ ε i a b ∧ Q.TauCoord a b k := h

  choose k hk hc using h'
  refine ⟨fun a b => Exists.choose (hc a b), fun a b => ⟨(Exists.choose_spec (hc a b)).1, k a b, hk a b, ?_⟩⟩
  exact (Exists.choose_spec (hc a b)).2

theorem isMonomialTau_of_tauIn {Q : Data V} {τ₀ : Gens Q} {N : ℕ} {s : Fin N → V}
    {ε : Fin N → LinearMap.BilinForm ℤ Q.X} (h : TauIn Q τ₀ s ε) : Q.IsMonomialTau s ε := by
  intro a b
  obtain ⟨hg, k, hk, hv⟩ := h a b
  exact ⟨k, hk, Exists.intro (τ₀ a b) ⟨hg, hv⟩⟩



end GlobalTheory.Poinc.Sep.Model
