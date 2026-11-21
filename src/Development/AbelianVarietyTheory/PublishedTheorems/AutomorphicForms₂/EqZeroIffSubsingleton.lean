import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral

noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM

namespace GlobalTheory.SiegelTor

section Param

variable {o R : Type} [CommRing o] [CommRing R] [IsLocalRing R] {m : ℕ} {b : o →+* R} {t : Fin m → R}

theorem IsRelParam.notMem_sq (h : IsRelParam b t) (i : Fin m) : t i ∉ maximalIdeal R ^ 2 := fun hi => by
  have := h.mem_of_mem_sq (Pi.single i 1) (by simpa [Pi.single_apply] using hi) i
  simp at this

theorem IsRelParam.ne_zero (h : IsRelParam b t) (i : Fin m) : t i ≠ 0 := fun h0 => h.notMem_sq i (h0 ▸ zero_mem _)

theorem IsRelParam.eq_of_dvd (h : IsRelParam b t) {i j : Fin m} (hd : t i ∣ t j) : i = j := by
  by_contra hne
  obtain ⟨c, hc⟩ := hd
  have := h.mem_of_mem_sq (Pi.single j 1 - Pi.single i c)
    (by simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]; simp [Pi.single_apply, hc, mul_comm c]) j
  simp [Ne.symm hne] at this

end Param

section Local

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {m : ℕ}



omit [IsLocalRing R] in

theorem not_isMonomial_of_odd (D : DegPre R) (t : Fin 1 → R) (γ : LinearMap.BilinForm ℤ D.X) {y : D.X} (hy : γ y y = 1)
    {n : ℕ} (hn : Odd n) : ¬ IsMonomial D t fun _ => (n : ℤ) • γ := fun h => by
  obtain ⟨u, e, he, -⟩ := h y
  have := he 0
  obtain ⟨a, rfl⟩ := hn
  simp [hy] at this
  omega

end Local

section Charts

variable {o : Type} [CommRing o] {ζ : o} {g n : ℕ} {F : SFam g n ζ} {S : Scheme.{0}} {s : S ⟶ Sp o} {j : F.X ⟶ S}
  {G : Over S} [GrpObj G] {e : F.univ.A.left ⟶ G.left}


end Charts

theorem exists_support (h : GlobalTheory.Published.SiegelToroidalIntegral) {g n : ℕ} (hg : 1 ≤ g) (hn : 3 ≤ n) (ho : Odd n) :
    ∃ (S : Scheme.{0}) (s : S ⟶ Sp (cycAway n)) (G : Over S) (_ : GrpObj G) (BD : EffCartierData S) (k : ℕ),
      IsProjOver s ∧ IsSemiAbelian G ∧ IsAmpleLB (CechPic.tens (lbPow (hodge G g) k) (CechPic.dual BD.lb)) ∧
      ∀ x, ReciprocityTheory.AnForm.R.FinalTheorems.stalkId BD.idealSheaf x = ⊤ ↔ x ∈ abLocus G := by
  obtain ⟨φ, hφ, h⟩ := h g hg
  obtain ⟨F, S, s, j, _, G, _, e, BD, d, N, h1, -, -, -, h2, -, -, h3, hd, hc, -, -, k₀, hk⟩ := h n hn ho
  exact ⟨S, s, G, _, BD, _, h1, h2, hk k₀ le_rfl, fun x => h3 ▸ (hc x).idl_eq_top_iff hφ (by omega) (by omega)⟩

end GlobalTheory.SiegelTor
