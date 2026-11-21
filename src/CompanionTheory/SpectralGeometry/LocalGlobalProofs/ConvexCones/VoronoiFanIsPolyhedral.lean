import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarisationBaseFunctionProperties
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.PsdConeFinitelyManyOrbits
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.VorFunValueLe

section
set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan

theorem evalR_vorFun_eq (O : Type) [CommRing O] [Module.Finite ℤ O] (g : ℕ) {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] [Module.Finite ℤ X] {d : ℕ} {s : (Fin d → ℤ) →ₗ[ℤ] X} (hs : Function.Surjective s)
    (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) :
    evalR (vorFun O g) B = (fineDen g {1} : ℝ) *
      ((((1 : ℕ) : ℝ) + 1) ^ d)⁻¹ * ∑ y, classMin 1 (fun a b => B (s a) (s b)) y := by
  have h0 : zeroFun.eval X (fun a b => B a b) = 0 := by
    rw [zeroFun.eval_eq hs]
    rfl
  rw [evalR, vorFun, eval_baseFun, h0, Finset.sum_singleton, fineMean_eval_eq 1 hs, zero_add, mul_assoc]

theorem vorFun_homog_superadd : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O)
    (g : ℕ) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X],
    (∀ B ∈ psdCone bar X, ∀ t : ℝ, 0 ≤ t → evalR (vorFun O g) (t • B) = t * evalR (vorFun O g) B) ∧
    ∀ B ∈ psdCone bar X, ∀ B' ∈ psdCone bar X,
      evalR (vorFun O g) B + evalR (vorFun O g) B' ≤ evalR (vorFun O g) (B + B') := by
  intro O _ _ _ _ bar g X _ _ _
  have : Module.Finite ℤ X := Module.Finite.trans O X
  obtain ⟨d, s, hs⟩ := Module.Finite.exists_fin' ℤ X
  have hc : (0 : ℝ) ≤ (fineDen g {1} : ℝ) * ((((1 : ℕ) : ℝ) + 1) ^ d)⁻¹ := by positivity
  refine ⟨fun B _ t ht => ?_, fun B hB B' hB' => ?_⟩
  · rw [evalR_vorFun_eq O g hs, evalR_vorFun_eq O g hs]
    simp only [LinearMap.smul_apply, smul_eq_mul, classMin_smul ht, ← Finset.mul_sum]
    ring
  · rw [evalR_vorFun_eq O g hs, evalR_vorFun_eq O g hs, evalR_vorFun_eq O g hs, ← mul_add,
      ← Finset.sum_add_distrib]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y _ => ?_) hc
    simp only [LinearMap.add_apply]
    exact classMin_add_le (fun a => nonneg_of_mem_psdCone hB _) (fun a => nonneg_of_mem_psdCone hB' _) y

end GlobalTheory.CompanionTheory.Ar.Fan
end
end

section
section
set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan

theorem exists_least_points {X : Type} [AddCommGroup X] {n : ℕ} (r : (Fin n → ℤ) →ₗ[ℤ] X)
    (hr : Function.Surjective r) (β : LinearMap.BilinForm ℤ X) (hβ : ∀ y, 0 ≤ β y y) :
    ∃ a : (Fin n → ZMod (1 + 1)) → Fin n → ℤ, (∀ y, redV 1 (a y) = y) ∧ ∀ y, IsMin2 (toReal β) (r (a y)) := by
  have hmin : ∀ y : Fin n → ZMod (1 + 1), ∃ c : Fin n → ℤ, redV 1 c = y ∧
      ∀ c', redV 1 c' = y → β (r c) (r c) ≤ β (r c') (r c') := fun y => by
    obtain ⟨c0, h0⟩ := redV_surjective 1 n y
    obtain ⟨c, hc, hm⟩ := WellFounded.has_min
      (InvImage.wf (fun c : Fin n → ℤ => (β (r c) (r c)).toNat) Nat.lt_wfRel.wf)
      {c | redV 1 c = y} ⟨c0, h0⟩
    refine ⟨c, hc, fun c' hc' => ?_⟩
    have h1 : ¬ (β (r c') (r c')).toNat < (β (r c) (r c)).toNat := hm c' hc'
    have h2 := hβ (r c)
    have h3 := hβ (r c')
    omega
  choose a ha hm using hmin
  refine ⟨a, ha, fun y x => ?_⟩
  obtain ⟨d, rfl⟩ := hr x
  have h := hm y (a y + (((1 : ℕ) : ℤ) + 1) • d) (by rw [redV_add_smul, ha])
  have e : r (a y + (((1 : ℕ) : ℤ) + 1) • d) = r (a y) + (r d + r d) := by
    rw [map_add, map_smul, show (((1 : ℕ) : ℤ) + 1) = 2 by norm_num, two_smul]
  rw [e] at h
  simp only [toReal, LinearMap.compr₂_apply, Algebra.linearMap_apply, eq_intCast]
  exact_mod_cast h

theorem apply_eq_zero_of_self {X : Type} [AddCommGroup X] (β : LinearMap.BilinForm ℤ X) (hs : ∀ y z, β y z = β z y)
    (hβ : ∀ y, 0 ≤ β y y) {z : X} (hz : β z z = 0) (w : X) : β z w = 0 := by
  by_contra ht
  have h := hβ (w + (-(β w w + 1) * β z w) • z)
  simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, hz, hs w z] at h
  have h1 : 1 ≤ β z w * β z w := mul_self_pos.2 ht
  have h2 := hβ w
  nlinarith

theorem eq_zero_of_covers {X : Type} [AddCommGroup X] (β : LinearMap.BilinForm ℤ X) (hs : ∀ y z, β y z = β z y)
    (hβ : ∀ y, 0 ≤ β y y) {ι : Type} {a : ι → X} (hc : Covers2 a) (h0 : ∀ i, β (a i) (a i) = 0) : β = 0 := by
  have hdiv : ∀ (k : ℕ) (z w : X), (2 : ℤ) ^ k ∣ β z w := by
    intro k
    induction k with
    | zero => intro z w; simp
    | succ k ih =>
      intro z w
      obtain ⟨i, x, rfl⟩ := hc z
      obtain ⟨m, hm⟩ := ih x w
      refine ⟨m, ?_⟩
      simp only [map_add, LinearMap.add_apply, apply_eq_zero_of_self β hs hβ (h0 i) w, hm]
      ring
  refine LinearMap.ext₂ fun z w => ?_
  refine Int.eq_zero_of_abs_lt_dvd (hdiv (β z w).natAbs z w) ?_
  rw [Int.abs_eq_natAbs]
  exact_mod_cast Nat.lt_two_pow_self

theorem vorFun_int_pos : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (g q : ℕ)
    (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X],
    Module.finrank ℤ O * q ≤ g → Module.finrank O X ≤ q →
    (∀ β : LinearMap.BilinForm ℤ X, (∀ y, 0 ≤ β y y) → ∃ n : ℤ, (vorFun O g).evalZ β = n) ∧
    ∀ β : LinearMap.BilinForm ℤ X, (∀ y z, β y z = β z y) → (∀ y, 0 ≤ β y y) → β ≠ 0 → 0 < (vorFun O g).evalZ β := by
  intro O _ _ _ _ bar g q X _ _ _ _ hg hq
  have hfin : Module.Finite ℤ X := Module.Finite.trans O X
  have hO : Module.Free ℤ O := Module.free_of_finite_type_torsion_free'
  have htf : Module.IsTorsionFree ℤ X := Module.IsTorsionFree.trans O
  have hfree : Module.Free ℤ X := Module.free_of_finite_type_torsion_free'
  have hn : Module.finrank ℤ X ≤ g := by
    rw [GlobalTheory.finrank_int_eq_mul_of_finite (O := O) (M := X)]
    exact (Nat.mul_le_mul_left _ hq).trans hg
  let b : Module.Basis (Fin (Module.finrank ℤ X)) ℤ X := Module.finBasis ℤ X
  let r : (Fin (Module.finrank ℤ X) → ℤ) →ₗ[ℤ] X := b.equivFun.symm.toLinearMap
  have hr : Function.Surjective r := b.equivFun.symm.surjective
  have key : ∀ β : LinearMap.BilinForm ℤ X, (∀ y, 0 ≤ β y y) →
      ∃ a : (Fin (Module.finrank ℤ X) → ZMod (1 + 1)) → Fin (Module.finrank ℤ X) → ℤ, Covers2 (fun y => r (a y)) ∧
        (vorFun O g).evalZ β = 2 ^ (g - Module.finrank ℤ X) * ∑ y, (β (r (a y)) (r (a y)) : ℝ) := by
    intro β hβ
    obtain ⟨a, ha, hm⟩ := exists_least_points r hr β hβ
    obtain ⟨hc, h⟩ := vorFun_value_le O bar g X _ r a hr ha
    refine ⟨a, hc, ?_⟩
    have hB : ∀ y, 0 ≤ toReal β y y := fun y => by
      simp only [toReal, LinearMap.compr₂_apply, Algebra.linearMap_apply, eq_intCast]
      exact_mod_cast hβ y
    have h1 := ((h (toReal β) hB).2).2 hm
    rw [evalR_toReal] at h1
    have h2 : ∀ u v, toReal β u v = (β u v : ℝ) := fun u v => by
      simp only [toReal, LinearMap.compr₂_apply, Algebra.linearMap_apply, eq_intCast]
    simp only [h2] at h1
    have h3 : (2 : ℝ) ^ g = 2 ^ Module.finrank ℤ X * 2 ^ (g - Module.finrank ℤ X) := by
      rw [← pow_add, Nat.add_sub_cancel' hn]
    rw [h3, mul_assoc] at h1
    exact mul_left_cancel₀ (by positivity) h1
  refine ⟨fun β hβ => ?_, fun β hs hβ hne => ?_⟩
  · obtain ⟨a, -, h⟩ := key β hβ
    exact ⟨2 ^ (g - Module.finrank ℤ X) * ∑ y, β (r (a y)) (r (a y)), by rw [h]; push_cast; rfl⟩
  · obtain ⟨a, hc, h⟩ := key β hβ
    have hnn : ∀ y, (0 : ℝ) ≤ (β (r (a y)) (r (a y)) : ℝ) := fun y => by exact_mod_cast hβ _
    rw [h]
    refine mul_pos (by positivity) (lt_of_le_of_ne (Finset.sum_nonneg fun y _ => hnn y) fun h0 => hne ?_)
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg fun y _ => hnn y).1 h0.symm
    exact eq_zero_of_covers β hs hβ hc fun y => by exact_mod_cast h1 y (Finset.mem_univ y)

end GlobalTheory.CompanionTheory.Ar.Fan
end
end

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.voronoi_function_integral_positive : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (g q : ℕ) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank ℤ O * q ≤ g → Module.finrank O X ≤ q → (∀ β : LinearMap.BilinForm ℤ X, (∀ y, 0 ≤ β y y) → ∃ n : ℤ, (vorFun O g).evalZ β = n) ∧ ∀ β : LinearMap.BilinForm ℤ X, (∀ y z, β y z = β z y) → (∀ y, 0 ≤ β y y) → β ≠ 0 → 0 < (vorFun O g).evalZ β := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Fan.vorFun_int_pos
end

section
section
set_option autoImplicit false

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan

theorem vorFun_isPolyFan : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (g q : ℕ),
    (∀ (Y : Type) [AddCommGroup Y] [Module O Y] [Module.Finite O Y] [Module.Projective O Y], HasRedCover bar Y) →
    Module.finrank ℤ O * q ≤ g → IsPolyFan bar q (vorFun O g) := by
  intro O _ _ _ _ bar g q hred hg X _ _ _ _ hX
  obtain ⟨hhom, hsup⟩ := vorFun_homog_superadd O bar g X
  obtain ⟨hint, hpos⟩ := GlobalTheory.T.voronoi_function_integral_positive O bar g q X hg hX
  exact
    { homog := hhom
      superadd := hsup
      integral := fun β _ h => hint β h
      pos := fun β hβ h h0 => hpos β hβ.1 h h0
      finite := GlobalTheory.T.psd_cone_finitely_many_orbits O bar g hred X }

end GlobalTheory.CompanionTheory.Ar.Fan
end

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan
theorem _root_.GlobalTheory.T.voronoi_fan_is_polyhedral : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (g q : ℕ), (∀ (Y : Type) [AddCommGroup Y] [Module O Y] [Module.Finite O Y] [Module.Projective O Y], HasRedCover bar Y) → Module.finrank ℤ O * q ≤ g → IsPolyFan bar q (vorFun O g) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Fan.vorFun_isPolyFan
end
