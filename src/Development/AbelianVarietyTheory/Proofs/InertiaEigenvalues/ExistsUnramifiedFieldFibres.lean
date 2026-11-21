import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUnitaryOfTraceEq
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsDatumRankOne
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CoeffFieldAlgClosedFunctionFieldOfTorsionDefined
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CmHostRootComplexEqPmSqrt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CyclotomicCharacterEqCmMultiplierNorm
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CmCurveTorsionDefinedOverOfWeberValues
import Development.AbelianVarietyTheory.Proofs.HeightProofs.WeberValuesFiniteAlgebraicPermuted
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsMonHomOfMapLattice
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FixesRootOfActsTorsion
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MultiplierIffExistsHom
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MkLeContinuumOfDenseRange
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MulPowTwoLeTripleProdOfGe
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsGoodReductionAlgebraicWeierstrassModel
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralJAndAlgebraicData

section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompRat.Inertia

open GlobalTheory.WeierstrassCurve GlobalTheory.UnifCoord GlobalTheory.PeriodicWeierstrass PeriodPair GlobalTheory.CompRat.Weber

theorem fibre_coord (W : WeierstrassCurve ℂ) (hb : W.b₂ = 0) {P₀ : Out.PolAV (Sp ℂ)} {ψ₀ : P₀.A.left ⟶ scheme W}
    [IsIso ψ₀] (hψ₀ : ψ₀ ≫ toSpec W = P₀.A.hom) (he : eSec P₀.A ≫ ψ₀ = zero W) {v : epsR ℂ ⟶ P₀.A}
    (hvt : IsTangent v) {h : IsUnimodularSol (W.map (algebraMap ℂ (DualNumber ℂ))) ![DualNumber.eps, -1, 0]}
    (hv : v.left ≫ ψ₀ = ptHom W (algebraMap ℂ (DualNumber ℂ)) ![DualNumber.eps, -1, 0] h) (f : ℂ →+* ℂ)
    (PC : Out.PolAV (Sp ℂ)) (hg1 : PC.g = 1) (u : HolUnif PC.A PC.L PC.g) (hu : IsThetaUnif u)
    {ψ : PC.A.left ⟶ P₀.A.left} (hψ : IsGrpPullback PC.A P₀.A (spMap f) ψ) :
    ∃ (w : Fin PC.g → ℂ) (L' : PeriodPair), w ≠ 0 ∧ (∀ z, z ∈ L'.lattice ↔ z • w ∈ u.Λ) ∧
      f W.c₄ = 12 * L'.g₂ ∧ f W.c₆ = 216 * L'.g₃ ∧
      ∀ z : ℂ, ∃ (P : Fin 3 → ℂ) (hP : IsUnimodularSol (W.map f) P),
        (u.ex (z • w)).left ≫ ψ ≫ ψ₀ = ptHom W f P hP ∧ (P 2 = 0 ↔ z ∈ L'.lattice) ∧
          (P 2 ≠ 0 → ℘[L'] z * P 2 = P 0) := by
  obtain ⟨v', hv't, hv'⟩ := exists_tangent_over f hψ hvt
  obtain ⟨w, hd, -⟩ := hu.choose_spec.choose_spec.choose_spec.2.1 v' hv't
  obtain ⟨h', h1, h2, h3⟩ := fibre_over_scheme W f hψ₀ he hv hψ hv'
  obtain ⟨hw, x, y, t, hP, hx, hy, hper, heq, ht, ht0, ht1, hty, hlim⟩ :=
    exists_coord_eq ℂ W f PC.A (ψ ≫ ψ₀) v' h' h1 h2 h3 PC.L PC.g u w hd
  obtain ⟨L', hL'⟩ := exists_periodPair_of_lattice_in_line PC.g u.Λ w hg1 hw u.discrete u.full
  have hset : (L'.lattice : Set ℂ) = {z | z • w ∈ u.Λ} := Set.ext hL'
  have key := invariants_eq_of_periodic_solution L' (W.map f) x y t 1 one_ne_zero (hset ▸ hx) (hset ▸ hy)
    (fun l hl => hper l ((hL' l).1 hl)) (fun z hz => heq z fun e => hz ((hL' z).2 e)) ht ht0 ht1 hty hlim
  have kx := x_eq_of_periodic_solution L' (W.map f) x y t 1 one_ne_zero (hset ▸ hx) (hset ▸ hy)
    (fun l hl => hper l ((hL' l).1 hl)) (fun z hz => heq z fun e => hz ((hL' z).2 e)) ht ht0 ht1 hty hlim
  simp only [one_pow, _root_.one_mul, WeierstrassCurve.map_c₄, WeierstrassCurve.map_c₆, WeierstrassCurve.map_b₂,
    hb, map_zero, zero_div, sub_zero] at key kx
  refine ⟨w, L', hw, hL', key.1, key.2.1, fun z => ?_⟩
  obtain ⟨P, hP, e1, e2, e3⟩ := hP z
  refine ⟨P, hP, e1, by rw [e2, hL'], fun h2 => ?_⟩
  rw [← e3 h2, kx _ fun hz => h2 (e2.2 ((hL' _).1 hz))]

theorem exists_hom_of_lattice (P Q : Out.PolAV (Sp ℂ)) (g1 : P.g = 1) (g2 : Q.g = 1) (u : HolUnif P.A P.L P.g)
    (u' : HolUnif Q.A Q.L Q.g) (hu : IsThetaUnif u) (hu' : IsThetaUnif u') (L : PeriodPair) (w : Fin P.g → ℂ)
    (w' : Fin Q.g → ℂ) (w0 : w ≠ 0) (w0' : w' ≠ 0) (hΛ : ∀ z, z ∈ L.lattice ↔ z • w ∈ u.Λ)
    (hΛ' : ∀ z, z ∈ L.lattice ↔ z • w' ∈ u'.Λ) :
    ∃ f : P.A ⟶ Q.A, IsMonHom f ∧ ∀ z : ℂ, u'.ex (z • w') = u.ex (z • w) ≫ f := by
  obtain ⟨Hm, χ, Ef, hA, -, -, hθ, hE, hEb⟩ := hu
  obtain ⟨Hm', χ', Ef', hA', -, -, hθ', hE', hEb'⟩ := hu'
  have hH := hermForm_principal_dim_one _ u.Λ w L Hm Ef g1 w0 hΛ hA.1 (hA.2.1 w w0) hE hEb
  have hH' := hermForm_principal_dim_one _ u'.Λ w' L Hm' Ef' g2 w0' hΛ' hA'.1 (hA'.2.1 w' w0') hE' hEb'
  obtain ⟨c, hc, hc1⟩ := EllipticHom.exists_coord g1 w0
  let F : (Fin P.g → ℂ) →ₗ[ℂ] (Fin Q.g → ℂ) := c.smulRight w'
  have hF : ∀ x, F x = c x • w' := fun x => rfl
  obtain ⟨f, hf, hFf⟩ := exists_hom_of_linear_scaling_hermForm P Q u u' Hm χ Hm' χ' hA hA'
    (fun k => (hθ k).2) (fun k => (hθ' k).1) F 1
    (fun l hl => by
      rw [hF, ← hΛ']
      exact (hΛ _).2 (by rwa [hc]))
    (fun x y => by
      have e := hH (c x) (c y)
      rw [hc, hc] at e
      rw [hF, hF, hH', e, Nat.cast_one, _root_.one_mul])
  refine ⟨f, hf, fun z => ?_⟩
  rw [← hFf, hF, map_smul, hc1, smul_eq_mul, _root_.mul_one]

theorem exists_isGrpPullback_of_lattice (P Q : Out.PolAV (Sp ℂ)) (g1 : P.g = 1) (g2 : Q.g = 1)
    (u : HolUnif P.A P.L P.g)
    (u' : HolUnif Q.A Q.L Q.g) (hu : IsThetaUnif u) (hu' : IsThetaUnif u') (L : PeriodPair) (w : Fin P.g → ℂ)
    (w' : Fin Q.g → ℂ) (w0 : w ≠ 0) (w0' : w' ≠ 0) (hΛ : ∀ z, z ∈ L.lattice ↔ z • w ∈ u.Λ)
    (hΛ' : ∀ z, z ∈ L.lattice ↔ z • w' ∈ u'.Λ) :
    ∃ φ : P.A.left ⟶ Q.A.left, IsGrpPullback P.A Q.A (𝟙 _) φ := by
  obtain ⟨f, hf, e⟩ := exists_hom_of_lattice P Q g1 g2 u u' hu hu' L w w' w0 w0' hΛ hΛ'
  obtain ⟨f', hf', e'⟩ := exists_hom_of_lattice Q P g2 g1 u' u hu' hu L w' w w0' w0 hΛ' hΛ
  obtain ⟨c, hc, -⟩ := EllipticHom.exists_coord g1 w0
  obtain ⟨c', hc', -⟩ := EllipticHom.exists_coord g2 w0'
  have := P.isAb.smooth
  have := Q.isAb.smooth
  have := P.isAb.proper
  have := Q.isAb.proper
  have : IsReduced P.A.left := isReduced_of_smooth_complex _ P.A.hom inferInstance
  have : IsReduced Q.A.left := isReduced_of_smooth_complex _ Q.A.hom inferInstance
  let i : P.A ≅ Q.A :=
    { hom := f
      inv := f'
      hom_inv_id := ComplexPoints.over_hom_ext_of_complexPoints fun x => by
        obtain ⟨z, rfl⟩ := u.ex_onto x
        rw [← hc z, ← Category.assoc, ← e, ← e', Category.comp_id]
      inv_hom_id := ComplexPoints.over_hom_ext_of_complexPoints fun x => by
        obtain ⟨z, rfl⟩ := u'.ex_onto x
        rw [← hc' z, ← Category.assoc, ← e', ← e, Category.comp_id] }
  have : IsMonHom i.hom := hf
  exact ⟨_, isGrpPullback_of_iso i⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem mem_iff (C : Curve H) {L : PeriodPair} (hL : ∀ x, x ∈ L.lattice ↔ ∃ s, x = wC H s) (z : ℂ) :
    z ∈ L.lattice ↔ (fun _ => C.c * z : Fin C.P.g → ℂ) ∈ C.u.Λ := by
  have i : Fin C.P.g := ⟨0, by rw [C.g_eq]; omega⟩
  rw [hL, exists_wC_iff, C.lat]
  exact ⟨fun ⟨m, n, h⟩ => ⟨m, n, by rw [h]⟩, fun ⟨m, n, h⟩ => ⟨m, n, mul_left_cancel₀ C.c_ne (congrFun h i)⟩⟩

theorem curve_coord (C : Curve H) {L : PeriodPair} (hL : ∀ x, x ∈ L.lattice ↔ ∃ s, x = wC H s)
    (W : WeierstrassCurve ℂ) (hb : W.b₂ = 0) {P₀ : Out.PolAV (Sp ℂ)} {ψ₀ : P₀.A.left ⟶ scheme W}
    [IsIso ψ₀] (hψ₀ : ψ₀ ≫ toSpec W = P₀.A.hom) (he : eSec P₀.A ≫ ψ₀ = zero W) {v : epsR ℂ ⟶ P₀.A}
    (hvt : IsTangent v) {h : IsUnimodularSol (W.map (algebraMap ℂ (DualNumber ℂ))) ![DualNumber.eps, -1, 0]}
    (hv : v.left ≫ ψ₀ = ptHom W (algebraMap ℂ (DualNumber ℂ)) ![DualNumber.eps, -1, 0] h) (f : ℂ →+* ℂ)
    {ψ : C.P.A.left ⟶ P₀.A.left} (hψ : IsGrpPullback C.P.A P₀.A (spMap f) ψ) :
    ∃ lam : ℂ, lam ≠ 0 ∧ ∀ z : ℂ, ∃ (P : Fin 3 → ℂ) (hP : IsUnimodularSol (W.map f) P),
        C.pt z ≫ ψ ≫ ψ₀ = ptHom W f P hP ∧ (P 2 = 0 ↔ z ∈ L.lattice) ∧
          (P 2 ≠ 0 → lam * ℘[L] z * P 2 = P 0) := by
  obtain ⟨w, L', hw, hL', -, -, hP⟩ := fibre_coord W hb hψ₀ he hvt hv f C.P C.g_eq C.u C.theta hψ
  obtain ⟨c, hc, -⟩ := EllipticHom.exists_coord C.g_eq hw
  set m := c fun _ => C.c with hm
  have e : ∀ z : ℂ, (fun _ => C.c * z : Fin C.P.g → ℂ) = (m * z) • w := fun z => by
    rw [_root_.mul_comm m, ← smul_smul, hm, hc]
    funext _
    simp [_root_.mul_comm]
  have hh : IsHomothetic m L L' := fun x => by rw [hL', ← e, ← mem_iff C hL]
  refine ⟨(m ^ 2)⁻¹, inv_ne_zero (pow_ne_zero _ hh.ne_zero), fun z => ?_⟩
  obtain ⟨P, hP, e1, e2, e3⟩ := hP (m * z)
  refine ⟨P, hP, by unfold Curve.pt; rw [e]; exact e1, by rw [e2, hh], fun h2 => ?_⟩
  rw [← e3 h2, hh.weierstrassP_mul]

theorem exists_multiplier (C : Curve H) {L : PeriodPair} (hL : ∀ x, x ∈ L.lattice ↔ ∃ s, x = wC H s)
    {τ : ℂ ≃+* ℂ} {io : C.P.A.left ⟶ C.P.A.left} (h : IsGrpPullback C.P.A C.P.A (spMap (τ : ℂ →+* ℂ)) io) :
    ∃ a : ℂ, ∀ z z', C.pt z ≫ io = spMap (τ : ℂ →+* ℂ) ≫ C.pt z' → z' ∉ L.lattice →
      z ∉ L.lattice ∧ τ (℘[L] z') = a * ℘[L] z := by
  let W := latticeCurve L
  have hb : W.b₂ = 0 := by simp [W, latticeCurve, WeierstrassCurve.b₂]
  have h4 : W.c₄ = 12 * L.g₂ := latticeCurve_c₄ L
  have h6 : W.c₆ = 216 * L.g₃ := by
    simp only [W, latticeCurve, WeierstrassCurve.c₆, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
    ring
  have hid : spMap (RingHom.id ℂ) = 𝟙 (Sp ℂ) := Spec.map_id (CommRingCat.of ℂ)
  obtain ⟨P₀, ψ₀, v, hg, hiso, hψ₀, he, ⟨hs, hv⟩, hlie⟩ := exists_polAV ℂ W (latticeCurve_Δ_ne_zero L).isUnit
  obtain ⟨u, hu⟩ := exists_isThetaUnif thetaUnifAV_all P₀
  have : IsMonHom (Iso.refl P₀.A).hom := inferInstanceAs (IsMonHom (𝟙 _))
  obtain ⟨w, L', hw, hL', e4, e6, -⟩ := fibre_coord W hb hψ₀ he (hlie.1 0) hv (RingHom.id ℂ) P₀ hg u hu
    ((isGrpPullback_of_iso (Iso.refl P₀.A)).congr hid.symm rfl)
  have eL : L'.lattice = L.lattice :=
    lattice_eq_of_g₂_eq_of_g₃_eq (by rw [RingHom.id_apply, h4] at e4; linear_combination -e4 / 12)
      (by rw [RingHom.id_apply, h6] at e6; linear_combination -e6 / 216)
  obtain ⟨φ, hφ⟩ := exists_isGrpPullback_of_lattice C.P P₀ C.g_eq hg C.u u C.theta hu L (fun _ => C.c) w
    (fun e => C.c_ne (congrFun e ⟨0, by rw [C.g_eq]; omega⟩)) hw
    (fun z => by
      rw [mem_iff C hL]
      congr! 2
      simp [_root_.mul_comm])
    (fun z => by rw [← eL, hL'])
  obtain ⟨l₁, hl₁, hQ⟩ := curve_coord C hL W hb hψ₀ he (hlie.1 0) hv (RingHom.id ℂ) (hφ.congr hid.symm rfl)
  obtain ⟨l₂, -, hP⟩ := curve_coord C hL W hb hψ₀ he (hlie.1 0) hv (τ : ℂ →+* ℂ)
    ((h.comp hφ).congr (Category.comp_id _) rfl)
  have ht : τ l₁ ≠ 0 := by simpa using hl₁
  refine ⟨l₂ / τ l₁, fun z z' e hz' => ?_⟩
  obtain ⟨P, hP1, a1, a2, a3⟩ := hP z
  obtain ⟨Q, hQ1, b1, b2, b3⟩ := hQ z'
  have e2 : C.pt z ≫ (io ≫ φ) ≫ ψ₀ = spMap (τ : ℂ →+* ℂ) ≫ C.pt z' ≫ φ ≫ ψ₀ := by
    simp only [← Category.assoc, e]
  have hτ : (τ : ℂ →+* ℂ).comp (RingHom.id ℂ) = (τ : ℂ →+* ℂ) := rfl
  have hQ2 := hQ1.map_comp (τ : ℂ →+* ℂ)
  rw [hτ] at hQ2
  rw [a1, b1, SpecMap_ptHom, ptHom_congr W _ _ _ hτ rfl hQ2, ptHom_eq_ptHom_iff] at e2
  obtain ⟨v, hv⟩ := e2
  have v0 : τ (Q 0) = v * P 0 := congrFun hv 0
  have v2 : τ (Q 2) = v * P 2 := congrFun hv 2
  have hQ0 : Q 2 ≠ 0 := fun h => hz' (b2.1 h)
  have hQ0' : τ (Q 2) ≠ 0 := by simpa using hQ0
  have hP0 : P 2 ≠ 0 := right_ne_zero_of_mul (v2 ▸ hQ0')
  refine ⟨fun h => hP0 (a2.2 h), ?_⟩
  have e3 : τ l₁ * τ (℘[L] z') * τ (Q 2) = l₂ * ℘[L] z * τ (Q 2) := by
    rw [← map_mul, ← map_mul, b3 hQ0, v0, v2, ← a3 hP0]
    ring
  have e4 := mul_right_cancel₀ hQ0' e3
  field_simp
  linear_combination e4

end GlobalTheory.CompRat.Inertia
end
end

section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.MomOne PeriodPair

namespace GlobalTheory.CompRat.Inertia

theorem exists_ringEquiv (p : ℕ) [hp : Fact p.Prime] (A : ValuationSubring ℂ) (hA : (p : ℂ) ∈ A.nonunits) :
    ∃ ι : ℂ ≃+* ℂ_[p], ∀ x : ℂ, IsAlgebraic ℚ x → (x ∈ A ↔ ‖ι x‖ ≤ 1) := by
  let Ω := algebraicClosure ℚ ℂ
  have : IsAlgClosure ℚ Ω := algebraicClosure.isAlgClosure ℚ ℂ
  let B : ValuationSubring Ω := A.comap (algebraMap Ω ℂ)
  have hB : B.valuation (p : Ω) < 1 := by
    rw [← ValuationSubring.mem_nonunits_iff, ValuationSubring.mem_nonunits_iff_or] at *
    refine hA.imp (fun h => absurd (by exact_mod_cast h) hp.out.ne_zero) fun h h' => h ?_
    have : algebraMap Ω ℂ (p : Ω)⁻¹ ∈ A := h'
    simpa using this
  have hpr : Prime (p : 𝓞 ℚ) := by
    have := (MulEquiv.prime_iff Rat.ringOfIntegersEquiv.symm).2 (Nat.prime_iff_prime_int.1 hp.out)
    simpa using this
  let w : HeightOneSpectrum (𝓞 ℚ) := ⟨Ideal.span {(p : 𝓞 ℚ)}, (Ideal.span_singleton_prime hpr.ne_zero).2 hpr,
    by simpa using hpr.ne_zero⟩
  obtain ⟨j, hj⟩ := GlobalTheory.PlaceBridge.exists_embedding (l := p) ℚ Ω w B (Ideal.mem_span_singleton_self _) fun x => by
    obtain ⟨n, rfl⟩ := Rat.ringOfIntegersEquiv.symm.surjective x
    have e : algebraMap ℚ Ω ((Rat.ringOfIntegersEquiv.symm n : 𝓞 ℚ) : ℚ) = (n : Ω) := by simp
    rw [e, GlobalTheory.PlaceBridge.val_int_lt_one_iff B hp.out hB]
    change _ ↔ _ ∈ Ideal.span _
    rw [Ideal.mem_span_singleton, ← map_dvd_iff Rat.ringOfIntegersEquiv]
    simp
  obtain ⟨ι, hι⟩ := GlobalTheory.PadicComplexIso.exists_ringEquiv_extending p ((algebraMap (PadicAlgCl p) ℂ_[p]).comp j)
  refine ⟨ι, fun x hx => ?_⟩
  have e := hι ⟨x, mem_algebraicClosure_iff.2 hx⟩
  rw [show ι x = _ from e, RingHom.comp_apply, ← PadicComplex.coe_eq, PadicComplex.norm_extends, ← hj]
  rfl

theorem exists_coord {d : ℕ} (hd : d.Prime) (hd' : d % 16 = 7) {L : PeriodPair} (hL : IsOK d L) {p : ℕ} (hp : p.Prime)
    (A : ValuationSubring ℂ) (hA : (p : ℂ) ∈ A.nonunits) {N : ℕ} (hN : ¬ p ∣ N) :
    ∃ (x : ℂ → ℂ) (α β : ℂ), α ≠ 0 ∧ (∀ z, x z = α * ℘[L] z + β) ∧
      (∀ z, (N : ℂ) * z ∈ L.lattice → z ∉ L.lattice → IsAlgebraic ℚ (x z) ∧ x z ∈ A) ∧
      ∀ z z', (N : ℂ) * z ∈ L.lattice → (N : ℂ) * z' ∈ L.lattice → z ∉ L.lattice → z' ∉ L.lattice →
        x z - x z' ∈ A.nonunits → z - z' ∈ L.lattice ∨ z + z' ∈ L.lattice := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨ι, hι⟩ := exists_ringEquiv p A hA
  obtain ⟨M, rfl, rfl, hM, h₁, h₂, h₃, h₄, h₆⟩ := exists_model d p ι L hd hd' hL
  obtain ⟨t1, t2⟩ := TorsionReduction.torsion_integral_and_distinct p M N hM
    ((Nat.Prime.coprime_iff_not_dvd hp).2 hN).symm
  have hN0 : 0 < N := Nat.pos_of_ne_zero (by rintro rfl; exact hN (dvd_zero _))
  let K := algebraicClosure ℚ ℂ_[p]
  have tr : ∀ y : ℂ, M.ι y ∈ K → y ∈ algebraicClosure ℚ ℂ := fun y hy =>
    mem_algebraicClosure_iff.2 ((isAlgebraic_algHom_iff (M.ι : ℂ →+* ℂ_[p]).toRatAlgHom M.ι.injective).1
      (mem_algebraicClosure_iff.1 hy))
  let W₀ : WeierstrassCurve K := ⟨⟨_, mem_algebraicClosure_iff.2 h₁⟩, ⟨_, mem_algebraicClosure_iff.2 h₂⟩,
    ⟨_, mem_algebraicClosure_iff.2 h₃⟩, ⟨_, mem_algebraicClosure_iff.2 h₄⟩, ⟨_, mem_algebraicClosure_iff.2 h₆⟩⟩
  have hW : W₀.map (algebraMap K ℂ_[p]) = M.W := rfl
  have hb : M.W.b₂ ∈ K := by rw [← hW, WeierstrassCurve.map_b₂]; exact W₀.b₂.2
  have h4 : M.W.c₄ ∈ K := by rw [← hW, WeierstrassCurve.map_c₄]; exact W₀.c₄.2
  have h6 : M.W.c₆ ∈ K := by rw [← hW, WeierstrassCurve.map_c₆]; exact W₀.c₆.2
  have hh := isHomothetic_scalePeriods M.L M.c hM.1
  generalize scalePeriods M.L M.c hM.1 = L' at hh
  have g2 : L'.g₂ ∈ algebraicClosure ℚ ℂ := tr _ (by
    rw [hh.g₂_eq, inv_mul_eq_div, ← hM.2.2.2.2.2.2.2.1]
    exact K.div_mem h4 (ofNat_mem K 12))
  have g3 : L'.g₃ ∈ algebraicClosure ℚ ℂ := tr _ (by
    rw [hh.g₃_eq, inv_mul_eq_div, ← hM.2.2.2.2.2.2.2.2]
    exact K.div_mem h6 (ofNat_mem K 216))
  have alg : ∀ z, (N : ℂ) * z ∈ M.L.lattice → z ∉ M.L.lattice → M.x z ∈ algebraicClosure ℚ ℂ := fun z hz hz' => by
    have h := (GlobalTheory.CurveAlgebraic.weierstrassP_mem L' (t := M.c * z) g2 g3 hN0 (by rwa [hh])
      (by rwa [mul_left_comm, hh])).1
    rw [hh.weierstrassP_mul, inv_mul_eq_div] at h
    exact sub_mem h (tr _ (by rw [RingEquiv.apply_symm_apply]; exact K.div_mem hb (ofNat_mem K 12)))
  refine ⟨M.x, (M.c ^ 2)⁻¹, -M.ι.symm (M.W.b₂ / 12), inv_ne_zero (pow_ne_zero _ hM.1), fun z => ?_,
    fun z hz hz' => ?_, fun z z' hz hz' h h' hx => ?_⟩
  · rw [Mdl.x]; ring
  · have ha := mem_algebraicClosure_iff.1 (alg z hz hz')
    exact ⟨ha, (hι _ ha).2 (t1 z hz hz')⟩
  · by_contra hc
    rw [not_or] at hc
    have e := t2 z z' hz hz' h h' hc.2 hc.1
    rw [← map_sub] at e
    rcases (ValuationSubring.mem_nonunits_iff_or A).1 hx with h0 | h0
    · simp [h0] at e
    · exact h0 ((hι _ (mem_algebraicClosure_iff.1 (inv_mem (sub_mem (alg z hz h) (alg z' hz' h'))))).2
        (by rw [map_inv₀, norm_inv, e, inv_one]))

end GlobalTheory.CompRat.Inertia
end
end

section
section
noncomputable section

open CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompRat PeriodPair

namespace GlobalTheory.CompRat.Inertia

open GlobalTheory.CompRat.Weber

theorem affine_sub_mem (A : ValuationSubring ℂ) {a b x₁ x₂ y : ℂ} (m₁ : x₁ ∈ A) (my : y ∈ A)
    (h : x₁ - x₂ ∉ A.nonunits) (h₁ : a * x₁ + b - x₁ ∈ A.nonunits) (h₂ : a * x₂ + b - x₂ ∈ A.nonunits) :
    a * y + b - y ∈ A.nonunits := by
  simp only [ValuationSubring.mem_nonunits_iff, not_lt] at *
  have e₁ : A.valuation ((a - 1) * (x₁ - x₂)) < 1 := by
    rw [show (a - 1) * (x₁ - x₂) = (a * x₁ + b - x₁) - (a * x₂ + b - x₂) by ring]
    exact Valuation.map_sub_lt _ h₁ h₂
  rw [map_mul] at e₁
  have e₂ : A.valuation (a - 1) < 1 := lt_of_le_of_lt (le_mul_of_one_le_right' h) e₁
  rw [show a * y + b - y = (a * x₁ + b - x₁) + (a - 1) * (y - x₁) by ring]
  refine Valuation.map_add_lt _ h₁ ?_
  rw [map_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_right' ((A.valuation_le_one_iff _).2 (sub_mem my m₁))) e₂

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem eq_zero_of_wC_eq_zero {s : ℤ × ℤ} (h : wC H s = 0) : s = 0 := by
  have hd : 0 < H.d := H.d_prime.pos
  have hs : Real.sqrt H.d ≠ 0 := by positivity
  have h2 : s.2 = 0 := by
    have := congrArg Complex.im h
    rcases cmHost_rootComplex_eq_pm_sqrt H with e | e <;> simpa [wC, e, hs, hd.ne'] using this
  have h1 : s.1 = 0 := by simpa [wC, h2] using h
  exact Prod.ext h1 h2

theorem dvd_of_div_mem {L : PeriodPair} (hL : ∀ x, x ∈ L.lattice ↔ ∃ s, x = wC H s) {k : ℕ} (hk : k ≠ 0) {s : ℤ × ℤ}
    (h : wC H s / k ∈ L.lattice) : (k : ℤ) ∣ s.1 ∧ (k : ℤ) ∣ s.2 := by
  obtain ⟨t, ht⟩ := (hL _).1 h
  have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk
  rw [div_eq_iff hk'] at ht
  have e : (s.1 - k * t.1, s.2 - k * t.2) = (0 : ℤ × ℤ) := eq_zero_of_wC_eq_zero (H := H) (by
    simp only [wC] at ht ⊢
    push_cast
    linear_combination ht)
  exact ⟨⟨t.1, sub_eq_zero.1 (congrArg Prod.fst e)⟩, ⟨t.2, sub_eq_zero.1 (congrArg Prod.snd e)⟩⟩

theorem fixesCurve_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (m n p : ℕ) (A : ValuationSubring ℂ) (τ : ℂ ≃+* ℂ), p.Prime → (p : ℂ) ∈ A.nonunits → ¬ p ∣ n → Nat.Coprime m n → 3 ≤ m / p ^ m.factorization p → FixesCurve H τ m → (∀ x : ℂ, IsAlgebraic ℚ x → x ∈ A → τ x - x ∈ A.nonunits) → FixesCurve H τ (m * n) := by
  rintro E _ _ _ H m n p A τ hp hA hn hmn h3 ⟨C, io, h, hfix⟩ hτ
  have hm0 : m ≠ 0 := by rintro rfl; simp at h3
  have hn0 : n ≠ 0 := by rintro rfl; exact hn (dvd_zero _)
  have hk : ¬ p ∣ m / p ^ m.factorization p := Nat.not_dvd_ordCompl hp hm0
  have hqk : p ^ m.factorization p * (m / p ^ m.factorization p) = m := Nat.ordProj_mul_ordCompl_eq_self m p
  generalize m / p ^ m.factorization p = k at h3 hk hqk
  generalize p ^ m.factorization p = q at hqk
  have hk0 : k ≠ 0 := by omega
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm0
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn0
  have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk0
  have hqk' : (q : ℂ) * k = m := by exact_mod_cast hqk
  have hOK := GlobalTheory.MomOne.Basic.isOK_okPair H.d H.d_prime.pos
  generalize GlobalTheory.MomOne.Basic.okPair H.d H.d_prime.pos = L at hOK
  have hL : ∀ x, x ∈ L.lattice ↔ ∃ s, x = wC H s := fun x => (hOK x).trans (exists_wC_iff H x).symm
  obtain ⟨c, hc⟩ := exists_multiplier C hL h
  obtain ⟨x, α, β, hα, hx, hint, hsep⟩ := exists_coord H.d_prime H.d_mod hOK hp A hA (N := k * n)
    fun hd => ((Nat.Prime.dvd_mul hp).1 hd).elim hk hn
  have hpt : ∀ z z', C.pt z = C.pt z' ↔ z - z' ∈ L.lattice := fun z z' => by rw [pt_eq_iff, hL]
  let T : ℂ → ℂ → Prop := fun z z' => C.pt z ≫ io = spMap (τ : ℂ →+* ℂ) ≫ C.pt z'
  have hm : ∀ a, T (wC H a / m) (wC H a / m) := fun a => by simpa [wC] using hfix a
  have h0 : T 0 0 := by simpa [wC] using hm 0
  have huniq : ∀ {z w z' w'}, T z z' → T w w' → z' - w' ∈ L.lattice → z - w ∈ L.lattice := fun {z w z' w'} a b e =>
    (hpt _ _).1 (conj_inj h (a.trans ((congrArg _ ((hpt _ _).2 e)).trans b.symm)))
  have hmul : ∀ {z z'}, T z z' → ∀ j : ℕ, T (j * z) (j * z') := fun {z z'} a j => by
    induction j with
    | zero => simpa using h0
    | succ j ih => simpa only [Nat.cast_succ, add_mul, one_mul] using conj_add h ih a
  have hkT : ∀ a, T (wC H a / k) (wC H a / k) := fun a => by
    have e : wC H ((q : ℤ) • a) / m = wC H a / k := by
      rw [← hqk'] at hm' ⊢
      have := left_ne_zero_of_mul hm'
      simp only [wC, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      push_cast
      field_simp
    exact e ▸ hm _
  have hkN : ∀ a, ((k * n : ℕ) : ℂ) * (wC H a / k) ∈ L.lattice := fun a => (hL _).2 ⟨(n : ℤ) • a, by
    simp only [wC, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    push_cast
    field_simp⟩
  have hnN : ∀ a, ((k * n : ℕ) : ℂ) * (wC H a / n) ∈ L.lattice := fun a => (hL _).2 ⟨(k : ℤ) • a, by
    simp only [wC, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    push_cast
    field_simp⟩
  have hnot : ∀ (j : ℤ) (z : ℂ) (b : ℤ), j = 1 ∨ j = 2 → z = wC H (j, b) / k → z ∉ L.lattice := by
    rintro j _ b hj rfl hz
    have := Int.le_of_dvd (by omega) (dvd_of_div_mem hL hk0 hz).1
    simp only at this
    omega
  have haff : ∀ z z', T z z' → z' ∉ L.lattice →
      τ (x z') = τ α * c / α * x z + (τ β - τ α * c / α * β) := fun z z' a b => by
    rw [hx, hx, map_add, map_mul, (hc z z' a b).2]
    field_simp
    ring
  generalize τ α * c / α = a at haff
  generalize τ β - a * β = b at haff
  have n₁ : wC H (1, 0) / k ∉ L.lattice := hnot 1 _ 0 (.inl rfl) rfl
  have n₂ : wC H (1, 1) / k ∉ L.lattice := hnot 1 _ 1 (.inl rfl) rfl
  have key : ∀ z z', T z z' → ((k * n : ℕ) : ℂ) * z' ∈ L.lattice → z - z' ∈ L.lattice ∨ z + z' ∈ L.lattice := by
    intro z z' t hz'
    by_cases hl : z' ∈ L.lattice
    · exact .inl (sub_mem (by simpa using huniq t h0 (by simpa using hl)) hl)
    have hz : ((k * n : ℕ) : ℂ) * z ∈ L.lattice := by simpa using huniq (hmul t (k * n)) h0 (by simpa using hz')
    have hl' := (hc z z' t hl).1
    refine hsep z z' hz hz' hl' hl ?_
    have i₁ := hint _ (hkN _) n₁
    have i₂ := hint _ (hkN _) n₂
    have e₁ := affine_sub_mem A (a := a) (b := b) (x₂ := x (wC H (1, 1) / k)) i₁.2 (hint z hz hl').2
      (fun e => (hsep _ _ (hkN _) (hkN _) n₁ n₂ e).elim (fun e' => ?_)
        (hnot 2 _ 1 (.inr rfl) (by simp only [wC]; push_cast; ring)))
      (haff _ _ (hkT _) n₁ ▸ hτ _ i₁.1 i₁.2) (haff _ _ (hkT _) n₂ ▸ hτ _ i₂.1 i₂.2)
    · have e₂ := hτ _ (hint z' hz' hl).1 (hint z' hz' hl).2
      rw [haff z z' t hl] at e₂
      rw [ValuationSubring.mem_nonunits_iff] at e₁ e₂ ⊢
      rw [show x z - x z' = (a * x z + b - x z') - (a * x z + b - x z) by ring]
      exact Valuation.map_sub_lt _ e₂ e₁
    · have e₂ : wC H (1, 0) / k - wC H (1, 1) / k = wC H (0, -1) / k := by simp only [wC]; push_cast; ring
      have := Int.le_of_dvd (by omega) (Int.dvd_neg.1 (dvd_of_div_mem hL hk0 (e₂ ▸ e')).2)
      omega
  have hnT : ∀ s, T (wC H s / n) (wC H s / n) := fun s => by
    obtain ⟨z, t⟩ := exists_conj_pt h (wC H s / n)
    suffices e : z - wC H s / n ∈ L.lattice from (congrArg (· ≫ io) ((hpt _ _).2 e)).symm.trans t
    refine (key _ _ t (hnN s)).elim id fun e => ?_
    refine (key _ _ (conj_add h t (hkT (1, 0))) (by rw [mul_add]; exact add_mem (hnN _) (hkN _))).elim
      (fun e' => by simpa using e') fun e' => ?_
    exact absurd (sub_mem e' e) (hnot 2 _ 0 (.inr rfl) (by simp only [wC]; push_cast; ring))
  refine ⟨C, io, h, fun s => ?_⟩
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hmn
  have huv' : (u : ℂ) * m + v * n = 1 := by exact_mod_cast huv
  have e : wC H s / (m * n : ℕ) = wC H (v • s) / m + wC H (u • s) / n := by
    simp only [wC, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    push_cast
    field_simp
    linear_combination -(s.1 * 2 + s.2 * (1 + H.rt0)) * huv'
  rw [show wC H (1, 0) = 1 by simp [wC], one_mul, e]
  exact conj_add h (hm _) (hnT _)

end GlobalTheory.CompRat.Inertia
end
end

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompRat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fixesCurve_mul_coprime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (m n p : ℕ) (A : ValuationSubring ℂ) (τ : ℂ ≃+* ℂ), p.Prime → (p : ℂ) ∈ A.nonunits → ¬ p ∣ n → Nat.Coprime m n → 3 ≤ m / p ^ m.factorization p → FixesCurve H τ m → (∀ x : ℂ, IsAlgebraic ℚ x → x ∈ A → τ x - x ∈ A.nonunits) → FixesCurve H τ (m * n) := by
  atlas_forward_decl GlobalTheory.CompRat.Inertia.fixesCurve_mul
end

section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.WeberFixed

open GlobalTheory.WeierstrassCurve GlobalTheory.UnifCoord GlobalTheory.PeriodicWeierstrass PeriodPair GlobalTheory.CompRat.Weber GlobalTheory.FieldSize

theorem exists_lattice_coord {R : Type} [CommRing R] (W : WeierstrassCurve R) (hb : W.b₂ = 0)
    {A : Over (Sp R)} [GrpObj A] {ψ₀ : A.left ⟶ scheme W} [IsIso ψ₀]
    (hψ₀ : ψ₀ ≫ toSpec W = A.hom) (he : eSec A ≫ ψ₀ = zero W) {v : epsR R ⟶ A} (htv : IsTangent v)
    {h : IsUnimodularSol (W.map (algebraMap R (DualNumber R))) ![DualNumber.eps, -1, 0]}
    (hv : v.left ≫ ψ₀ = ptHom W (algebraMap R (DualNumber R)) ![DualNumber.eps, -1, 0] h)
    (f : R →+* ℂ) (PC : Out.PolAV (Sp ℂ)) (hg1 : PC.g = 1) (u : HolUnif PC.A PC.L PC.g) {ψ : PC.A.left ⟶ A.left}
    (hψ : IsGrpPullback PC.A A (spMap f) ψ) :
    ∃ (c : ℂ) (L' : PeriodPair), c ≠ 0 ∧ (∀ z, z ∈ L'.lattice ↔ (fun _ => c * z) ∈ u.Λ) ∧
      f W.c₄ = 12 * L'.g₂ ∧ f W.c₆ = 216 * L'.g₃ ∧
      ∀ z ∉ L'.lattice, ∃ (P : Fin 3 → ℂ) (hP : IsUnimodularSol (W.map f) P),
        (u.ex fun _ => c * z).left ≫ ψ ≫ ψ₀ = ptHom W f P hP ∧ P 2 ≠ 0 ∧ ℘[L'] z * P 2 = P 0 := by
  obtain ⟨v', hv't, hv'⟩ := exists_tangent_over f hψ htv
  obtain ⟨w, hd, -⟩ := (AnyUnif.tangent_and_unimodular thetaUnifAV_all PC u).1 v' hv't
  obtain ⟨h', h1, h2, h3⟩ := fibre_over_scheme W f hψ₀ he hv hψ hv'
  obtain ⟨hw, x, y, t, hP, hx, hy, hper, heq, ht, ht0, ht1, hty, hlim⟩ :=
    exists_coord_eq R W f PC.A (ψ ≫ ψ₀) v' h' h1 h2 h3 PC.L PC.g u w hd
  obtain ⟨L', hL'⟩ := exists_periodPair_of_lattice_in_line PC.g u.Λ w hg1 hw u.discrete u.full
  have hset : (L'.lattice : Set ℂ) = {z | z • w ∈ u.Λ} := Set.ext hL'
  have key := invariants_eq_of_periodic_solution L' (W.map f) x y t 1 one_ne_zero (hset ▸ hx) (hset ▸ hy)
    (fun l hl => hper l ((hL' l).1 hl)) (fun z hz => heq z fun e => hz ((hL' z).2 e)) ht ht0 ht1 hty hlim
  have kx := x_eq_of_periodic_solution L' (W.map f) x y t 1 one_ne_zero (hset ▸ hx) (hset ▸ hy)
    (fun l hl => hper l ((hL' l).1 hl)) (fun z hz => heq z fun e => hz ((hL' z).2 e)) ht ht0 ht1 hty hlim
  simp only [one_pow, _root_.one_mul, WeierstrassCurve.map_c₄, WeierstrassCurve.map_c₆, WeierstrassCurve.map_b₂,
    hb, map_zero, zero_div, sub_zero] at key kx
  let i : Fin PC.g := ⟨0, by omega⟩
  have hi : ∀ j : Fin PC.g, j = i := fun j => Fin.ext (by have := j.2; omega)
  have hwi : w i ≠ 0 := fun h => hw (funext fun j => by rw [hi j]; exact h)
  have hc : ∀ z : ℂ, (fun _ => w i * z : Fin PC.g → ℂ) = z • w := fun z =>
    funext fun j => by rw [hi j, Pi.smul_apply, smul_eq_mul]; ring
  refine ⟨w i, L', hwi, fun z => by rw [hc, hL'], key.1, key.2.1, fun z hz => ?_⟩
  obtain ⟨P, hP, e1, e2, e3⟩ := hP z
  have h2 : P 2 ≠ 0 := fun h => hz ((hL' z).2 (e2.1 h))
  exact ⟨P, hP, by rw [hc]; exact e1, h2, by rw [← e3 h2, kx _ hz]⟩

theorem exists_iso (P Q : Out.PolAV (Sp ℂ)) (hP : P.g = 1) (hQ : Q.g = 1) (u : HolUnif P.A P.L P.g)
    (u' : HolUnif Q.A Q.L Q.g) {c c' : ℂ} (hc : c ≠ 0) (hc' : c' ≠ 0)
    (h : ∀ z, (fun _ => c * z) ∈ u.Λ ↔ (fun _ => c' * z) ∈ u'.Λ) :
    ∃ ψ : P.A.left ⟶ Q.A.left, IsGrpPullback P.A Q.A (𝟙 _) ψ := by
  generalize hg : P.g = g at u h
  generalize hg' : Q.g = g' at u' h
  obtain rfl : g = 1 := hg.symm.trans hP
  obtain rfl : g' = 1 := hg'.symm.trans hQ
  have hL := firstFiveLaws.1
  have e : ∀ (a : ℂ) (z : Fin 1 → ℂ), a ≠ 0 → z = fun _ => a * (z 0 / a) := fun a z ha =>
    funext fun j => by rw [Subsingleton.elim j 0, mul_div_cancel₀ _ ha]
  obtain ⟨α, hα, hα'⟩ := exists_isMonHom_of_map_lattice thetaUnifAV_all hL P Q 1 u u' ((c' / c) • LinearMap.id)
    hP hQ fun z hz => by
      rw [e c z hc, h] at hz
      convert hz using 1
      funext j
      rw [Subsingleton.elim j 0]
      simp
      ring
  obtain ⟨β, -, hβ'⟩ := exists_isMonHom_of_map_lattice thetaUnifAV_all hL Q P 1 u' u ((c / c') • LinearMap.id)
    hQ hP fun z hz => by
      rw [e c' z hc', ← h] at hz
      convert hz using 1
      funext j
      rw [Subsingleton.elim j 0]
      simp
      ring
  have := P.isAb.smooth
  have := Q.isAb.smooth
  have := P.isAb.proper
  have := Q.isAb.proper
  have : IsReduced P.A.left := isReduced_of_smooth_complex _ P.A.hom inferInstance
  have : IsReduced Q.A.left := isReduced_of_smooth_complex _ Q.A.hom inferInstance
  simp only [LinearMap.smul_apply, LinearMap.id_apply] at hα' hβ'
  let ψ : P.A ≅ Q.A :=
    { hom := α
      inv := β
      hom_inv_id := ComplexPoints.over_hom_ext_of_complexPoints fun x => by
        obtain ⟨z, rfl⟩ := u.ex_onto x
        rw [← Category.assoc, ← hα', ← hβ', smul_smul, show c / c' * (c' / c) = 1 by field_simp, one_smul,
          Category.comp_id]
      inv_hom_id := ComplexPoints.over_hom_ext_of_complexPoints fun x => by
        obtain ⟨z, rfl⟩ := u'.ex_onto x
        rw [← Category.assoc, ← hβ', ← hα', smul_smul, show c' / c * (c / c') = 1 by field_simp, one_smul,
          Category.comp_id] }
  have : IsMonHom ψ.hom := hα
  exact ⟨_, isGrpPullback_of_iso ψ⟩

theorem weber_homothetic {L L' : PeriodPair} {m : ℂ} (hm : m ≠ 0) (h : IsHomothetic m L L') :
    L'.g₂ ^ 3 / (L'.g₂ ^ 3 - 27 * L'.g₃ ^ 2) = L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) ∧
      ∀ z, L'.g₂ * L'.g₃ / (L'.g₂ ^ 3 - 27 * L'.g₃ ^ 2) * ℘[L'] (m * z) =
        L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * ℘[L] z := by
  have hD := g₂_cube_sub_g₃_sq_ne_zero L
  have e : L'.g₂ ^ 3 - 27 * L'.g₃ ^ 2 = (m ^ 12)⁻¹ * (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) := by
    rw [h.g₂_eq, h.g₃_eq]; field_simp
  refine ⟨?_, fun z => ?_⟩
  · rw [e, h.g₂_eq]; field_simp
  · rw [e, h.g₂_eq, h.g₃_eq, h.weierstrassP_mul]; field_simp

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem weber_fixed (H : Host E) (L : PeriodPair) (hL : ∀ x, x ∈ L.lattice ↔ ∃ s, x = wC H s) {τ : ℂ ≃+* ℂ} {n : ℕ}
    (hτ : FixesCurve H τ n) : ∀ x ∈ weberSet L n, τ x = x := by
  obtain ⟨C, io, hio, hact⟩ := hτ
  let W : WeierstrassCurve ℂ := ⟨0, 0, 0, -L.g₂ / 4, -L.g₃ / 4⟩
  have hb : W.b₂ = 0 := by simp [W, WeierstrassCurve.b₂]
  have h4 : W.c₄ = 12 * L.g₂ := by
    simp only [W, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]; ring
  have h6 : W.c₆ = 216 * L.g₃ := by
    simp only [W, WeierstrassCurve.c₆, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]; ring
  have hΔ : IsUnit W.Δ := by
    refine isUnit_iff_ne_zero.2 fun h => g₂_cube_sub_g₃_sq_ne_zero L ?_
    have e := W.c_relation
    rw [h, h4, h6] at e
    linear_combination -e / 1728
  obtain ⟨P₀, ψ₀, v, hg, hiso, hψ₀, he, ⟨h, hv⟩, hlie⟩ := exists_polAV ℂ W hΔ
  have hid : spMap (RingHom.id ℂ) = 𝟙 _ := Spec.map_id (CommRingCat.of ℂ)
  have : IsMonHom (Iso.refl P₀.A).hom := inferInstanceAs (IsMonHom (𝟙 _))
  obtain ⟨u₀, -⟩ := exists_isThetaUnif thetaUnifAV_all P₀
  obtain ⟨c₀, L₀, hc₀, hL₀, a4, a6, -⟩ := exists_lattice_coord W hb hψ₀ he (hlie.1 0) hv (RingHom.id ℂ) P₀ hg u₀
    ((isGrpPullback_of_iso (Iso.refl P₀.A)).congr hid.symm rfl)
  have e₀ : L₀.lattice = L.lattice := lattice_eq_of_g₂_eq_of_g₃_eq
    (by rw [RingHom.id_apply, h4] at a4; linear_combination -a4 / 12)
    (by rw [RingHom.id_apply, h6] at a6; linear_combination -a6 / 216)
  have i : Fin C.P.g := ⟨0, by rw [C.g_eq]; omega⟩
  have hC : ∀ z, (fun _ => C.c * z) ∈ C.u.Λ ↔ z ∈ L.lattice := fun z => by
    rw [CurveEndo.mem_lattice, hL]
    exact exists_congr fun a => ⟨fun h => mul_left_cancel₀ C.c_ne (congrFun h i), fun h => by rw [h]⟩
  obtain ⟨ψ, hψ⟩ := exists_iso C.P P₀ C.g_eq hg C.u u₀ C.c_ne hc₀ fun z => by rw [hC, ← hL₀, e₀]
  obtain ⟨c₁, L₁, hc₁, hL₁, b4, b6, hb₁⟩ := exists_lattice_coord W hb hψ₀ he (hlie.1 0) hv (RingHom.id ℂ) C.P C.g_eq
    C.u (hψ.congr hid.symm rfl)
  obtain ⟨c₂, L₂, hc₂, hL₂, d4, d6, hb₂⟩ := exists_lattice_coord W hb hψ₀ he (hlie.1 0) hv (τ : ℂ →+* ℂ) C.P C.g_eq
    C.u ((hio.comp hψ).congr (Category.comp_id _) rfl)
  have hc := C.c_ne
  have H₁ : IsHomothetic (C.c / c₁) L L₁ := fun x => by
    rw [hL₁, ← hC, ← _root_.mul_assoc, mul_div_cancel₀ _ hc₁]
  have H₂ : IsHomothetic (C.c / c₂) L L₂ := fun x => by
    rw [hL₂, ← hC, ← _root_.mul_assoc, mul_div_cancel₀ _ hc₂]
  obtain ⟨j₁, w₁⟩ := weber_homothetic (div_ne_zero hc hc₁) H₁
  obtain ⟨j₂, w₂⟩ := weber_homothetic (div_ne_zero hc hc₂) H₂
  rw [RingHom.id_apply] at b4 b6
  have t2 : τ L₁.g₂ = L₂.g₂ := by
    rw [b4, map_mul, map_ofNat] at d4
    exact mul_left_cancel₀ (by norm_num) d4
  have t3 : τ L₁.g₃ = L₂.g₃ := by
    rw [b6, map_mul, map_ofNat] at d6
    exact mul_left_cancel₀ (by norm_num) d6
  rintro _ (rfl | ⟨z, hz, hz', rfl⟩)
  · conv_lhs => rw [← j₁]
    rw [← j₂]
    simp [map_div₀, t2, t3, map_ofNat]
  obtain ⟨s, rfl⟩ := (hL z).1 hz
  obtain ⟨Q, hQ1, b1, hQ0, b3⟩ := hb₁ _ fun h => hz' ((H₁ _).1 h)
  obtain ⟨P, hP1, a1, hP0, a3⟩ := hb₂ _ fun h => hz' ((H₂ _).1 h)
  have e := hact s
  rw [show wC H (1, 0) = 1 by simp [wC], _root_.one_mul] at e
  simp only [← _root_.mul_assoc, mul_div_cancel₀ _ hc₁] at b1
  simp only [← _root_.mul_assoc, mul_div_cancel₀ _ hc₂] at a1
  have e2 : ptHom W (τ : ℂ →+* ℂ) P hP1 = spMap (τ : ℂ →+* ℂ) ≫ ptHom W (RingHom.id ℂ) Q hQ1 := by
    rw [← a1, ← b1]
    have e3 := congrArg (· ≫ ψ ≫ ψ₀) e
    simp only [Category.assoc] at e3 ⊢
    exact e3
  have hQ2 := hQ1.map_comp (τ : ℂ →+* ℂ)
  rw [RingHom.comp_id] at hQ2
  rw [SpecMap_ptHom, ptHom_congr W _ _ _ (RingHom.comp_id _) rfl hQ2, ptHom_eq_ptHom_iff] at e2
  obtain ⟨k, hk⟩ := e2
  have v0 : τ (Q 0) = k * P 0 := congrFun hk 0
  have v2 : τ (Q 2) = k * P 2 := congrFun hk 2
  have hQ0' : τ (Q 2) ≠ 0 := by simpa using hQ0
  have tp : τ (℘[L₁] (C.c / c₁ * (wC H s / n))) = ℘[L₂] (C.c / c₂ * (wC H s / n)) := by
    refine mul_right_cancel₀ hQ0' ?_
    rw [← map_mul, b3, v0, v2, ← a3]
    ring
  conv_lhs => rw [← w₁]
  rw [← w₂, map_mul, tp]
  simp [map_div₀, t2, t3, map_ofNat]

theorem zeta_fixed (H : Host E) {τ : ℂ ≃+* ℂ} {n : ℕ} (hn : 2 ≤ n) (hτ : FixesCurve H τ n) : τ (zeta n) = zeta n := by
  obtain ⟨C, io, h⟩ := hτ
  simpa using MultiplierNorm.map_zeta_eq_zpow_norm E H C τ (CurveConjCompare.fixes_root_of_acts_torsion hn h) io n (1, 0)
    (by omega) h

end GlobalTheory.WeberFixed
end
end

section
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.DeepCoeff

open GlobalTheory.WeierstrassCurve GlobalTheory.UnifCoord GlobalTheory.PeriodicWeierstrass PeriodPair GlobalTheory.CompRat.Weber GlobalTheory.FieldSize GlobalTheory.WeberFixed

def preimageField (τ : ℂ ≃+* ℂ) (K : IntermediateField ℚ ℂ) : IntermediateField ℚ ℂ :=
  K.comap ((τ : ℂ →+* ℂ).toRatAlgHom)

theorem exists_coeff_unramified : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l l₂ : Level H) (c : Coeff l) (n p : ℕ), p.Prime → ¬ p ∣ n → Nat.Coprime l.M n → l₂.M = l.M * n → l₂.A = 1 → l.GoodAt p → CurveOver H c.F l.M → ∃ c' : Coeff l₂, c.F ≤ c'.F ∧ CurveOver H c'.F l₂.M ∧ ∀ τ : ℂ ≃+* ℂ, (∀ x ∈ c.F, τ x = x) → (∀ x ∈ c'.F, τ x ∈ c'.F) ∧ ∀ A : ValuationSubring ℂ, (p : ℂ) ∈ A.nonunits → (∀ x : ℂ, IsAlgebraic ℚ x → x ∈ A → τ x - x ∈ A.nonunits) → ∀ x ∈ c'.F, τ x = x := by
  intro E _ _ _ H l l₂ c n p hp hpn hco hM hA hgood hcurve
  obtain ⟨L, hL⟩ := GlobalTheory.FinalJoin.CurveField.exists_periodPair H
  have h3 := l₂.three_le
  have hN : 0 < l₂.M := by omega
  have hN0 : (l₂.M : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  obtain ⟨hfin, halg, hperm⟩ := weberSet_finite_algebraic_permuted L l₂.M hN (g₂_ne_zero H L hL) (g₃_ne_zero H L hL)
  have hζ : IsPrimitiveRoot (zeta l₂.M) l₂.M := Complex.isPrimitiveRoot_exp _ hN.ne'
  let S : Set ℂ := insert (zeta l₂.M) (weberSet L l₂.M)
  have := (hfin.insert (zeta l₂.M)).to_subtype
  have hS : FiniteDimensional ℚ (IntermediateField.adjoin ℚ S) := by
    refine IntermediateField.finiteDimensional_adjoin ?_
    rintro x (rfl | hx)
    · exact (hζ.isIntegral hN).tower_top
    · exact (halg (GlobalTheory.WeberField.invariant_isAlgebraic H L hL) x hx).isIntegral
  have := c.fin
  let F := c.F ⊔ IntermediateField.adjoin ℚ S
  have hl : c.F ≤ F := le_sup_left
  have hr : ∀ x ∈ S, x ∈ F := fun x hx => le_sup_right (a := c.F) (IntermediateField.subset_adjoin ℚ S hx)
  have hrt : H.rt0 ∈ c.F := c.le (IntermediateField.subset_adjoin _ _ (by simp))
  have hle : ∀ K : IntermediateField ℚ ℂ, c.F ≤ K → S ⊆ K → F ≤ K := fun K h₁ h₂ =>
    sup_le h₁ (IntermediateField.adjoin_le_iff.2 h₂)
  refine ⟨⟨F, inferInstance, fun τ a => hl (c.conj τ a), ?_, ?_⟩, hl, fun τ hτ => ?_, fun τ hτ => ⟨?_, ?_⟩⟩
  · rw [Level.M', hA, Nat.lcm_one_right]
    exact hr _ (.inl rfl)
  · refine IntermediateField.adjoin_le_iff.2 ?_
    rintro x (rfl | rfl)
    · exact hl hrt
    · rw [hA, show zeta 1 = 1 by simp [zeta]]
      exact one_mem F
  · exact fixesCurve_of_weber E H L _ hN hL τ (hτ _ (hl hrt)) (hτ _ (hr _ (.inr (.inl rfl))))
      fun s hs => hτ _ (hr _ (.inr (.inr ⟨_, (hL _).2 ⟨s, rfl⟩, hs, rfl⟩)))
  · have hj := weber_fixed H L hL (hcurve τ hτ) _ (.inl rfl)
    refine hle (preimageField τ F) (fun x hx => ?_) ?_
    · show τ x ∈ F
      rw [hτ x hx]
      exact hl hx
    rintro x (rfl | rfl | ⟨z, hz, hz', rfl⟩)
    · show τ (zeta l₂.M) ∈ F
      have : NeZero l₂.M := ⟨hN.ne'⟩
      obtain ⟨k, -, hk⟩ := hζ.eq_pow_of_pow_eq_one (ξ := τ (zeta l₂.M)) (by rw [← map_pow, hζ.pow_eq_one, map_one])
      rw [← hk]
      exact pow_mem (hr _ (.inl rfl)) _
    · show τ _ ∈ F
      rw [hj]
      exact hr _ (.inr (.inl rfl))
    · show τ _ ∈ F
      obtain ⟨t, h₁, h₂, h₃⟩ := hperm τ hj (z / l₂.M) (by rwa [mul_div_cancel₀ _ hN0]) hz'
      rw [h₃]
      have e : l₂.M * t / l₂.M = t := mul_div_cancel_left₀ _ hN0
      exact hr _ (.inr (.inr ⟨_, h₁, by rwa [e], by rw [e]⟩))
  · intro A hpA hin
    have hfix : FixesCurve H τ l₂.M := hM ▸ GlobalTheory.T.fixesCurve_mul_coprime E H l.M n p A τ hp hpA hpn hco hgood (hcurve τ hτ) hin
    let K : IntermediateField ℚ ℂ :=
      ((τ : ℂ →+* ℂ).eqLocusField (RingHom.id ℂ)).toIntermediateField fun q => by
        show τ (algebraMap ℚ ℂ q) = algebraMap ℚ ℂ q
        simp
    refine hle K hτ ?_
    rintro x (rfl | hx)
    · exact zeta_fixed H (by omega) hfix
    · exact weber_fixed H L hL hfix x hx

end GlobalTheory.DeepCoeff
end
end

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompRat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coeff_field_curve : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l l₂ : Level H) (c : Coeff l) (n p : ℕ), p.Prime → ¬ p ∣ n → Nat.Coprime l.M n → l₂.M = l.M * n → l₂.A = 1 → l.GoodAt p → CurveOver H c.F l.M → ∃ c' : Coeff l₂, c.F ≤ c'.F ∧ CurveOver H c'.F l₂.M ∧ ∀ τ : ℂ ≃+* ℂ, (∀ x ∈ c.F, τ x = x) → (∀ x ∈ c'.F, τ x ∈ c'.F) ∧ ∀ A : ValuationSubring ℂ, (p : ℂ) ∈ A.nonunits → (∀ x : ℂ, IsAlgebraic ℚ x → x ∈ A → τ x - x ∈ A.nonunits) → ∀ x ∈ c'.F, τ x = x := by
  atlas_forward_decl GlobalTheory.DeepCoeff.exists_coeff_unramified
end

section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.Member
open scoped TensorProduct Matrix
open GlobalTheory.CompRat

namespace GlobalTheory.DetFibre

theorem exists_complete_of_idem {R ι A : Type} [CommRing R] [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A]
    (a₀ : A) (χ : ι → R) (hχ : ∀ i, χ i * χ i = χ i) (t : ι → A) :
    ∃ cs : A → R, (∀ a, cs a * cs a = cs a) ∧ (∀ a b, a ≠ b → cs a * cs b = 0) ∧ ∑ a, cs a = 1 ∧
      (∀ S : Subring R, (∀ i, χ i ∈ S) → ∀ a, cs a ∈ S) ∧
      ∀ (T : Type) [CommRing T] (φ : R →+* T) (i : ι), (∀ j, φ (χ j) = if i = j then 1 else 0) →
        ∀ a, φ (cs a) = if t i = a then 1 else 0 := by
  let e : A → R := fun a => ∏ i, if t i = a then 1 else 1 - χ i
  let z : R := ∏ i, (1 - χ i)
  have h1 : ∀ i, (1 - χ i) * (1 - χ i) = 1 - χ i := fun i => by linear_combination hχ i
  have ee : ∀ a, e a * e a = e a := fun a => by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    split_ifs
    · exact one_mul _
    · exact h1 i
  have ez : ∀ a, e a * z = z := fun a => by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    split_ifs
    · exact one_mul _
    · exact h1 i
  have zz : z * z = z := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => h1 i
  have eb : ∀ a b, a ≠ b → e a * e b = z := fun a b hab => by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    split_ifs with ha hb
    · exact absurd (ha.symm.trans hb) hab
    · exact one_mul _
    · exact mul_one _
    · exact h1 i
  let f : A → R := fun a => e a - z
  have ff : ∀ a, f a * f a = f a := fun a => by
    simp only [f]; linear_combination ee a - 2 * ez a + zz
  have fb : ∀ a b, a ≠ b → f a * f b = 0 := fun a b hab => by
    simp only [f]; linear_combination eb a b hab - ez a - ez b + zz
  let s : R := ∑ a, f a
  have fs : ∀ a, f a * s = f a := fun a => by
    rw [Finset.mul_sum, Finset.sum_eq_single a (fun b _ hb => fb a b hb.symm) (by simp), ff]
  have ss : s * s = s := by
    conv_lhs => rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => fs a
  refine ⟨fun a => f a + if a = a₀ then 1 - s else 0, fun a => ?_, fun a b hab => ?_, ?_, fun S hS a => ?_,
    fun T _ φ i hφ a => ?_⟩
  · beta_reduce
    split_ifs
    · linear_combination ff a - 2 * fs a + ss
    · simp [ff]
  · beta_reduce
    split_ifs with ha hb
    · exact absurd (ha.trans hb.symm) hab
    · linear_combination fb a b hab - fs b
    · linear_combination fb a b hab - fs a
    · simp [fb a b hab]
  · rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
    simp [s]
  · have hf : ∀ a, f a ∈ S := fun a => by
      refine sub_mem (prod_mem fun i _ => ?_) (prod_mem fun i _ => sub_mem (one_mem _) (hS i))
      split_ifs
      · exact one_mem _
      · exact sub_mem (one_mem _) (hS i)
    refine add_mem (hf a) ?_
    split_ifs
    · exact sub_mem (one_mem _) (sum_mem fun a _ => hf a)
    · exact zero_mem _
  · have hz : φ z = 0 := by
      rw [map_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hφ])
    have hf : ∀ a, φ (f a) = if t i = a then 1 else 0 := fun a => by
      rw [map_sub, hz, sub_zero, map_prod]
      split_ifs with h
      · refine Finset.prod_eq_one fun j _ => ?_
        split_ifs with h'
        · exact map_one _
        · have : i ≠ j := fun hij => h' (hij ▸ h)
          simp [hφ, this]
      · exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hφ, h])
    have hs : φ s = 1 := by
      rw [map_sum, Finset.sum_congr rfl fun a _ => hf a, Finset.sum_ite_eq]
      simp
    rw [map_add, hf]
    split_ifs <;> simp [hs]

section Periods

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_idem_of_map (σ : c.F →+* ℂ) {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (hcl : FnAlgClosed Xo c)
    {A : Type} [Fintype A] [DecidableEq A] (a₀ : A) (t : Fin F.n → A) :
    ∃ cs : A → Rul Xo c, (∀ a, cs a ∈ sec Xo c 0 0) ∧ (∀ a, cs a * cs a = cs a) ∧
      (∀ a b, a ≠ b → cs a * cs b = 0) ∧ ∑ a, cs a = 1 ∧
      ∀ (y : FrPt Xo c (CAt σ)) (i : Fin F.n) P, IsPeriod (F.Di i) ty P → y.x = F.u i P →
        ∀ a, Formalism.L2.PjFree.toC (evR Xo c (cs a) y) = if t i = a then 1 else 0 := by
  have hA := GlobalTheory.Frames.allTest_of_secBaseChange GlobalTheory.allSixLaws.1.secBaseChange E H Dw l Xo c
  choose χ h1 h2 h3 using GlobalTheory.CompFun.exists_idempotent hA σ F hcl
  obtain ⟨cs, k1, k2, k3, k4, k5⟩ := exists_complete_of_idem a₀ χ h2 t
  let S : Subring (Rul Xo c) :=
    { (sec Xo c 0 0).toAddSubgroup with
      one_mem' := GlobalTheory.CompFun.one_mem_sec
      mul_mem' := fun ha hb => by simpa using sec_mul Xo c 0 0 0 0 ha hb }
  refine ⟨cs, k4 S h1, k1, k2, k3, fun y i P hP hy a => ?_⟩
  have : IsReduced (CAt σ) := inferInstanceAs (IsReduced ℂ)
  have hy' := hA (CAt σ) y
  let ev : Rul Xo c →+* CAt σ :=
    { toFun := fun f => evR Xo c f y
      map_one' := evalAt_one _ _ y hy'
      map_mul' := fun f f' => evalAt_mul _ _ f f' y
      map_zero' := evalAt_zero _ _ y
      map_add' := fun f f' => evalAt_add _ _ f f' y }
  exact k5 (CAt σ) ev i (fun j => h3 j y i P hP hy) a

end Periods

section Marks

open GlobalTheory.CharRead

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H}

theorem det_cong_of_finCong (V : HSp D) (N : ℕ) (hN : N ≠ 0) (u : GA D V) (hu : FinCong V N u) :
    ∃ w ∈ GlobalTheory.AdLat.hat1 D.host.F (Set.range (algebraMap (𝓞 D.host.E) D.host.E)),
        ((Matrix.GeneralLinearGroup.det (finHom V u) : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) :
          (Af D.host.F ⊗[D.host.F] D.host.E)) - 1 = (N : ℕ) • w := by
  obtain ⟨k1, -, k3, k4, -⟩ := GlobalTheory.T.completedLattice_eq_adelicCompletion_and_gram D V
  exact det_cong_one D.host.F (latC V) k3 k4 N hN (finHom V u).1 (by rw [← k1]; exact hu)

set_option maxHeartbeats 800000 in

theorem exists_rat_of_marks (l : Level H) (V : HSp D) (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))
    (hio : LatEmb V io) {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La] (t : Dw.La → La)
    (g g' : GA D V) (Λ Λ' : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (hΛ : Λ = latG V g) (hΛ' : Λ' = latG V g')
    (φ : La ≃ₗ[𝓞 D.host.E] Λ) (φ' : La ≃ₗ[𝓞 D.host.E] Λ') (ξ : D.host.E) (hξ : ξ ≠ 0)
    (htr : ∀ a b, Algebra.trace ℚ D.host.E (ξ * herm (-V.gramᵀ) (φ a : Fin V.rank → D.host.E) (φ b)) =
      Algebra.trace ℚ D.host.E (ξ * herm (-V.gramᵀ) (φ' a : Fin V.rank → D.host.E) (φ' b)))
    (hM : ∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
      ∃ w ∈ latGHat V g, finVec V (φ (t a) : Fin V.rank → D.host.E) - (finHom V g).1.mulVec (finVec V (io a)) =
        (l.M : ℕ) • w)
    (hM' : ∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
      ∃ w ∈ latGHat V g', finVec V (φ' (t a) : Fin V.rank → D.host.E) - (finHom V g').1.mulVec (finVec V (io a)) =
        (l.M : ℕ) • w) :
    ∃ γ ∈ GQ V, ∃ u : GA D V, gLat V u = latHat V ∧ FinCong V l.M u ∧ g' = γ * g * u := by
  subst hΛ hΛ'
  obtain ⟨r1, -, r3, -, r5⟩ := GlobalTheory.T.rational_points_adelicUnitary_eq_unitary D V
  obtain ⟨δ, hδ1, hδ2, hδ3⟩ := exists_unitary_of_trace_eq _ _ (GlobalTheory.T.adelicElementLattice_full_and_completion D V g).2.1 (GlobalTheory.T.adelicElementLattice_full_and_completion D V g').2.1
    φ φ' _ ξ hξ htr
  obtain ⟨γ, hγ⟩ := r3 δ hδ3
  obtain ⟨m1, m2⟩ := (GlobalTheory.T.adelicUnitaryLattice_rationalTranslate_invariance D V).1 γ δ g hγ
  have hlat : latG V (γ * g) = latG V g' := by
    ext v
    have hv : (δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ
        (((δ⁻¹ : GL (Fin V.rank) D.host.E) : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ v) = v := by
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    have a1 := m1 (((δ⁻¹ : GL (Fin V.rank) D.host.E) : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ v)
    have a2 := hδ2 (((δ⁻¹ : GL (Fin V.rank) D.host.E) : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ v)
    rw [hv] at a1 a2
    exact a1.symm.trans a2
  have hc : FinCong V l.M ((γ * g)⁻¹ * g') := by
    refine finCong_of_marks l V io hio _ _ hlat (fun a => finVec V (φ' (t a) : Fin V.rank → D.host.E)) ?_ hM'
    intro a ha
    obtain ⟨w, hw, e⟩ := hM a ha
    refine ⟨_, (m2 w).1 hw, ?_⟩
    have e2 := congrArg (fun z => (finHom V γ).1 *ᵥ z) e
    simp only [Matrix.mulVec_sub, Matrix.mulVec_smul] at e2
    rw [(r5 _ δ hγ).1, Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, hδ1] at e2
    exact e2
  have hu : gLat V ((γ * g)⁻¹ * g') = latHat V := by
    refine gLat_eq_of_finCong V _ ((GlobalTheory.T.adelicUnitaryLattice_rationalTranslate_invariance D V).2.2.2 _ _ hlat) ?_
    have e0 : ((γ * g)⁻¹ * g')⁻¹ = g'⁻¹ * (γ * g) := by group
    rw [e0]
    exact (GlobalTheory.T.adelicUnitaryLattice_rationalTranslate_invariance D V).2.2.2 _ _ hlat.symm
  exact ⟨γ, (r1 γ).2 ⟨δ, hγ⟩, _, hu, hc, (mul_inv_cancel_left _ _).symm⟩

theorem exists_rat_of_index {l : Level H} {Xo : Moduli Dw l} {s : KA l →+* ℂ} {n : ℕ} {ty : Fin n → D.host.E →+* ℂ}
    (F : FamilyUnif Xo s ty) (V : HSp D) (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))
    (hio : LatEmb V io) (i i' : Fin F.n) (hi : i = i')
    (g g' : GA D V) (Λ Λ' : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (hΛ : Λ = latG V g) (hΛ' : Λ' = latG V g')
    (φ : (F.Di i).La ≃ₗ[𝓞 D.host.E] Λ) (φ' : (F.Di i').La ≃ₗ[𝓞 D.host.E] Λ') (ξ : D.host.E) (hξ : ξ ≠ 0)
    (htr : ∀ a b, (((F.Di i).EF a b : ℤ) : ℚ) =
      Algebra.trace ℚ D.host.E (ξ * herm (-V.gramᵀ) (φ a : Fin V.rank → D.host.E) (φ b)))
    (htr' : ∀ a b, (((F.Di i').EF a b : ℤ) : ℚ) =
      Algebra.trace ℚ D.host.E (ξ * herm (-V.gramᵀ) (φ' a : Fin V.rank → D.host.E) (φ' b)))
    (hM : ∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
      ∃ w ∈ latGHat V g, finVec V (φ (F.t i a) : Fin V.rank → D.host.E) -
        (finHom V g).1.mulVec (finVec V (io a)) = (l.M : ℕ) • w)
    (hM' : ∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
      ∃ w ∈ latGHat V g', finVec V (φ' (F.t i' a) : Fin V.rank → D.host.E) -
        (finHom V g').1.mulVec (finVec V (io a)) = (l.M : ℕ) • w) :
    ∃ γ ∈ GQ V, ∃ u : GA D V, gLat V u = latHat V ∧ FinCong V l.M u ∧ g' = γ * g * u := by
  subst hi
  exact exists_rat_of_marks l V io hio (F.t i) g g' Λ Λ' hΛ hΛ' φ φ' ξ hξ
    (fun a b => (htr a b).symm.trans (htr' a b)) hM hM'

set_option maxHeartbeats 1000000 in

theorem exists_map_of_invariant {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (V : HSp D)
    (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))
    (σ : c.F →+* ℂ) (r : ℕ) (hr : V.rank = r) (U : Unf Xo c σ r)
    (dict : GA D V → Σ k, Frame (U.X k).Ψ r) (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ)
    (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (hio : LatEmb V io) (hW : ∀ k, ModelW V hr (U.X k)) (hD : DictLat U V hr dict io e F ik φ th x₀)
    {A : Type} (ν : GA D V → A) (h1 : ∀ u : GA D V, gLat V u = latHat V → FinCong V l.M u → ∀ h, ν (h * u) = ν h)
    (h2 : ∀ γ ∈ GQ V, ∀ h, ν (γ * h) = ν h) :
    ∃ t : Fin F.n → A, (∀ i, ∃ h, t i = ν h) ∧
      ∀ h γ : GA D V, MarkBy U V hr dict io F ik φ h γ → t (ik (dict h).1) = ν (γ * h) := by
  subst hr
  have hG : ∀ k, (U.X k).Gm = -V.gramᵀ := fun k => (hW k).1
  have htr : ∀ k a b, (((F.Di (ik k)).EF a b : ℤ) : ℚ) = Algebra.trace ℚ D.host.E
      (-(-D.host.xi0) * herm (-V.gramᵀ) (φ k a : Fin V.rank → D.host.E) (φ k b)) := fun k a b => by
    rw [hD.1.1 k a b, hG k, (hW k).2]
  have key : ∀ h γ h' γ', MarkBy U V rfl dict io F ik φ h γ → MarkBy U V rfl dict io F ik φ h' γ' →
      ik (dict h).1 = ik (dict h').1 → ν (γ * h) = ν (γ' * h') := by
    intro h γ h' γ' hm hm' hi
    have hξ : -(-D.host.xi0) ≠ 0 := by
      rw [← (hW (dict h).1).2]
      exact neg_ne_zero.2 (U.X _).ξ0_ne
    obtain ⟨δ, hδ, u, hu1, hu2, hu3⟩ := exists_rat_of_index F V io hio _ _ hi _ _ _ _
      (SetLike.ext' (hm.2.1.trans (Set.image_id _)))
      (SetLike.ext' (hm'.2.1.trans (Set.image_id _))) (φ _) (φ _) _ hξ (htr _) (htr _) hm.2.2 hm'.2.2
    rw [hu3, h1 u hu1 hu2, h2 δ hδ]
  have hv : ∀ i : Fin F.n, ∃ a : A, (∃ h, a = ν h) ∧
      ∀ h γ, MarkBy U V rfl dict io F ik φ h γ → ik (dict h).1 = i → a = ν (γ * h) := by
    intro i
    by_cases hex : ∃ h γ, MarkBy U V rfl dict io F ik φ h γ ∧ ik (dict h).1 = i
    · obtain ⟨h, γ, hm, hi⟩ := hex
      exact ⟨_, ⟨_, rfl⟩, fun h' γ' hm' hi' => key h γ h' γ' hm hm' (hi.trans hi'.symm)⟩
    · exact ⟨_, ⟨1, rfl⟩, fun h γ hm hi => absurd ⟨h, γ, hm, hi⟩ hex⟩
  choose t ht1 ht2 using hv
  exact ⟨t, ht1, fun h γ hm => ht2 _ h γ hm rfl⟩

set_option maxHeartbeats 1000000 in

theorem exists_idem_of_invariant {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (V : HSp D)
    (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))
    (σ : c.F →+* ℂ) (r : ℕ) (hr : V.rank = r) (U : Unf Xo c σ r)
    (dict : GA D V → Σ k, Frame (U.X k).Ψ r) (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ)
    (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (hio : LatEmb V io) (hW : ∀ k, ModelW V hr (U.X k)) (hD : DictLat U V hr dict io e F ik φ th x₀)
    (hdom : ∀ h, (dict h).2 ∈ (U.X (dict h).1).dom) (hcl : FnAlgClosed Xo c)
    {A : Type} [Fintype A] [DecidableEq A] (ν : GA D V → A)
    (h1 : ∀ u : GA D V, gLat V u = latHat V → FinCong V l.M u → ∀ h, ν (h * u) = ν h)
    (h2 : ∀ γ ∈ GQ V, ∀ h, ν (γ * h) = ν h) :
    ∃ cs : A → Rul Xo c, (∀ a, cs a ∈ sec Xo c 0 0) ∧ (∀ a, cs a * cs a = cs a) ∧
      (∀ a b, a ≠ b → cs a * cs b = 0) ∧ ∑ a, cs a = 1 ∧
      ∀ h γ : GA D V, MarkBy U V hr dict io F ik φ h γ → ∀ a,
        rdU U (cs a) (dict h).1 (dict h).2 = (if ν (γ * h) = a then 1 else 0) ∧
        ∀ (y : FrPt Xo c (CAt σ)) P, IsPeriod (F.Di (ik (dict h).1)) (fun j => relab c σ (e j).1) P →
          y.x = F.u (ik (dict h).1) P → toC (evR Xo c (cs a) y) = if ν (γ * h) = a then 1 else 0 := by
  obtain ⟨t, -, ht⟩ := exists_map_of_invariant V io σ r hr U dict g e F ik φ th x₀ hio hW hD ν h1 h2
  obtain ⟨cs, k0, k1, k2, k3, k4⟩ := exists_idem_of_map σ F hcl (ν 1) t
  refine ⟨cs, k0, k1, k2, k3, fun h γ hm a => ⟨?_, fun y P hP hy => ?_⟩⟩
  · obtain ⟨Pm, -, hP, hx, -⟩ := hD.1.2 (dict h).1 ⟨(dict h).2, hdom h⟩
    rw [← ht h γ hm, ← k4 _ _ Pm hP hx a]
    exact dif_pos (hdom h)
  · rw [← ht h γ hm, ← k4 y _ P hP hy a]
    rfl

set_option maxHeartbeats 1000000 in

theorem exists_idem_rdU_det {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (V : HSp D)
    (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))
    (σ : c.F →+* ℂ) (r : ℕ) (hr : V.rank = r) (U : Unf Xo c σ r)
    (dict : GA D V → Σ k, Frame (U.X k).Ψ r) (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ)
    (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (hio : LatEmb V io) (hW : ∀ k, ModelW V hr (U.X k)) (hD : DictLat U V hr dict io e F ik φ th x₀)
    (hdom : ∀ h, (dict h).2 ∈ (U.X (dict h).1).dom) (hcl : FnAlgClosed Xo c)
    {A : Type} [Fintype A] [DecidableEq A] (ν : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ → A)
    (h1 : ∀ u : GA D V, gLat V u = latHat V →
      (∃ w ∈ GlobalTheory.AdLat.hat1 D.host.F (Set.range (algebraMap (𝓞 D.host.E) D.host.E)),
        ((Matrix.GeneralLinearGroup.det (finHom V u) : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) :
          (Af D.host.F ⊗[D.host.F] D.host.E)) - 1 = (l.M : ℕ) • w) →
      ∀ h, ν (Matrix.GeneralLinearGroup.det (finHom V (h * u))) = ν (Matrix.GeneralLinearGroup.det (finHom V h)))
    (h2 : ∀ γ ∈ GQ V, ∀ h,
      ν (Matrix.GeneralLinearGroup.det (finHom V (γ * h))) = ν (Matrix.GeneralLinearGroup.det (finHom V h))) :
    ∃ cs : A → Rul Xo c, (∀ a, cs a ∈ sec Xo c 0 0) ∧ (∀ a, cs a * cs a = cs a) ∧
      (∀ a b, a ≠ b → cs a * cs b = 0) ∧ ∑ a, cs a = 1 ∧
      ∀ h γ : GA D V, MarkBy U V hr dict io F ik φ h γ → ∀ a,
        rdU U (cs a) (dict h).1 (dict h).2 =
          if ν (Matrix.GeneralLinearGroup.det (finHom V (γ * h))) = a then 1 else 0 := by
  obtain ⟨cs, k0, k1, k2, k3, k4⟩ := exists_idem_of_invariant V io σ r hr U dict g e F ik φ th x₀ hio hW hD hdom hcl
    (fun h => ν (Matrix.GeneralLinearGroup.det (finHom V h)))
    (fun u hu hc => h1 u hu (det_cong_of_finCong V l.M (by have := l.three_le; omega) u hc)) h2
  exact ⟨cs, k0, k1, k2, k3, fun h γ hm a => (k4 h γ hm a).1⟩



theorem fnAlgClosed_of_iotaOK {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) (V : HSp D)
    (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (hio : IotaOK Dw V io) (hpos : 1 ≤ Dw.p + Dw.q)
    (hrk : Dw.p = 0 ∨ Dw.q = 0 ∨ 3 ≤ Dw.p + Dw.q) (hA : l.A = 1) (hc : CurveOver H c.F l.M) : FnAlgClosed Xo c :=
  GlobalTheory.CompRat.fnAlgClosed_of_curveOver _ H Dw l Xo c hpos hA
    (hrk.imp_right (Or.imp_right fun h => ⟨h, GlobalTheory.RankOneDatum.exists_datum_rank_one D H Dw V io hio hpos⟩)) hc

end Marks

set_option maxHeartbeats 1000000 in

theorem exists_unramified_field_fibres (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (l l₂ : Level H) (c : Coeff l)
    (n p : ℕ) (hp : p.Prime) (hpn : ¬ p ∣ n) (hMn : Nat.Coprime l.M n) (hM : l₂.M = l.M * n) (hA : l₂.A = 1)
    (hgood : l.GoodAt p) (hcurve : CurveOver H c.F l.M) :
    ∃ (c₁ : Coeff l) (c₂ : Coeff l₂), c₂.F = c₁.F ∧ c.F ≤ c₂.F ∧ CurveOver H c₂.F l₂.M ∧
    (∀ τ : ℂ ≃+* ℂ, (∀ x ∈ c.F, τ x = x) → (∀ x ∈ c₂.F, τ x ∈ c₂.F) ∧
      ∀ O : ValuationSubring ℂ, (p : ℂ) ∈ O.nonunits → (∀ x : ℂ, IsAlgebraic ℚ x → x ∈ O → τ x - x ∈ O.nonunits) →
        ∀ x ∈ c₂.F, τ x = x) ∧
    ∀ (Dw : Datum H) (Xo₂ : Moduli Dw l₂) (V : HSp D) (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)),
    IotaOK Dw V io → 1 ≤ Dw.p + Dw.q → (Dw.p = 0 ∨ Dw.q = 0 ∨ 3 ≤ Dw.p + Dw.q) →
    FnAlgClosed Xo₂ c₂ ∧ ∀ (σ : c₂.F →+* ℂ) (r : ℕ) (hr : V.rank = r) (U : Unf Xo₂ c₂ σ r)
    (dict : GA D V → Σ k, Frame (U.X k).Ψ r) (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo₂ (σ.comp (IntermediateField.inclusion c₂.le).toRingHom) (fun j => relab c₂ σ (e j).1))
    (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ)
    (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ),
    GoodEmb c₂ σ → (∀ k, ModelW V hr (U.X k)) → DictLat U V hr dict io e F ik φ th x₀ →
    (∀ h, (dict h).2 ∈ (U.X (dict h).1).dom) →
    (∀ (A : Type) [Fintype A] [DecidableEq A] (ν : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ → A),
      (∀ u : GA D V, gLat V u = latHat V →
        (∃ w ∈ GlobalTheory.AdLat.hat1 D.host.F (Set.range (algebraMap (𝓞 D.host.E) D.host.E)),
        ((Matrix.GeneralLinearGroup.det (finHom V u) : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) :
          (Af D.host.F ⊗[D.host.F] D.host.E)) - 1 = (l₂.M : ℕ) • w) →
        ∀ h, ν (Matrix.GeneralLinearGroup.det (finHom V (h * u))) = ν (Matrix.GeneralLinearGroup.det (finHom V h))) →
      (∀ γ ∈ GQ V, ∀ h,
        ν (Matrix.GeneralLinearGroup.det (finHom V (γ * h))) = ν (Matrix.GeneralLinearGroup.det (finHom V h))) →
      ∃ cs : A → Rul Xo₂ c₂, (∀ a, cs a ∈ sec Xo₂ c₂ 0 0) ∧ (∀ a, cs a * cs a = cs a) ∧
        (∀ a b, a ≠ b → cs a * cs b = 0) ∧ ∑ a, cs a = 1 ∧
        ∀ h γ : GA D V, MarkBy U V hr dict io F ik φ h γ → ∀ a,
          rdU U (cs a) (dict h).1 (dict h).2 =
            if ν (Matrix.GeneralLinearGroup.det (finHom V (γ * h))) = a then 1 else 0) ∧
    ∀ xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ,
      (∀ u : GA D V, gLat V u = latHat V →
        (∃ w ∈ GlobalTheory.AdLat.hat1 D.host.F (Set.range (algebraMap (𝓞 D.host.E) D.host.E)),
        ((Matrix.GeneralLinearGroup.det (finHom V u) : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) :
          (Af D.host.F ⊗[D.host.F] D.host.E)) - 1 = (l₂.M : ℕ) • w) →
        xi (Matrix.GeneralLinearGroup.det (finHom V u)) = 1) →
      (∀ γ ∈ GQ V, xi (Matrix.GeneralLinearGroup.det (finHom V γ)) = 1) →
      (∀ h : GA D V, ∃ a : c₂.F, σ a = (xi (Matrix.GeneralLinearGroup.det (finHom V h)) : ℂˣ)) →
      ∃ f ∈ sec Xo₂ c₂ 0 0,
        (∀ m : ℕ, (∀ h : GA D V, xi (Matrix.GeneralLinearGroup.det (finHom V h)) ^ m = 1) → f ^ m = 1) ∧
        ∀ h γ : GA D V, MarkBy U V hr dict io F ik φ h γ →
          rdU U f (dict h).1 (dict h).2 = (xi (Matrix.GeneralLinearGroup.det (finHom V (γ * h))) : ℂˣ) := by
  obtain ⟨c₂, hle, hc₂, hun⟩ := GlobalTheory.T.exists_coeff_field_curve _ H l l₂ c n p hp hpn hMn hM hA hgood hcurve
  refine ⟨⟨c₂.F, c₂.fin, c₂.conj, hle c.zeta_mem, c.le.trans hle⟩, c₂, rfl, hle, hc₂, hun, ?_⟩
  intro Dw Xo₂ V io hio hpos hrk
  have hcl := fnAlgClosed_of_iotaOK Xo₂ c₂ V io hio hpos hrk hA hc₂
  refine ⟨hcl, fun σ r hr U dict g e F ik φ th x₀ hσ hW hD hdom => ⟨fun A _ _ ν h1 h2 => ?_, ?_⟩⟩
  · exact exists_idem_rdU_det V io σ r hr U dict g e F ik φ th x₀ hio.emb hW hD hdom hcl ν h1 h2
  · exact GlobalTheory.CharRead.exists_sec_rdU_eq_char D H Dw l₂ Xo₂ c₂ σ V r hr U dict io g e F ik φ th x₀ hio hpos hA hσ hW hD
      hdom hcl

end GlobalTheory.DetFibre
end
