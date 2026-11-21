import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IsPowGrpBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDenominatorOfAdelicLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeMapGivesHomomorphism
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOneOfSurjective
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsCounitEqOneMulEqZeroOfIsNilpotent
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsAbelianSchemeModelOfIsogenyDedekind
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointDefinedOverBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveOfSurjectiveOnPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyFiniteFlat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MorphismTrivialOnReducedKernel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomomorphismDescendsToAlgebraic

section
section
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory

open scoped UpperHalfPlane

namespace GlobalTheory.CMModel

theorem j_mul_Δ_eq (F : Type) [Field F] (W : WeierstrassCurve F) [W.IsElliptic] :
    W.j * W.Δ = W.c₄ ^ 3 := by
  rw [WeierstrassCurve.j, ← WeierstrassCurve.coe_Δ', mul_comm]
  exact _root_.Units.mul_inv_cancel_left W.Δ' _

theorem exists_upper_of_sq_eq_neg {d : ℕ} {τ : ℂ} (hd : 0 < d) (h : τ ^ 2 = -(d : ℂ)) :
    ∃ τ₀ : ℍ, (τ₀ : ℂ) = τ ∨ (τ₀ : ℂ) = -τ := by
  have him : τ.im ≠ 0 := by
    intro h0
    have h1 := congrArg Complex.re h
    simp [pow_two, h0] at h1
    have : (0 : ℝ) < d := by exact_mod_cast hd
    nlinarith [sq_nonneg τ.re]
  rcases lt_or_gt_of_ne him with hn | hp
  · exact ⟨⟨-τ, by simpa using hn⟩, Or.inr rfl⟩
  · exact ⟨⟨τ, hp⟩, Or.inl rfl⟩

theorem modularJ_mem_Qb {d : ℕ} {τ₀ : ℍ} (h : (τ₀ : ℂ) ^ 2 = -(d : ℂ)) :
    modularJ τ₀ ∈ algebraicClosure ℚ ℂ := by
  have hi : _root_.IsIntegral ℤ (modularJ τ₀) :=
    isIntegral_modularJ_of_quadratic (a := 1) (b := 0) (c := d) one_ne_zero (by push_cast; rw [h]; ring)
  exact mem_algebraicClosure_iff.2 (hi.tower_top (A := ℚ)).isAlgebraic

end GlobalTheory.CMModel

theorem GlobalTheory.CMModel.exists_curve_lattice :
    ∀ (d : ℕ) (τ : ℂ), 0 < d → τ ^ 2 = -(d : ℂ) →
  ∃ (A₀ : Over (Sp Qb)) (_ : GrpObj A₀) (A : Over (Sp ℂ)) (_ : GrpObj A) (p : A.left ⟶ A₀.left) (L : LB A.left)
    (u : HolUnif A L 1) (c : ℂ), IsAbelianScheme A₀ ∧ SmoothOfRelativeDimension 1 A₀.hom ∧
    IsGrpPullback A A₀ (spMap (algebraMap Qb ℂ)) p ∧ L.IsLB ∧ c ≠ 0 ∧ ∀ z ∈ u.Λ, ∃ a b : ℤ, z 0 = c * (a + b * τ) := by
  classical
  intro d τ hd hτ
  obtain ⟨τ₀, hτ₀⟩ := GlobalTheory.CMModel.exists_upper_of_sq_eq_neg hd hτ
  have hτ₀2 : (τ₀ : ℂ) ^ 2 = -(d : ℂ) := by rcases hτ₀ with e | e <;> rw [e] <;> simp [hτ]
  let j : Qb := ⟨GlobalTheory.modularJ τ₀, GlobalTheory.CMModel.modularJ_mem_Qb hτ₀2⟩
  let W : WeierstrassCurve Qb := WeierstrassCurve.ofJ j
  have hWj : W.j = j := WeierstrassCurve.ofJ_j j
  have hΔ : IsUnit W.Δ := (inferInstance : W.IsElliptic).isUnit
  obtain ⟨P, v, Lf, ⟨hg, hv, -, hU'⟩, hLf⟩ :=
    GlobalTheory.exists_polAV_latticeFamily GlobalTheory.thetaUnifAV_all GlobalTheory.polBaseChange_holds Qb W hΔ
  let s : Qb →+* ℂ := algebraMap Qb ℂ
  obtain ⟨P', φ, h⟩ := GlobalTheory.exists_isPolFibre GlobalTheory.polBaseChange_holds s P
  obtain ⟨v', hv', -⟩ := GlobalTheory.existsUnique_isVecOver h.2.1.1 v
  obtain ⟨rig, hrig⟩ := P'.rigid
  obtain ⟨u, -, -, -, -, -, hd', -⟩ := GlobalTheory.thetaUnifAV_all P' rig hrig
  obtain ⟨w, hw, -⟩ := hd' v' (hv'.isTangent h.2.1 (hv.1 0))
  obtain ⟨hw0, hmem⟩ := hU' s P' φ v' u w h hv' hw
  have hj : s W.j = (GlobalTheory.latticeCurve (GlobalTheory.periodPairOfTau τ₀)).j := by
    rw [hWj, GlobalTheory.latticeCurve_j one_ne_zero (GlobalTheory.mem_lattice_periodPairOfTau τ₀)]
    rfl
  have e1 := congrArg s (GlobalTheory.CMModel.j_mul_Δ_eq Qb W)
  rw [map_mul, map_pow, hj, (hLf s).1, (hLf s).2.2] at e1
  have e2 := GlobalTheory.CMModel.j_mul_Δ_eq ℂ (GlobalTheory.latticeCurve (GlobalTheory.periodPairOfTau τ₀))
  rw [GlobalTheory.latticeCurve_Δ, GlobalTheory.latticeCurve_c₄] at e2
  have key : (GlobalTheory.periodPairOfTau τ₀).g₂ ^ 3 * ((Lf s).g₂ ^ 3 - 27 * (Lf s).g₃ ^ 2) =
      (Lf s).g₂ ^ 3 * ((GlobalTheory.periodPairOfTau τ₀).g₂ ^ 3 - 27 * (GlobalTheory.periodPairOfTau τ₀).g₃ ^ 2) := by
    linear_combination (((GlobalTheory.periodPairOfTau τ₀).g₂ ^ 3 - 27 * (GlobalTheory.periodPairOfTau τ₀).g₃ ^ 2) * e1 -
      ((Lf s).g₂ ^ 3 - 27 * (Lf s).g₃ ^ 2) * e2) / 1728
  obtain ⟨c, hc0, hc⟩ := (GlobalTheory.lattice_determined_by_invariants (GlobalTheory.periodPairOfTau τ₀) (Lf s)).2 key
  cases P' with | mk A' isAb' g' sm' L' isLB' rig' sym' amp' kt' => ?_
  have e : g' = 1 := h.1.trans hg
  subst e
  have hw00 : w 0 ≠ 0 := fun h0 => hw0 (funext fun i => by fin_cases i; exact h0)
  refine ⟨P.A, inferInstance, A', inferInstance, φ, L', u, w 0 * c, P.isAb, hg ▸ P.smoothDim, h.2.1,
    isLB', mul_ne_zero hw00 hc0, fun z hz => ?_⟩
  have hz' : z = (z 0 / w 0) • w := funext fun i => by
    fin_cases i
    simp [hw00]
  obtain ⟨x, hx, hxz⟩ := (hc _).1 ((hmem (z 0 / w 0)).2 (hz' ▸ hz))
  obtain ⟨m, n, rfl⟩ := (GlobalTheory.mem_lattice_periodPairOfTau τ₀ x).1 hx
  have hz0 : z 0 = w 0 * c * (1 * (m * (τ₀ : ℂ) + n)) := by
    rw [_root_.mul_assoc, ← hxz]
    field_simp
  rcases hτ₀ with e | e
  · exact ⟨n, m, by rw [hz0, e]; ring⟩
  · exact ⟨n, -m, by rw [hz0, e]; push_cast; ring⟩
end

open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.elliptic_curve_lattice_period_form : ∀ (d : ℕ) (τ : ℂ), 0 < d → τ ^ 2 = -(d : ℂ) →
  ∃ (A₀ : Over (Sp Qb)) (_ : GrpObj A₀) (A : Over (Sp ℂ)) (_ : GrpObj A) (p : A.left ⟶ A₀.left) (L : LB A.left)
    (u : HolUnif A L 1) (c : ℂ), IsAbelianScheme A₀ ∧ SmoothOfRelativeDimension 1 A₀.hom ∧
    IsGrpPullback A A₀ (spMap (algebraMap Qb ℂ)) p ∧ L.IsLB ∧ c ≠ 0 ∧ ∀ z ∈ u.Λ, ∃ a b : ℤ, z 0 = c * (a + b * τ) := by
  atlas_forward_decl GlobalTheory.CMModel.exists_curve_lattice
end

section
section
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
open CategoryTheory.Limits
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.EllPowModel

def isPowGrpIso {S : Scheme.{0}} {G' G H : Over S} [GrpObj G'] [GrpObj G] [GrpObj H] {j : ℕ}
    (p : Out.IsPowGrp G' G j) (e : G ≅ H) [IsMonHom e.hom] : Out.IsPowGrp G' H j where
  pr i := p.pr i ≫ e.hom
  hom i := by haveI := p.hom i; infer_instance
  lim := mkFanLimit _ (fun s => p.lim.lift (Fan.mk s.pt (fun i => s.proj i ≫ e.inv)))
    (fun s i => by
      have h : p.lim.lift (Fan.mk s.pt (fun i => s.proj i ≫ e.inv)) ≫ p.pr i = s.proj i ≫ e.inv :=
        p.lim.fac (Fan.mk s.pt (fun i => s.proj i ≫ e.inv)) ⟨i⟩
      show _ ≫ (p.pr i ≫ e.hom) = _
      rw [← Category.assoc, h, Category.assoc, e.inv_hom_id, Category.comp_id])
    (fun s m hm => p.lim.hom_ext fun ⟨i⟩ => by
      have h : p.lim.lift (Fan.mk s.pt (fun i => s.proj i ≫ e.inv)) ≫ p.pr i = s.proj i ≫ e.inv :=
        p.lim.fac (Fan.mk s.pt (fun i => s.proj i ≫ e.inv)) ⟨i⟩
      have hmi : m ≫ p.pr i ≫ e.hom = s.proj i := hm i
      show m ≫ p.pr i = p.lim.lift (Fan.mk s.pt (fun i => s.proj i ≫ e.inv)) ≫ p.pr i
      rw [h, ← hmi, Category.assoc, Category.assoc, e.hom_inv_id, Category.comp_id])

theorem main : ∀ (k : Type) [Field k] (σ : k →+* ℂ) (A₀ : Over (Sp k)) [GrpObj A₀] (A : Over (Sp ℂ)) [GrpObj A]
    (p : A.left ⟶ A₀.left) (L : LB A.left) (u : HolUnif A L 1), IsAbelianScheme A₀ → SmoothOfRelativeDimension 1 A₀.hom →
    IsGrpPullback A A₀ (spMap σ) p → L.IsLB → ∀ n : ℕ,
  ∃ (B₀ : Over (Sp k)) (_ : GrpObj B₀) (B : Over (Sp ℂ)) (_ : GrpObj B) (q : B.left ⟶ B₀.left) (M : LB B.left)
    (v : HolUnif B M n), IsAbelianScheme B₀ ∧ SmoothOfRelativeDimension n B₀.hom ∧ IsAbelianScheme B ∧
    SmoothOfRelativeDimension n B.hom ∧ IsGrpPullback B B₀ (spMap σ) q ∧ ∀ z ∈ v.Λ, ∀ j, (fun _ : Fin 1 ↦ z j) ∈ u.Λ := by
  intro k _ σ A₀ _ A _ p L u hA₀ hd hp hL n
  let B₀ : Over (Sp k) := Out.powObj A₀ n
  let B : Over (Sp ℂ) := (Over.pullback (spMap σ)).obj B₀
  have P := PowGrp.powers (Sp k) B₀ A₀ n (Out.powIsPowGrp A₀ n)
  have hB₀ : IsAbelianScheme B₀ := P.2.2.2.1 hA₀
  have hdB₀ : SmoothOfRelativeDimension n B₀.hom := by
    have := P.2.2.1 1 hd
    rwa [Nat.mul_one] at this
  have hB : IsAbelianScheme B := isAbelianScheme_pullback_obj (spMap σ) B₀ hB₀
  have hdB : SmoothOfRelativeDimension n B.hom := by
    have : SmoothOfRelativeDimension n (pullback.snd B₀.hom (spMap σ)) :=
      (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
        (IsPullback.of_hasPullback _ _) hdB₀
    exact this
  obtain ⟨p', -⟩ := isPowGrp_baseChange (Sp k) (Sp ℂ) (spMap σ) B₀ A₀ n (Out.powIsPowGrp A₀ n)
  obtain ⟨e, he, -⟩ := grpPullback_iso (isGrpPullback_pullback A₀ (spMap σ)) hp
  let pw : Out.IsPowGrp B A n := isPowGrpIso p' e
  obtain ⟨w, hw⟩ := PolBaseChange.lbIso_refl (LB.isLB_linComb hL (fun i => (pw.pr i).left) (fun _ => (1 : ℤ)))
  obtain ⟨v, hv, -, -⟩ := PowUnif.exists_powUnif pw u hL (LB.isLB_linComb hL (fun i => (pw.pr i).left) (fun _ => (1 : ℤ)))
    w hw (Equiv.prodUnique (Fin n) (Fin 1))
  refine ⟨B₀, inferInstance, B, inferInstance, pullback.fst B₀.hom (spMap σ), _, v, hB₀, hdB₀, hB, hdB,
    isGrpPullback_pullback B₀ (spMap σ), fun z hz j => ?_⟩
  have := (hv z).1 hz j
  rw [PowUnif.blockPr_apply] at this
  convert this using 2 with a
  rw [Fin.fin_one_eq_zero a]
  rfl

end GlobalTheory.EllPowModel
end
end

open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_scheme_descent_with_uniformization : ∀ (k : Type) [Field k] (σ : k →+* ℂ) (A₀ : Over (Sp k)) [GrpObj A₀] (A : Over (Sp ℂ)) [GrpObj A]
    (p : A.left ⟶ A₀.left) (L : LB A.left) (u : HolUnif A L 1), IsAbelianScheme A₀ → SmoothOfRelativeDimension 1 A₀.hom →
    IsGrpPullback A A₀ (spMap σ) p → L.IsLB → ∀ n : ℕ,
  ∃ (B₀ : Over (Sp k)) (_ : GrpObj B₀) (B : Over (Sp ℂ)) (_ : GrpObj B) (q : B.left ⟶ B₀.left) (M : LB B.left)
    (v : HolUnif B M n), IsAbelianScheme B₀ ∧ SmoothOfRelativeDimension n B₀.hom ∧ IsAbelianScheme B ∧
    SmoothOfRelativeDimension n B.hom ∧ IsGrpPullback B B₀ (spMap σ) q ∧ ∀ z ∈ v.Λ, ∀ j, (fun _ : Fin 1 ↦ z j) ∈ u.Λ := by
  atlas_forward_decl GlobalTheory.EllPowModel.main
end

section
section
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LatModel

theorem surj_lattice : ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (io : K →+* ℂ), Module.finrank ℚ K = 2 → 0 < d → δ ^ 2 = -(d : K) →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
      IsCMType φ → (∀ i, (φ i).comp (algebraMap K E) = io) → ∀ (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ →
      ∀ e : Fin (Module.finrank ℚ (FR E)) ≃ I,
      ∃ M : (Fin (Module.finrank ℚ (FR E)) → ℂ) →ₗ[ℂ] (Fin (Module.finrank ℚ (FR E)) → ℂ), Function.Surjective M ∧
        ∀ z, (∀ j, ∃ a b : ℤ, z j = a + b * io δ) → ∃ x ∈ lattice c y, M z = fun j ↦ φ (e j) x := by
  intro K _ _ d δ io hK hd hδ E _ _ _ _ I _ φ hφ hio c y hc e
  classical
  have hEK : Module.finrank K E = Module.finrank ℚ (FR E) := by
    have h1 : Module.finrank ℚ E = 2 * Module.finrank ℚ (FR E) := by
      rw [← Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E,
        Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E, mul_comm]
    have h2 : Module.finrank ℚ K * Module.finrank K E = Module.finrank ℚ E := Module.finrank_mul_finrank ℚ K E
    rw [hK, h1] at h2
    omega
  generalize Module.finrank ℚ (FR E) = f at e hEK ⊢
  let b := Module.finBasisOfFinrankEq K E hEK
  obtain ⟨m, hm0, hm⟩ := exists_integral_multiples ℤ ℚ (L := E) (Finset.univ.image b)
  obtain ⟨N, hN0, hNmem, -⟩ := GlobalTheory.CMVal.LatBound.lattice_between E c hc y

  have hint : ∀ j, IsIntegral ℤ (m • b j) := fun j => hm _ (Finset.mem_image_of_mem _ (Finset.mem_univ j))
  have hδint : IsIntegral ℤ (algebraMap K E δ) := by
    refine ⟨Polynomial.X ^ 2 + Polynomial.C (d : ℤ), ?_, ?_⟩
    · exact Polynomial.monic_X_pow_add_C _ two_ne_zero
    · simp only [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_C]
      rw [← map_pow, hδ]; simp
  let u : Fin f → 𝓞 E := fun j => ⟨m • b j, hint j⟩
  let v : Fin f → 𝓞 E := fun j => ⟨algebraMap K E δ * (m • b j), hδint.mul (hint j)⟩
  let w : Fin f → E := fun j => (N : E) * (m • b j)
  have hw : ∀ j, w j ∈ lattice c y := fun j => hNmem (u j)
  have hδw : ∀ j, algebraMap K E δ * w j ∈ lattice c y := fun j => by
    have := hNmem (v j)
    simpa [w, v, mul_left_comm] using this

  have hs : ∀ _j : Fin f, IsUnit ((N : K) * (m : K)) := fun _ => by
    refine IsUnit.mk0 _ (mul_ne_zero (by exact_mod_cast hN0.ne') (by exact_mod_cast hm0))
  let b' := b.isUnitSMul hs
  have hb' : ∀ j, b' j = w j := fun j => by
    simp only [b', Module.Basis.isUnitSMul_apply, w, Algebra.smul_def, zsmul_eq_mul, map_mul, map_natCast, map_intCast]
    simp only [algebraMap_int_eq, eq_intCast]
    ring
  let A : Matrix (Fin f) (Fin f) ℂ := fun i j => φ (e i) (w j)
  refine ⟨Matrix.mulVecLin A, ?_, ?_⟩
  ·
    show Function.Surjective A.mulVec
    rw [Matrix.mulVec_surjective_iff_isUnit, ← Matrix.linearIndependent_rows_iff_isUnit]
    have hinj : Function.Injective (fun i : Fin f => ((φ (e i) : E →+* ℂ) : E →* ℂ)) := by
      intro i i' h
      have h' : φ (e i) = φ (e i') := RingHom.ext fun x => DFunLike.congr_fun h x
      obtain ⟨k, -, hk⟩ := hφ (φ (e i))
      have a1 := hk (e i) (Or.inl rfl)
      have a2 := hk (e i') (Or.inl h')
      exact e.injective (a1.trans a2.symm)
    have li : LinearIndependent ℂ (fun i : Fin f => ((((φ (e i) : E →+* ℂ) : E →* ℂ)) : E → ℂ)) :=
      (linearIndependent_monoidHom E ℂ).comp _ hinj
    rw [Fintype.linearIndependent_iff] at li ⊢
    intro g hg i
    refine li g ?_ i
    funext x
    have hrow : ∀ j, ∑ i, g i * φ (e i) (w j) = 0 := fun j => by
      have := congrFun hg j
      simpa [Matrix.row, A, Finset.sum_apply] using this
    have hx : x = ∑ j, b'.repr x j • w j := by
      conv_lhs => rw [← b'.sum_repr x]
      simp only [hb']
    simp only [Finset.sum_apply, Pi.smul_apply, MonoidHom.coe_coe, smul_eq_mul, Pi.zero_apply]
    rw [hx]
    simp only [map_sum, Algebra.smul_def, map_mul]
    have hio' : ∀ i (k : K), φ (e i) (algebraMap K E k) = io k := fun i k => by
      rw [← hio (e i)]; rfl
    simp only [hio']
    calc ∑ i, g i * ∑ j, io (b'.repr x j) * φ (e i) (w j)
        = ∑ j, io (b'.repr x j) * ∑ i, g i * φ (e i) (w j) := by
          simp only [Finset.mul_sum]; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
      _ = 0 := by simp [hrow]
  · intro z hz
    choose a a' ha using hz
    refine ⟨∑ j, ((a j : E) * w j + (a' j : E) * (algebraMap K E δ * w j)), ?_, ?_⟩
    · rw [← coe_latticeSub]
      refine AddSubgroup.sum_mem _ fun j _ => AddSubgroup.add_mem _ ?_ ?_
      · rw [← zsmul_eq_mul]; exact AddSubgroup.zsmul_mem _ (hw j) _
      · rw [← zsmul_eq_mul]; exact AddSubgroup.zsmul_mem _ (hδw j) _
    · funext i
      have hio' : φ (e i) (algebraMap K E δ) = io δ := by rw [← hio (e i)]; rfl
      show A.mulVec z i = φ (e i) _
      simp only [Matrix.mulVec, dotProduct, A, map_sum, map_add, map_mul, map_intCast, hio', ha]
      refine Finset.sum_congr rfl fun j _ => by ring

end GlobalTheory.LatModel
end

open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_period_matrix_exists : ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (io : K →+* ℂ), Module.finrank ℚ K = 2 → 0 < d → δ ^ 2 = -(d : K) →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
      IsCMType φ → (∀ i, (φ i).comp (algebraMap K E) = io) → ∀ (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ →
      ∀ e : Fin (Module.finrank ℚ (FR E)) ≃ I,
      ∃ M : (Fin (Module.finrank ℚ (FR E)) → ℂ) →ₗ[ℂ] (Fin (Module.finrank ℚ (FR E)) → ℂ), Function.Surjective M ∧
        ∀ z, (∀ j, ∃ a b : ℤ, z j = a + b * io δ) → ∃ x ∈ lattice c y, M z = fun j ↦ φ (e j) x := by
  atlas_forward_decl GlobalTheory.LatModel.surj_lattice
end

section
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_map_gives_homomorphism : ∀ (A A' : Over (Sp ℂ)) [GrpObj A] [GrpObj A'] (g : ℕ), IsAbelianScheme A → IsAbelianScheme A' →
    SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g A'.hom →
    ∀ (L : LB A.left) (L' : LB A'.left) (u : HolUnif A L g) (u' : HolUnif A' L' g) (M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)),
      (∀ x ∈ u.Λ, M x ∈ u'.Λ) → ∃ α : A ⟶ A', IsMonHom α ∧ ∀ w, u'.ex (M w) = u.ex w ≫ α := by
  first | exact @GlobalTheory.HolUnifHom.exists_isMonHom_of_map_lattice | exact GlobalTheory.HolUnifHom.exists_isMonHom_of_map_lattice | (intros; apply GlobalTheory.HolUnifHom.exists_isMonHom_of_map_lattice <;> assumption)
end

section
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.surjective_of_surjective_on_points : ∀ (A X : Over (Sp ℂ)) [GrpObj A] [GrpObj X] (ψ : A ⟶ X), IsAbelianScheme A → IsAbelianScheme X →
    (∀ y : 𝟙_ (Over (Sp ℂ)) ⟶ X, ∃ x : 𝟙_ (Over (Sp ℂ)) ⟶ A, x ≫ ψ = y) → Surjective ψ.left := by
  first | exact @GlobalTheory.ComplexAbVarSurj.surjective_of_surjective_points | exact GlobalTheory.ComplexAbVarSurj.surjective_of_surjective_points | (intros; apply GlobalTheory.ComplexAbVarSurj.surjective_of_surjective_points <;> assumption)
end

section
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isogeny_finite_flat : ∀ (A X : Over (Sp ℂ)) [GrpObj A] [GrpObj X] (g : ℕ), IsAbelianScheme A → IsAbelianScheme X →
    SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g X.hom →
    ∀ (ψ : A ⟶ X) [IsMonHom ψ] [Surjective ψ.left], IsFinite ψ.left ∧ Flat ψ.left := by
  first | exact @GlobalTheory.SurjHomFlat.finite_flat | exact GlobalTheory.SurjHomFlat.finite_flat | (intros; apply GlobalTheory.SurjHomFlat.finite_flat <;> assumption)
end

section
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.morphism_trivial_on_reduced_kernel : ∀ (A Y Y' Z : Over (Sp ℂ)) [GrpObj A] [GrpObj Y] [GrpObj Y'] [IsSeparated Y'.hom] (u : A ⟶ Y) (f : A ⟶ Y')
    (i : Z ⟶ A), IsPullback i (toUnit Z) u η[Y] → ∀ [AlgebraicGeometry.IsReduced Z.left] [LocallyOfFiniteType Z.hom],
    (∀ x : 𝟙_ (Over (Sp ℂ)) ⟶ A, x ≫ u = 1 → x ≫ f = 1) →
    ∀ (T : Over (Sp ℂ)) (x : T ⟶ A), x ≫ u = 1 → x ≫ f = 1 := by
  first | exact @GlobalTheory.KernelKill.comp_eq_one_of_kill_closedPoints | exact GlobalTheory.KernelKill.comp_eq_one_of_kill_closedPoints | (intros; apply GlobalTheory.KernelKill.comp_eq_one_of_kill_closedPoints <;> assumption)
end

section
section
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RealMult

theorem torsion_of_complex_is_algebraic : ∀ (A₀ : Over (Sp Qb)) [GrpObj A₀] (A : Over (Sp ℂ)) [GrpObj A] (p : A.left ⟶ A₀.left) (g n : ℕ),
    IsAbelianScheme A₀ → SmoothOfRelativeDimension g A₀.hom → IsGrpPullback A A₀ (spMap (algebraMap Qb ℂ)) p →
    1 ≤ n → ∀ x : 𝟙_ (Over (Sp ℂ)) ⟶ A, x ^ n = 1 →
    ∃ c : 𝟙_ (Over (Sp Qb)) ⟶ A₀, x.left ≫ p = spMap (algebraMap Qb ℂ) ≫ c.left := by
  intro A₀ _ A _ p g n hA₀ hg hp hn x hx
  set t : Sp ℂ ⟶ Sp Qb := spMap (algebraMap Qb ℂ) with ht
  have hM := GlobalTheory.abMulN_holds
  have : IsAlgClosed Qb := (algebraicClosure.isAlgClosure ℚ ℂ).isAlgClosed
  have hSub : Subsingleton (Sp Qb) := inferInstanceAs (Subsingleton (PrimeSpectrum Qb))
  have : Flat t := inferInstance
  have : Surjective t := ⟨fun _ => ⟨(default : PrimeSpectrum ℂ), Subsingleton.elim _ _⟩⟩
  have : Epi t := Flat.epi_of_flat_of_surjective _
  have hA : IsAbelianScheme A := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA₀ hp
  have hdim : SmoothOfRelativeDimension g A.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hp.1 hg
  obtain ⟨e, he⟩ := GlobalTheory.exists_mulEquiv_of_isGrpPullback hp (𝟙 (Sp ℂ)) t (Category.id_comp t).symm
  have hnQ : ((n : ℕ) : Qb) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hnC : ((n : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have h₁ := hM Qb A₀ g n hA₀ hg hnQ
  have h₂ := hM ℂ A g n hA hdim hnC
  have hl : (toUnit (Over.mk t)).left = t := by simpa using Over.w (toUnit (Over.mk t))
  let r : {c : 𝟙_ (Over (Sp Qb)) ⟶ A₀ // c ^ n = 1} → {y : 𝟙_ (Over (Sp ℂ)) ⟶ A // y ^ n = 1} := fun c =>
    ⟨e.symm (toUnit (Over.mk t) ≫ c.1), by
      change e.symm _ ^ n = 1
      rw [← map_pow, ← MonObj.comp_pow, c.2, MonObj.comp_one, map_one]⟩
  have hr : Function.Injective r := fun a b h => Subtype.ext (Over.OverMorphism.ext ((cancel_epi t).1 (by
    have h' := congrArg (fun q => (e q.1).left) h
    simpa only [r, MulEquiv.apply_symm_apply, Over.comp_left, hl] using h')))
  have : Finite {y : 𝟙_ (Over (Sp ℂ)) ⟶ A // y ^ n = 1} := GlobalTheory.Published.AbMulNSt.finite hM hA hdim hnC
  obtain ⟨c, hc⟩ := ((Nat.bijective_iff_injective_and_card r).2 ⟨hr, h₁.trans h₂.symm⟩).2 ⟨x, hx⟩
  refine ⟨c.1, ?_⟩
  have h3 : e x = toUnit (Over.mk t) ≫ c.1 := by
    have hx' : e.symm (toUnit (Over.mk t) ≫ c.1) = x := congrArg Subtype.val hc
    rw [← hx', MulEquiv.apply_symm_apply]
  rw [← he x, h3, Over.comp_left, hl]

end GlobalTheory.RealMult
end

open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_point_algebraic_model : ∀ (A₀ : Over (Sp Qb)) [GrpObj A₀] (A : Over (Sp ℂ)) [GrpObj A] (p : A.left ⟶ A₀.left) (g n : ℕ),
    IsAbelianScheme A₀ → SmoothOfRelativeDimension g A₀.hom → IsGrpPullback A A₀ (spMap (algebraMap Qb ℂ)) p →
    1 ≤ n → ∀ x : 𝟙_ (Over (Sp ℂ)) ⟶ A, x ^ n = 1 →
    ∃ c : 𝟙_ (Over (Sp Qb)) ⟶ A₀, x.left ≫ p = spMap (algebraMap Qb ℂ) ≫ c.left := by
  atlas_forward_decl GlobalTheory.RealMult.torsion_of_complex_is_algebraic
end

section
section
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IsogModel

theorem exists_model_of_surjective : ∀ (A₀ : Over (Sp Qb)) [GrpObj A₀] (A X : Over (Sp ℂ)) [GrpObj A] [GrpObj X] (p : A.left ⟶ A₀.left) (g : ℕ),
    IsAbelianScheme A₀ → SmoothOfRelativeDimension g A₀.hom → IsGrpPullback A A₀ (spMap (algebraMap Qb ℂ)) p →
    IsAbelianScheme X → SmoothOfRelativeDimension g X.hom → ∀ ψ : A ⟶ X, IsMonHom ψ →
    (∀ y : 𝟙_ (Over (Sp ℂ)) ⟶ X, ∃ x : 𝟙_ (Over (Sp ℂ)) ⟶ A, x ≫ ψ = y) →
  ∃ (X₀ : Over (Sp Qb)) (_ : GrpObj X₀) (q : X.left ⟶ X₀.left), IsAbelianScheme X₀ ∧ SmoothOfRelativeDimension g X₀.hom ∧
    IsGrpPullback X X₀ (spMap (algebraMap Qb ℂ)) q := by
  intro A₀ _ A X _ _ p g hA₀ hg₀ hp hX hgX ψ hψ hpts
  haveI : IsAlgClosed Qb := (algebraicClosure.isAlgClosure ℚ ℂ).isAlgClosed
  have hA : IsAbelianScheme A := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA₀ hp
  have hgA : SmoothOfRelativeDimension g A.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hp.1 hg₀
  haveI : Surjective ψ.left := GlobalTheory.T.surjective_of_surjective_on_points A X ψ hA hX hpts
  obtain ⟨hfin, hflat⟩ := GlobalTheory.T.isogeny_finite_flat A X g hA hX hgA hgX ψ
  obtain ⟨n, hn, hkn⟩ := GlobalTheory.HolUnifEnd.exists_pow_eq_one_of_surjective A X g hA hX hgA hgX ψ
  set t : Sp ℂ ⟶ Sp Qb := spMap (algebraMap Qb ℂ) with ht
  have hSub : Subsingleton (Sp Qb) := inferInstanceAs (Subsingleton (PrimeSpectrum Qb))
  have : Flat t := inferInstance
  have : Surjective t := ⟨fun _ => ⟨(default : PrimeSpectrum ℂ), Subsingleton.elim _ _⟩⟩
  have : Epi t := Flat.epi_of_flat_of_surjective _
  obtain ⟨e, he⟩ := GlobalTheory.exists_mulEquiv_of_isGrpPullback hp (𝟙 (Sp ℂ)) t (Category.id_comp t).symm
  have hl : (toUnit (Over.mk t)).left = t := by simpa using Over.w (toUnit (Over.mk t))
  let r : (𝟙_ (Over (Sp Qb)) ⟶ A₀) →* (Over.mk t ⟶ A₀) :=
    { toFun := fun c => toUnit (Over.mk t) ≫ c
      map_one' := MonObj.comp_one _
      map_mul' := fun a b => MonObj.comp_mul _ _ _ }
  have hr : Function.Injective r := fun a b h => Over.OverMorphism.ext ((cancel_epi t).1 (by
    have := congrArg (fun q => q.left) h
    simpa only [r, MonoidHom.coe_mk, OneHom.coe_mk, Over.comp_left, hl] using this))
  let ψp : (Over.mk (𝟙 (Sp ℂ)) ⟶ A) →* (Over.mk (𝟙 (Sp ℂ)) ⟶ X) :=
    { toFun := fun x => x ≫ ψ
      map_one' := MonObj.one_comp _
      map_mul' := fun a b => MonObj.mul_comp _ _ _ }
  let C₀ : Subgroup (𝟙_ (Over (Sp Qb)) ⟶ A₀) := (ψp.comp (e.symm.toMonoidHom.comp r)).ker
  have hC : ∀ c, c ∈ C₀ ↔ e.symm (r c) ≫ ψ = 1 := fun c => Iff.rfl
  have hnQ : ((n : ℕ) : Qb) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hfinT := GlobalTheory.Published.AbMulNSt.finite GlobalTheory.abMulN_holds hA₀ hg₀ hnQ
  have hC₀ : Finite C₀ := by
    refine Finite.of_injective (β := {c : 𝟙_ (Over (Sp Qb)) ⟶ A₀ // c ^ n = 1})
      (fun c => ⟨c.1, ?_⟩) (fun a b h => Subtype.ext (by simpa using congrArg Subtype.val h))
    have h1 := hkn (e.symm (r c.1)) ((hC c.1).1 c.2)
    apply hr
    rw [map_pow, map_one, ← e.apply_symm_apply (r c.1), ← map_pow, h1, map_one]
  obtain ⟨X₀, _, π₀, hX₀, hπ₀, hfin₀, het₀, hsurj₀, hker₀⟩ :=
    GlobalTheory.exists_quotient_abelian_by_finite_points Qb A₀ hA₀ C₀ hC₀
  haveI := hπ₀
  have hgX₀ : SmoothOfRelativeDimension g X₀.hom := by
    have := hX₀.smooth
    exact GlobalTheory.SmoothDescent.smoothOfRelativeDimension_of_etale_cover Qb A₀.left X₀.left π₀.left X₀.hom g het₀
      hsurj₀ inferInstance (by rw [Over.w]; exact hg₀)
  let X' : Over (Sp ℂ) := (Over.pullback t).obj X₀
  letI : GrpObj X' := Functor.grpObjObj
  have hX' : IsGrpPullback X' X₀ t (pullback.fst X₀.hom t) := isGrpPullback_pullback X₀ t
  have hXa' : IsAbelianScheme X' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hX₀ hX'
  obtain ⟨e', he'⟩ := GlobalTheory.exists_mulEquiv_of_isGrpPullback hX' (𝟙 (Sp ℂ)) t (Category.id_comp t).symm
  obtain ⟨π, hπ, hπp⟩ := GlobalTheory.HomDescent.exists_isMonHom_pull hp hX' π₀
  haveI := hπ
  have hsq : IsPullback p π.left π₀.left (pullback.fst X₀.hom t) :=
    IsPullback.of_bot (by rw [Over.w π, Over.w π₀]; exact hp.1) hπp.symm hX'.1
  have hπe : Etale π.left := MorphismProperty.of_isPullback (P := @Etale) hsq het₀
  have hπs : Surjective π.left := MorphismProperty.of_isPullback (P := @Surjective) hsq hsurj₀
  have hπf : IsFinite π.left := MorphismProperty.of_isPullback (P := @IsFinite) hsq hfin₀

  have key : ∀ x : 𝟙_ (Over (Sp ℂ)) ⟶ A, e' (x ≫ π) = e x ≫ π₀ := fun x => by
    refine Over.OverMorphism.ext ?_
    rw [he', Over.comp_left, Over.comp_left, he, Category.assoc, hπp, Category.assoc]
  have hsep : IsSeparated X.hom := by have := hX.proper; infer_instance
  have hsep' : IsSeparated X'.hom := by have := hXa'.proper; infer_instance

  obtain ⟨Zπ, _, iπ, _, _, hkπ⟩ := GlobalTheory.TorsionKernelModel.exists_kernel π
  have hZπ : Etale Zπ.hom := by
    have h1 : Etale (toUnit Zπ).left :=
      MorphismProperty.of_isPullback (P := @Etale) (hkπ.map (Over.forget _)) hπe
    have h2 : (toUnit Zπ).left = Zπ.hom := by simpa using Over.w (toUnit Zπ)
    rwa [h2] at h1
  haveI : IsReduced Zπ.left := GlobalTheory.isReduced_of_smooth_of_isReduced Zπ.hom
  have hkill1 : ∀ (T : Over (Sp ℂ)) (x : T ⟶ A), x ≫ π = 1 → x ≫ ψ = 1 := by
    refine GlobalTheory.T.morphism_trivial_on_reduced_kernel A X' X Zπ π ψ iπ hkπ fun x hx => ?_
    have h1 : e x ≫ π₀ = 1 := by rw [← key, hx, map_one]
    obtain ⟨c, hc, hcx⟩ := (hker₀ ℂ t (e x)).1 h1
    have : x = e.symm (r c) := by rw [show r c = e x from hcx.symm]; simp
    rw [this]
    exact (hC c).1 hc
  obtain ⟨⟨β, hβ, hβc⟩, hepiπ⟩ := GlobalTheory.exists_monHom_factor_of_flat_surjective _ A X' X π ψ hπ hψ
    inferInstance hπs inferInstance hkill1

  obtain ⟨Zψ, _, iψ, _, _, hkψ⟩ := GlobalTheory.TorsionKernelModel.exists_kernel ψ
  have hZψf : IsFinite Zψ.hom := by
    have h1 : IsFinite (toUnit Zψ).left :=
      MorphismProperty.of_isPullback (P := @IsFinite) (hkψ.map (Over.forget _)) hfin
    have h2 : (toUnit Zψ).left = Zψ.hom := by simpa using Over.w (toUnit Zψ)
    rwa [h2] at h1
  letI : GrpObj (Over.mk Zψ.hom) := ‹GrpObj Zψ›
  have hZψ : Etale Zψ.hom := GlobalTheory.etale_of_grpObj_of_isFinite (k := ℂ) Zψ.hom
  haveI : IsReduced Zψ.left := GlobalTheory.isReduced_of_smooth_of_isReduced Zψ.hom
  have hkill2 : ∀ (T : Over (Sp ℂ)) (x : T ⟶ A), x ≫ ψ = 1 → x ≫ π = 1 := by
    refine GlobalTheory.T.morphism_trivial_on_reduced_kernel A X X' Zψ ψ π iψ hkψ fun x hx => ?_
    obtain ⟨c, hc⟩ := GlobalTheory.T.torsion_point_algebraic_model A₀ A p g n hA₀ hg₀ hp hn x (hkn x hx)
    have hxc : e x = r c := Over.OverMorphism.ext (by
      rw [he, hc]
      show t ≫ c.left = (toUnit (Over.mk t) ≫ c).left
      rw [Over.comp_left, hl])
    have hcC : c ∈ C₀ := by
      rw [hC, ← hxc, e.symm_apply_apply]; exact hx
    have h1 : e x ≫ π₀ = 1 := (hker₀ ℂ t (e x)).2 ⟨c, hcC, hxc⟩
    rw [← key] at h1
    exact (map_eq_one_iff e' e'.injective).1 h1
  obtain ⟨⟨κ, hκ, hκc⟩, hepiψ⟩ := GlobalTheory.exists_monHom_factor_of_flat_surjective _ A X X' ψ π hψ hπ
    hflat inferInstance inferInstance hkill2
  have h1 : β ≫ κ = 𝟙 X' := (cancel_epi π).1 (by rw [← Category.assoc, hβc, hκc, Category.comp_id])
  have h2 : κ ≫ β = 𝟙 X := (cancel_epi ψ).1 (by rw [← Category.assoc, hκc, hβc, Category.comp_id])
  let iso : X ≅ X' := ⟨κ, β, h2, h1⟩
  haveI : IsMonHom iso.hom := hκ
  refine ⟨X₀, inferInstance, κ.left ≫ pullback.fst X₀.hom t, hX₀, hgX₀, ?_⟩
  exact ((isGrpPullback_of_iso iso).comp hX').congr (Category.id_comp t) rfl

end GlobalTheory.IsogModel
end

open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotient_abelian_scheme_descends : ∀ (A₀ : Over (Sp Qb)) [GrpObj A₀] (A X : Over (Sp ℂ)) [GrpObj A] [GrpObj X] (p : A.left ⟶ A₀.left) (g : ℕ),
    IsAbelianScheme A₀ → SmoothOfRelativeDimension g A₀.hom → IsGrpPullback A A₀ (spMap (algebraMap Qb ℂ)) p →
    IsAbelianScheme X → SmoothOfRelativeDimension g X.hom → ∀ ψ : A ⟶ X, IsMonHom ψ →
    (∀ y : 𝟙_ (Over (Sp ℂ)) ⟶ X, ∃ x : 𝟙_ (Over (Sp ℂ)) ⟶ A, x ≫ ψ = y) →
  ∃ (X₀ : Over (Sp Qb)) (_ : GrpObj X₀) (q : X.left ⟶ X₀.left), IsAbelianScheme X₀ ∧ SmoothOfRelativeDimension g X₀.hom ∧
    IsGrpPullback X X₀ (spMap (algebraMap Qb ℂ)) q := by
  atlas_forward_decl GlobalTheory.IsogModel.exists_model_of_surjective
end

section
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homomorphism_descends_to_algebraic : ∀ (A₀ B₀ : Over (Sp Qb)) [GrpObj A₀] [GrpObj B₀] (A B : Over (Sp ℂ)) [GrpObj A] [GrpObj B]
    (p : A.left ⟶ A₀.left) (q : B.left ⟶ B₀.left) (g g' : ℕ), IsAbelianScheme A₀ → SmoothOfRelativeDimension g A₀.hom →
    IsAbelianScheme B₀ → SmoothOfRelativeDimension g' B₀.hom →
    IsGrpPullback A A₀ (spMap (algebraMap Qb ℂ)) p → IsGrpPullback B B₀ (spMap (algebraMap Qb ℂ)) q →
    ∀ α : A ⟶ B, IsMonHom α → ∃ α₀ : A₀ ⟶ B₀, IsMonHom α₀ ∧ α.left ≫ q = p ≫ α₀.left := by
  first | exact @GlobalTheory.HomDescentQb.hom_descends | exact GlobalTheory.HomDescentQb.hom_descends | (intros; apply GlobalTheory.HomDescentQb.hom_descends <;> assumption)
end

section
set_option autoImplicit false

noncomputable section

open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.BirigidLift

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CMModel

theorem cls_eq_of_pull {S S' : Scheme.{0}} {b : S' ⟶ S} [Flat b] [Surjective b] {A B D : Over S} [GrpObj A] [GrpObj D]
    {A' B' D' : Over S'} [GrpObj A'] [GrpObj D'] {f : A'.left ⟶ A.left} {g : B'.left ⟶ B.left} {d : D'.left ⟶ D.left}
    {l : (A' ⊗ B').left ⟶ (A ⊗ B).left} {m : (A' ⊗ D').left ⟶ (A ⊗ D).left}
    (hg : IsPullback g B'.hom B.hom b) (hd : IsGrpPullback D' D b d)
    (l₁ : l ≫ (fst A B).left = (fst A' B').left ≫ f) (l₂ : l ≫ (snd A B).left = (snd A' B').left ≫ g)
    (m₁ : m ≫ (fst A D).left = (fst A' D').left ≫ f) (m₂ : m ≫ (snd A D).left = (snd A' D').left ≫ d)
    {Q : LB (A ⊗ D).left} (q : IsDual A D Q) (q' : IsDual A' D' (Q.pull m))
    {P P' : LB (A ⊗ B).left} (hP : P.IsLB) (hP' : P'.IsLB) (a : IsAdditive P) (a' : IsAdditive P')
    (e : CechPic.pull l (cls P hP) = CechPic.pull l (cls P' hP')) : cls P hP = cls P' hP' := by
  obtain ⟨x, hx, -⟩ := q.univ B P hP a
  obtain ⟨x', hx', -⟩ := q.univ B P' hP' a'
  have ex : cls P hP = evc q.isLB (fst A B) (snd A B ≫ x) := (cls_eq_iff hP (pull_isLB q.isLB _)).2 hx
  have ex' : cls P' hP' = evc q.isLB (fst A B) (snd A B ≫ x') := (cls_eq_iff hP' (pull_isLB q.isLB _)).2 hx'
  have ly : ∀ y : B ⟶ D, ∃ y' : B' ⟶ D', g ≫ y.left = y'.left ≫ d := fun y ↦
    ⟨_, (liftPt_left hd B'.hom (g ≫ y.left) (by rw [Category.assoc, Over.w y, hg.w])).symm⟩
  obtain ⟨y, ey⟩ := ly x
  obtain ⟨y', ey'⟩ := ly x'
  obtain rfl : y = y' := dual_ext q' <| by
    rw [← pull_evc_eq l₁ l₂ m₁ m₂ q.isLB q'.isLB ey, ← pull_evc_eq l₁ l₂ m₁ m₂ q.isLB q'.isLB ey', ← ex, ← ex', e]
  obtain rfl : x = x' := ActDescent.over_hom_ext hg (ey.trans ey'.symm)
  exact ex.trans ex'.symm

theorem exists_obj_of_isGrpPullback (HD : GlobalTheory.Published.DualAbelianScheme) {F : Type} [Field F] [NumberField F]
    {𝔠 : FracId F} (X : Obj F 𝔠 (Sp ℂ)) (c₀ : 𝔠.elt) (hc₀ : IsTotPos (c₀ : F)) (A₀ : Over (Sp Qb)) [GrpObj A₀]
    (p : X.A.left ⟶ A₀.left) (hA₀ : IsAbelianScheme A₀) (gA₀ : SmoothOfRelativeDimension (Module.finrank ℚ F) A₀.hom)
    (hp : IsGrpPullback X.A A₀ (spMap (algebraMap Qb ℂ)) p) :
    ∃ (X₀ : Obj F 𝔠 (Sp Qb)) (p : X.A.left ⟶ X₀.A.left), X.IsPullBy X₀ (spMap (algebraMap Qb ℂ)) p := by
  haveI : Flat (spMap (algebraMap Qb ℂ)) := Flat.SpecMap_iff.2 (by
    letI := (algebraMap Qb ℂ).toAlgebra
    exact (inferInstance : Module.Flat Qb ℂ))
  haveI : Surjective (spMap (algebraMap Qb ℂ)) := ⟨fun x ↦ ⟨(inferInstance : Nonempty (PrimeSpectrum ℂ)).some,
    Subsingleton.elim (α := PrimeSpectrum Qb) _ _⟩⟩
  haveI := hA₀.comm
  obtain ⟨rm, hrm⟩ := ActDescent.exists_oAct hp X.rm fun a ↦ by
    obtain ⟨f, -, hf⟩ := GlobalTheory.T.homomorphism_descends_to_algebraic A₀ A₀ X.A X.A p p _ _ hA₀ gA₀ hA₀ gA₀ hp hp (X.rm.act a) (X.rm.hom a)
    exact ⟨f, hf⟩
  obtain ⟨D₀, _, Q, D, _, d, m, hD₀, gD₀, q₀, q₀', hd, m₁, m₂, q, q'⟩ := exists_dual_pair HD hA₀ gA₀ hp
  obtain ⟨l, l₁, l₂⟩ := exists_prod_pullback hp hp
  obtain ⟨H, hH, aH⟩ := exists_relAmple_prod X.ab X.ab (pull_isLB (X.isLB c₀) _) (X.pos c₀ hc₀)
    (pull_isLB (X.isLB c₀) _) (X.pos c₀ hc₀)
  have hx : ∀ c : 𝔠.elt, ∃ P₀ : LB (A₀ ⊗ A₀).left, ∃ h : P₀.IsLB, IsAdditive P₀ ∧ IsAdditive (swap P₀) ∧
      CechPic.pull l (cls P₀ h) = cls (X.P c) (X.isLB c) := fun c ↦ by
    obtain ⟨a₁, a₂⟩ := additive_of_triv X.ab X.ab hH aH (X.isLB c) (X.rig₁ c) (X.rig₂ c)
    obtain ⟨x, hx, ex⟩ := exists_hom q q' (X.isLB c) a₁ a₂
    obtain ⟨x₀, hx₀, e₀⟩ := GlobalTheory.T.homomorphism_descends_to_algebraic A₀ D₀ X.A D p d _ _ hA₀ gA₀ hD₀ gD₀ hp hd x hx
    obtain ⟨b₁, b₂⟩ := additive_ev q₀.isLB q₀.additive q₀'.additive x₀
    refine ⟨_, pull_isLB q₀.isLB _, b₁, b₂, ?_⟩
    rw [cls_ev q₀.isLB, ex]
    exact pull_evc_eq l₁ l₂ m₁ m₂ q₀.isLB q.isLB e₀.symm
  choose P₀ hP₀ a₁ a₂ eP using hx
  have inj : ∀ {P P' : LB (A₀ ⊗ A₀).left} (hP : P.IsLB) (hP' : P'.IsLB), IsAdditive P → IsAdditive P' →
      CechPic.pull l (cls P hP) = CechPic.pull l (cls P' hP') → LBIso P P' := fun hP hP' a a' e ↦
    (cls_eq_iff hP hP').1 (cls_eq_of_pull hp.1 hd l₁ l₂ m₁ m₂ q₀ q hP hP' a a' e)
  have iso : ∀ c, LBIso ((P₀ c).pull l) (X.P c) := fun c ↦
    (cls_eq_iff (pull_isLB (hP₀ c) _) (X.isLB c)).1 (by rw [cls_pull (hP₀ c)]; exact eP c)

  have val : ∀ (c : 𝔠.elt) {Y₀ : Over (Sp Qb)} {Y : Over (Sp ℂ)} (r : Y.left ⟶ Y₀.left) (a₀ t₀ : Y₀ ⟶ A₀)
      (a t : Y ⟶ X.A), a.left ≫ p = r ≫ a₀.left → t.left ≫ p = r ≫ t₀.left →
      CechPic.pull r (evc (hP₀ c) a₀ t₀) = evc (X.isLB c) a t := fun c Y₀ Y r a₀ t₀ a t ha ht ↦ by
    rw [evc, evc, ← eP, ← pull_comp, ← pull_comp]
    congr 2
    apply left_ext
    · rw [Category.assoc, Category.assoc, lift_left_fst, l₁, lift_left_fst_assoc, ha]
    · rw [Category.assoc, Category.assoc, lift_left_snd, l₂, lift_left_snd_assoc, ht]
  refine ⟨{ A := A₀
            ab := hA₀
            dim := gA₀
            rm := rm
            P := P₀
            isLB := hP₀
            rig₁ := fun c ↦ triv_left (hP₀ c) (a₁ c)
            rig₂ := fun c ↦ triv_right (hP₀ c) (a₂ c)
            symm := fun c ↦ ?_
            add := fun c c' ↦ ?_
            smul := fun a c ↦ ?_
            pos := fun c hc ↦ ?_
            ker := fun c T₀ x hx a ha ↦ ?_ }, p, hp, hrm, l, ⟨l₁, l₂⟩, fun c ↦ ?_⟩
  · refine inj (hP₀ c) (pull_isLB (hP₀ c) _) (a₁ c) (a₂ c) ?_
    rw [eP, cls_ev (hP₀ c), val c l _ _ _ _ l₂.symm l₁.symm]
    exact (cls_eq_iff _ (pull_isLB (X.isLB c) _)).2 (X.symm c)
  · have hq := LB.isLB_div (hP₀ (c + c')) (hP₀ c)
    have ev' : ∀ (Y : Over (Sp Qb)) (a t : Y ⟶ A₀), evc hq a t = evc (hP₀ (c + c')) a t - evc (hP₀ c) a t :=
      fun Y a t ↦ by rw [evc, cls_div (hP₀ (c + c')) (hP₀ c), map_sub]; rfl
    refine inj (hP₀ c') hq (a₁ c') ((isAdditive_iff hq).2 fun Y a a' t ↦ ?_) ?_
    · rw [ev', ev', ev', (isAdditive_iff (hP₀ _)).1 (a₁ _), (isAdditive_iff (hP₀ _)).1 (a₁ _)]
      abel
    · rw [cls_div (hP₀ (c + c')) (hP₀ c), map_sub, eP, eP, eP, ← cls_div (X.isLB (c + c')) (X.isLB c)
        (LB.isLB_div (X.isLB (c + c')) (X.isLB c))]
      exact (cls_eq_iff _ _).2 (X.add c c')
  · have hq : (ev (P₀ c) (fst A₀ A₀) (snd A₀ A₀ ≫ rm.act a)).IsLB := pull_isLB (hP₀ c) _
    refine inj (hP₀ _) hq (a₁ _) ((isAdditive_iff hq).2 fun Y u u' t ↦ ?_) ?_
    · simp only [evc_ev (hP₀ c), lift_fst, lift_snd_assoc]
      exact (isAdditive_iff (hP₀ c)).1 (a₁ c) _ _ _ _
    · rw [eP, cls_ev (hP₀ c), val c l _ _ (fst X.A X.A) (snd X.A X.A ≫ X.rm.act a) l₁.symm (by
        rw [Over.comp_left, Over.comp_left, Category.assoc, hrm, ← Category.assoc, ← Category.assoc, l₂])]
      exact (cls_eq_iff _ (pull_isLB (X.isLB c) _)).2 (X.smul a c)
  · refine AmpleDescent.relAmple_of_fieldExtension Qb ℂ _ A₀ X.A p _ _ hA₀ hp (pull_isLB (hP₀ c) _)
      (pull_isLB (X.isLB c) _) ((cls_eq_iff (pull_isLB (X.isLB c) _) (pull_isLB (pull_isLB (hP₀ c) _) _)).1 ?_)
      (X.pos c hc)
    rw [cls_pull (pull_isLB (hP₀ c) _), cls_ev (hP₀ c), cls_ev (X.isLB c)]
    exact (val c p _ _ _ _ (by simp) (by simp)).symm
  · let T : Over (Sp ℂ) := (Over.pullback (spMap (algebraMap Qb ℂ))).obj T₀
    let r : T.left ⟶ T₀.left := Limits.pullback.fst _ _
    have hr : IsPullback r T.hom T₀.hom (spMap (algebraMap Qb ℂ)) := IsPullback.of_hasPullback _ _
    have w : (r ≫ x.left) ≫ A₀.hom = T.hom ≫ spMap (algebraMap Qb ℂ) := by rw [Category.assoc, Over.w x, hr.w]
    let x' : T ⟶ X.A := liftPt hp T.hom _ w
    have ex : x'.left ≫ p = r ≫ x.left := liftPt_left hp _ _ w
    let u : Over.mk ((X.A ⊗ T).hom ≫ spMap (algebraMap Qb ℂ)) ⟶ T₀ := Over.homMk ((snd X.A T).left ≫ r) (by
      change ((snd X.A T).left ≫ r) ≫ T₀.hom = _
      rw [Category.assoc, hr.w, ← Category.assoc, Over.w]
      rfl)
    let s : (X.A ⊗ T).left ⟶ (A₀ ⊗ T₀).left := (lift (pushP hp (s := (X.A ⊗ T).hom) rfl (fst X.A T)) u).left
    have s₁ : s ≫ (fst A₀ T₀).left = (fst X.A T).left ≫ p := lift_left_fst _ _
    have s₂ : s ≫ (snd A₀ T₀).left = (snd X.A T).left ≫ r := lift_left_snd _ _
    have z : evc (X.isLB c) (fst X.A T) (snd X.A T ≫ x') = 0 := by
      rw [← val c s (fst A₀ T₀) (snd A₀ T₀ ≫ x) _ _ s₁.symm (by
        rw [Over.comp_left, Over.comp_left, Category.assoc, ex, ← Category.assoc, ← Category.assoc, s₂]),
        (triv_ev_iff (hP₀ c) _ _).1 hx, map_zero]
    have k := X.ker c T x' ((triv_ev_iff (X.isLB c) _ _).2 z) a ha
    refine ActDescent.over_hom_ext hr ?_
    rw [Over.comp_left, ← Category.assoc, ← ex, Category.assoc, ← hrm, ← Category.assoc, ← Over.comp_left, k]
    refine (one_left_comp hp (s := T.hom) rfl).trans ?_
    let r' : Over.mk (T.hom ≫ spMap (algebraMap Qb ℂ)) ⟶ T₀ := Over.homMk r hr.w
    exact congrArg (fun y ↦ y.left) (MonObj.comp_one (M := A₀) r').symm
  · exact (cls_eq_iff (X.isLB c) (pull_isLB (hP₀ c) _)).1 (by rw [cls_pull (hP₀ c)]; exact (eP c).symm)

theorem exists_model : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal →
  ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (io : K →+* ℂ), Module.finrank ℚ K = 2 → 0 < d → δ ^ 2 = -(d : K) →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
      IsCMType φ → (∀ i, (φ i).comp (algebraMap K E) = io) → ∀ (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ →
      ∀ (𝔠 : FracId (FR E)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ (lattice c y) 0 X),
      ∃ (X₀ : Obj (FR E) 𝔠 (Sp Qb)) (p : X.A.left ⟶ X₀.A.left), X.IsPullBy X₀ (spMap (algebraMap Qb ℂ)) p := by
  intro _ _ HD K _ _ d δ io h2 hd hδ E _ _ _ _ I _ φ hφ hio c y hc 𝔠 X U
  obtain ⟨C₀, _, C, _, p, L, u, s, hC₀, gC₀, hp, hL, hs, hu⟩ := GlobalTheory.T.elliptic_curve_lattice_period_form d (io δ) hd (by
    rw [← map_pow, hδ, map_neg, map_natCast])
  obtain ⟨B₀, _, B, _, q, M, v, hB₀, gB₀, hB, gB, hq, hv⟩ :=
    GlobalTheory.T.abelian_scheme_descent_with_uniformization Qb _ C₀ C p L u hC₀ gC₀ hp hL (Module.finrank ℚ (FR E))
  obtain ⟨T, hT, hTΛ⟩ := GlobalTheory.T.cm_period_matrix_exists K d δ io h2 hd hδ E I φ hφ hio c y hc U.e
  obtain ⟨ψ, hψ, eψ⟩ := GlobalTheory.T.lattice_map_gives_homomorphism B X.A _ hB X.ab gB X.dim M _ v U.u (s⁻¹ • T) fun z hz ↦ by
    obtain ⟨x, hx, ex⟩ := hTΛ (s⁻¹ • z) fun j ↦ by
      obtain ⟨a, b, e⟩ := hu _ (hv z hz j)
      exact ⟨a, b, by rw [Pi.smul_apply, e, smul_eq_mul, inv_mul_cancel_left₀ hs]⟩
    refine (U.lat _).2 ⟨x, hx, ?_⟩
    rw [LinearMap.smul_apply, ← map_smul, ex]
    funext j
    simp [GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord]
  obtain ⟨A₀, _, r, hA₀, gA₀, hr⟩ := GlobalTheory.T.quotient_abelian_scheme_descends B₀ B X.A q _ hB₀ gB₀ hq X.ab X.dim ψ hψ fun w ↦ by
    obtain ⟨z, rfl⟩ := U.u.ex_onto w
    obtain ⟨z', rfl⟩ := hT z
    refine ⟨v.ex (s • z'), ?_⟩
    rw [← eψ, LinearMap.smul_apply, map_smul, inv_smul_smul₀ hs]
  exact exists_obj_of_isGrpPullback HD.1 X U.c U.pos A₀ r hA₀ gA₀ hr

end GlobalTheory.CMModel
end
end
