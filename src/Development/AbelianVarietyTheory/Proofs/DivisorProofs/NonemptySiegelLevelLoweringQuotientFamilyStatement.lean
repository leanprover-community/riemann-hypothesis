import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothProjectiveStalkFactorial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCycAwayHomComplex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalSiegelObjectOddLevelRigid
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelObjectLoweredLevelStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothCommGroupSchemeEqOfPowEqOfClosedPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelObjectPullbackLevelPowerCalculusStatement
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQProjOverTargetGaloisCoverNoetherian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQProjOverOfRelAmpleOverQprojNoetherian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDescendsGaloisCoverNoetherianBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareBundleDescentGaloisCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegelObjectOfDescendedData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelObjectOfGaloisDescendedData
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothOfRelativeDimensionDescendsEtaleCover

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.SimilitudeLevel

theorem similitude_bij_mod (h N m : ℕ) (T : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] (Fin h ⊕ Fin h → ℤ)) (hN : 0 < N)
    (hm : m.Coprime N) (hT : ∀ x y, omegaStd (T x) (T y) ≡ m * omegaStd x y [ZMOD N]) :
    (∀ a, (∃ b, T a = N • b) ↔ ∃ b, a = N • b) ∧ ∀ a', ∃ a c, a' = T a + N • c := by
  classical
  haveI : NeZero N := ⟨hN.ne'⟩
  let red : (Fin h ⊕ Fin h → ℤ) → (Fin h ⊕ Fin h → ZMod N) := fun a i => (a i : ZMod N)
  have red_zero : ∀ a : Fin h ⊕ Fin h → ℤ, red a = 0 ↔ ∃ b, a = N • b := by
    intro a
    constructor
    · intro ha
      refine ⟨fun i => a i / N, funext fun i => ?_⟩
      have hd : (N : ℤ) ∣ a i := (ZMod.intCast_zmod_eq_zero_iff_dvd (a i) N).1 (congrFun ha i)
      simp only [Pi.smul_apply, nsmul_eq_mul]
      exact (Int.mul_ediv_cancel' hd).symm
    · rintro ⟨b, rfl⟩
      funext i
      simp [red]
  have omega_smul : ∀ (b y : Fin h ⊕ Fin h → ℤ), omegaStd (N • b) y = N * omegaStd b y := by
    intro b y
    simp only [omegaStd, Finset.mul_sum, Pi.smul_apply, nsmul_eq_mul]
    congr 1; ext i; ring
  have omega_inr : ∀ (a : Fin h ⊕ Fin h → ℤ) (i : Fin h), omegaStd a (Pi.single (Sum.inr i) 1) = a (Sum.inl i) := by
    intro a i; simp [omegaStd, Pi.single_apply]
  have omega_inl : ∀ (a : Fin h ⊕ Fin h → ℤ) (i : Fin h), omegaStd a (Pi.single (Sum.inl i) 1) = - a (Sum.inr i) := by
    intro a i; simp [omegaStd, Pi.single_apply]
  have hmN : IsCoprime (N : ℤ) m := Nat.isCoprime_iff_coprime.2 hm.symm
  have kerN : ∀ a, (∃ b, T a = N • b) → ∃ b, a = N • b := by
    rintro a ⟨b, hb⟩
    have hdiv : ∀ y, (N : ℤ) ∣ omegaStd a y := by
      intro y
      have h1 : (N : ℤ) ∣ omegaStd (T a) (T y) := by rw [hb, omega_smul]; exact dvd_mul_right _ _
      have h2 : (N : ℤ) ∣ m * omegaStd a y := by
        have := dvd_add (hT a y).dvd h1
        simpa using this
      exact hmN.dvd_of_dvd_mul_left h2
    rw [← red_zero]
    funext j
    rcases j with i | i
    · have := hdiv (Pi.single (Sum.inr i) 1)
      rw [omega_inr] at this
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).2 this
    · have := hdiv (Pi.single (Sum.inl i) 1)
      rw [omega_inl, dvd_neg] at this
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).2 this
  let M : Fin h ⊕ Fin h → Fin h ⊕ Fin h → ZMod N := fun j i => (T (Pi.single j 1) i : ZMod N)
  let TN : (Fin h ⊕ Fin h → ZMod N) → (Fin h ⊕ Fin h → ZMod N) := fun v i => ∑ j, v j * M j i
  have hT_sum : ∀ a : Fin h ⊕ Fin h → ℤ, T a = ∑ j, a j • T (Pi.single j 1) := by
    intro a
    conv_lhs => rw [← Finset.univ_sum_single a]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show Pi.single j (a j) = a j • (Pi.single j 1 : Fin h ⊕ Fin h → ℤ) by
      ext i; by_cases hi : i = j <;> simp [Pi.single_apply, hi], map_smul]
  have reduction_uniformizerPoint : ∀ a, red (T a) = TN (red a) := by
    intro a; funext i
    simp only [red, TN, M]
    rw [hT_sum a]
    simp [Finset.sum_apply]
  let lift : (Fin h ⊕ Fin h → ZMod N) → (Fin h ⊕ Fin h → ℤ) := fun v i => ((v i).val : ℤ)
  have red_lift : ∀ v, red (lift v) = v := fun v => funext fun i => by simp [red, lift]
  have TN_sub : ∀ v w, TN (v - w) = TN v - TN w := by
    intro v w; funext i; simp only [TN, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  have TN_inj : Function.Injective TN := by
    intro v w hvw
    have h0 : red (T (lift (v - w))) = 0 := by rw [reduction_uniformizerPoint, red_lift, TN_sub, hvw, sub_self]
    obtain ⟨b, hb⟩ := kerN _ ((red_zero _).1 h0)
    have := (red_zero _).2 ⟨b, hb⟩
    rw [red_lift] at this
    exact sub_eq_zero.1 this
  have TN_surj : Function.Surjective TN := Finite.injective_iff_surjective.1 TN_inj
  refine ⟨fun a => ⟨kerN a, fun ⟨b, hb⟩ => ⟨T b, by rw [hb, map_nsmul]⟩⟩, fun a' => ?_⟩
  obtain ⟨v, hv⟩ := TN_surj (red a')
  obtain ⟨c, hc⟩ := (red_zero (a' - T (lift v))).1 (by
    funext i
    have := congrFun (reduction_uniformizerPoint (lift v)) i
    rw [red_lift, hv] at this
    simp only [red, Pi.sub_apply, Int.cast_sub, Pi.zero_apply] at this ⊢
    rw [this, sub_self])
  exact ⟨lift v, c, by rw [← hc]; abel⟩

section Push

variable {S : Scheme.{0}} {G G' : Over S} [GrpObj G] [GrpObj G'] {φ : G'.left ⟶ G.left}

theorem exists_push (hp : IsGrpPullback G' G (𝟙 S) φ) (T : Over S) :
    ∃ ψ : (T ⟶ G') →* (T ⟶ G), ∀ p, (ψ p).left = p.left ≫ φ := by
  obtain ⟨ρ, hρ⟩ := GlobalTheory.SiegelDescent.exists_liftHom hp T T (𝟙 _) (by simp)
  have key : ∀ u, (ρ u).left ≫ φ = u.left := fun u => ((hρ u (ρ u)).1 rfl).trans (Category.id_comp _)
  have inj : Function.Injective ρ := fun u v e => Over.OverMorphism.ext ((key u).symm.trans (e ▸ key v))
  have surj : Function.Surjective ρ := fun p => ⟨Over.homMk (p.left ≫ φ) (by
      rw [Category.assoc, hp.1.w, Category.comp_id, Over.w]), (hρ _ p).2 (by simp)⟩
  let e := MulEquiv.ofBijective ρ ⟨inj, surj⟩
  refine ⟨e.symm.toMonoidHom, fun p => ?_⟩
  have h1 : ρ (e.symm p) = p := e.apply_symm_apply p
  have h2 := key (e.symm p)
  rw [h1] at h2
  exact h2.symm

end Push

theorem lev_zero {h N : ℕ} {B : Type} [CommRing B] {ζ : B} {S : Scheme.{0}} {s : S ⟶ Sp B}
    (C : SiegPre h N ζ s) : C.lev 0 = 1 := by
  have := C.lev_add 0 0
  rw [add_zero] at this
  exact mul_left_cancel (a := C.lev 0) (by rw [← this, _root_.mul_one])

theorem lev_nsmul {h N : ℕ} {B : Type} [CommRing B] {ζ : B} {S : Scheme.{0}} {s : S ⟶ Sp B}
    (C : SiegPre h N ζ s) (n : ℕ) (a : Fin h ⊕ Fin h → ℤ) : C.lev (n • a) = C.lev a ^ n := by
  induction n with
  | zero => rw [zero_smul, pow_zero, lev_zero]
  | succ n ih => rw [succ_nsmul, C.lev_add, ih, pow_succ]

theorem part_one (h N : ℕ) (B : Type) [CommRing B] (b : TBase B N) (hN : Odd N) (S : Scheme.{0}) (s : S ⟶ Sp B)
    (C : SiegPre h N (b.ζ : B) s) (T : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] (Fin h ⊕ Fin h → ℤ)) (m : ℕ) (hm : m.Coprime N)
    (hT : ∀ x y, omegaStd (T x) (T y) ≡ m * omegaStd x y [ZMOD N]) :
    ∃ (C' : SiegPre h N ((b.ζ : B) ^ m) s) (φ : C'.A.left ⟶ C.A.left) (φ₂ : (G2 C'.A).left ⟶ (G2 C.A).left),
      IsGrpPullback C'.A C.A (𝟙 S) φ ∧ IsSquare φ φ₂ ∧ LBIso C'.P (C.P.pull φ₂) ∧
        ∀ x, (C'.lev x).left ≫ φ = (C.lev (T x)).left := by
  obtain ⟨hinj, hsurj⟩ := similitude_bij_mod h N m T hN.pos hm hT
  have lev_mod : ∀ a c, C.lev (a + N • c) = C.lev a := by
    intro a c; rw [C.lev_add, lev_nsmul, C.lev_tors, _root_.mul_one]
  refine ⟨{ C with
      lev := fun a => C.lev (T a), lev_add := fun a c => (by rw [map_add]; exact C.lev_add _ _),
      lev_tors := fun a => C.lev_tors _, geom := ?_ }, 𝟙 _, 𝟙 _, ?_, ⟨by simp, by simp⟩,
      GlobalTheory.ThetaAffineGlue.lbIso_pull_id C.isLB, fun x => Category.comp_id _⟩
  · intro k _ _ x β z hx hz
    let z₀ : kˣ := Units.map β.toMonoidHom b.ζ
    have hzz : z = z₀ ^ m := Units.ext (by rw [hz, map_pow, Units.val_pow_eq_pow_val]; rfl)
    obtain ⟨ga, gb, gc⟩ := C.geom k x β z₀ hx rfl
    have hprim : IsPrimitiveRoot z₀ N := IsPrimitiveRoot.coe_units_iff.1 (b.prim k β)
    refine ⟨fun a => (ga (T a)).trans (hinj a), fun g hg => ?_, fun a c => ?_⟩
    · obtain ⟨a', ha'⟩ := gb g hg
      obtain ⟨a, c, rfl⟩ := hsurj a'
      exact ⟨a, by rw [← ha', lev_mod]⟩
    · have e : z ^ (2 * omegaStd a c) = z₀ ^ (2 * omegaStd (T a) (T c)) := by
        rw [hzz, ← zpow_natCast, ← zpow_mul, ← div_eq_one, div_eq_mul_inv, ← zpow_sub, hprim.zpow_eq_one_iff_dvd]
        obtain ⟨q, hq⟩ := (hT a c).dvd
        exact ⟨2 * q, by linear_combination 2 * hq⟩
      rw [e]
      exact gc (T a) (T c)
  · exact @isGrpPullback_of_iso _ _ _ _ _ (Iso.refl C.A) (inferInstanceAs (IsMonHom (𝟙 C.A)))

end GlobalTheory.SimilitudeLevel

namespace GlobalTheory.SimilitudeLevel

theorem part_two (h N : ℕ) (B : Type) [CommRing B] (b : TBase B N) (hN : Odd N)
    (R : Type) [CommRing R] [IsLocalRing R] (β : B →+* R) (m : ℕ) (β' : B →+* R)
    (C : SiegPre h N (b.ζ : B) (spMap β)) (C' : SiegPre h N (b.ζ : B) (spMap β'))
    (φ : C'.A.left ⟶ C.A.left) (φ₂ : (G2 C'.A).left ⟶ (G2 C.A).left) (hζ : β' (b.ζ : B) = β (b.ζ : B) ^ m)
    (hpb : IsGrpPullback C'.A C.A (𝟙 _) φ) (hsq : IsSquare φ φ₂) (hP : LBIso C'.P (C.P.pull φ₂)) :
    ∃ T : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] (Fin h ⊕ Fin h → ℤ), (∀ x y, omegaStd (T x) (T y) ≡ m * omegaStd x y [ZMOD N]) ∧
      ∀ x, (C'.lev x).left ≫ φ = (C.lev (T x)).left := by
  let K := AlgebraicClosure (IsLocalRing.ResidueField R)
  let jr : R →+* K := (algebraMap (IsLocalRing.ResidueField R) K).comp (IsLocalRing.residue R)
  let x : Sp K ⟶ Sp R := spMap jr
  have hx : ∀ g₀ : B →+* R, x ≫ spMap g₀ = spMap (jr.comp g₀) := fun g₀ => by
    simp only [x, spMap, ← Spec.map_comp]; rfl
  let Tx : Over (Sp R) := Over.mk x
  obtain ⟨ψ, hψ⟩ := exists_push hpb Tx
  let p : (Fin h ⊕ Fin h → ℤ) → (Tx ⟶ C'.A) := fun a => toUnit Tx ≫ C'.lev a
  have p_add : ∀ a c, p (a + c) = p a * p c := fun a c => by simp only [p, C'.lev_add, MonObj.comp_mul]
  let z : Kˣ := Units.map (jr.comp β).toMonoidHom b.ζ
  have gC := C.geom K x (jr.comp β) z (hx β) rfl
  have hprim : IsPrimitiveRoot z N := IsPrimitiveRoot.coe_units_iff.1 (b.prim K (jr.comp β))
  have hpN : ∀ a, ψ (p a) ^ N = 1 := fun a => by
    rw [← map_pow, show p a ^ N = 1 by rw [← MonObj.comp_pow, C'.lev_tors, MonObj.comp_one], map_one]
  choose a' ha' using fun i => gC.2.1 (ψ (p (Pi.single i 1))) (hpN _)
  let T : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] (Fin h ⊕ Fin h → ℤ) := (Pi.basisFun ℤ (Fin h ⊕ Fin h)).constr ℤ a'
  have hq : ∀ a, ψ (p a) = toUnit Tx ≫ C.lev (T a) := by
    let f₁ : (Fin h ⊕ Fin h → ℤ) →+ Additive (Tx ⟶ C.A) :=
      AddMonoidHom.mk' (fun a => Additive.ofMul (ψ (p a))) (fun a c => by rw [p_add, map_mul]; rfl)
    let f₂ : (Fin h ⊕ Fin h → ℤ) →+ Additive (Tx ⟶ C.A) :=
      AddMonoidHom.mk' (fun a => Additive.ofMul (toUnit Tx ≫ C.lev (T a)))
        (fun a c => by rw [map_add, C.lev_add, MonObj.comp_mul]; rfl)
    have hext : f₁ = f₂ := by
      refine AddMonoidHom.functions_ext _ _ _ fun i k => ?_
      rw [show (Pi.single i k : Fin h ⊕ Fin h → ℤ) = k • Pi.single i 1 by
        ext j; by_cases hj : j = i <;> simp [Pi.single_apply, hj], map_zsmul, map_zsmul]
      congr 1
      show Additive.ofMul (ψ (p (Pi.single i 1))) = Additive.ofMul (toUnit Tx ≫ C.lev (T (Pi.single i 1)))
      rw [← ha' i]
      congr 3
      have := (Pi.basisFun ℤ (Fin h ⊕ Fin h)).constr_basis ℤ a' i
      rw [Pi.basisFun_apply] at this
      exact this.symm
    intro a
    exact congrArg Additive.toMul (DFunLike.congr_fun hext a)
  have hdiag : LBIso C'.diag (C.diag.pull φ) :=
    GlobalTheory.SiegelDescent.lbIso_square C'.isLB C.isLB hP
      (GlobalTheory.SiegelDescent.lift_square (T := C'.A) (T₀ := C.A) (τ := φ) (a := 𝟙 _) (b := 𝟙 _) (a₀ := 𝟙 _)
        (b₀ := 𝟙 _) hsq (by simp) (by simp))
  let z' : Kˣ := Units.map (jr.comp β').toMonoidHom b.ζ
  have hzz : z' = z ^ m := Units.ext (by simp [z, z', hζ])
  have gC' := C'.geom K x (jr.comp β') z' (hx β') rfl
  refine ⟨T, fun a c => ?_, fun a => ?_⟩
  · have w1 := gC'.2.2 a c
    have w2 : Out.WeilIs C.A C.diag N (ψ (p a)) (ψ (p c)) (unitOn (z' ^ (2 * omegaStd a c))) := by
      have := (GlobalTheory.weilIs_grpPullback_of_comm' _ _ C.A C'.A (𝟙 _) φ C.diag C'.diag (pull_isLB C.isLB _)
        (pull_isLB C'.isLB _) hpb hdiag Tx N (p a) (p c) (Over.homMk (ψ (p a)).left (by simp))
        (Over.homMk (ψ (p c)).left (by simp)) _ (by simp [hψ]) (by simp [hψ])).1 w1
      exact GlobalTheory.SiegelDescent.weilIs_congr (by simp) _ _ _ _ _ _ rfl rfl _ this
    have w3 := gC.2.2 (T a) (T c)
    rw [← hq, ← hq] at w3
    have e := GlobalTheory.weilIs_unique_fieldPoint _ C.A C.diag (pull_isLB C.isLB _) K x N _ _ _ _ w2 w3
    rw [hzz, ← zpow_natCast, ← zpow_mul, ← div_eq_one, div_eq_mul_inv, ← zpow_sub, hprim.zpow_eq_one_iff_dvd] at e
    have h2 : IsCoprime (N : ℤ) 2 := by
      rw [Int.isCoprime_iff_gcd_eq_one]
      exact Nat.Coprime.symm (Nat.coprime_two_left.2 hN)
    have e' : (N : ℤ) ∣ 2 * (m * omegaStd a c - omegaStd (T a) (T c)) := by
      convert e using 1; ring
    exact Int.modEq_iff_dvd.2 (h2.dvd_of_dvd_mul_left e')
  · obtain ⟨ψ₀, hψ₀⟩ := exists_push hpb (𝟙_ (Over (Sp R)))
    have key := GlobalTheory.LocalRigid.eq_of_pow_eq_of_closedPoint (Sp R) C.A (@IsAbelianScheme.smooth _ _ _ C.ab) R (𝟙 _) N
      (by simpa using b.unit.map β) (ψ₀ (C'.lev a)) (C.lev (T a))
      (by rw [← map_pow, C'.lev_tors, C.lev_tors, map_one]) K jr inferInstance ?_
    · simpa [hψ₀] using congrArg (fun u => u.left) key
    · have := congrArg (fun u => u.left) (hq a)
      simp only [hψ, p, Over.comp_left] at this
      have ht : (toUnit Tx).left = x := (Category.comp_id _).symm.trans (Over.w (toUnit Tx))
      rw [ht] at this
      rw [hψ₀]
      exact this

end GlobalTheory.SimilitudeLevel

namespace GlobalTheory

theorem siegel_level_change_by_similitude : ∀ (h N : ℕ) (B : Type) [CommRing B] (b : TBase B N), Odd N → (∀ (S : Scheme.{0}) (s : S ⟶ Sp B) (C : SiegPre h N (b.ζ : B) s) (T : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] (Fin h ⊕ Fin h → ℤ)) (m : ℕ), m.Coprime N → (∀ x y, omegaStd (T x) (T y) ≡ m * omegaStd x y [ZMOD N]) → ∃ (C' : SiegPre h N ((b.ζ : B) ^ m) s) (φ : C'.A.left ⟶ C.A.left) (φ₂ : (G2 C'.A).left ⟶ (G2 C.A).left), IsGrpPullback C'.A C.A (𝟙 S) φ ∧ IsSquare φ φ₂ ∧ LBIso C'.P (C.P.pull φ₂) ∧ ∀ x, (C'.lev x).left ≫ φ = (C.lev (T x)).left) ∧ ∀ (R : Type) [CommRing R] [IsLocalRing R] (β : B →+* R) (m : ℕ) (β' : B →+* R) (C : SiegPre h N (b.ζ : B) (spMap β)) (C' : SiegPre h N (b.ζ : B) (spMap β')) (φ : C'.A.left ⟶ C.A.left) (φ₂ : (G2 C'.A).left ⟶ (G2 C.A).left), β' (b.ζ : B) = β (b.ζ : B) ^ m → IsGrpPullback C'.A C.A (𝟙 _) φ → IsSquare φ φ₂ → LBIso C'.P (C.P.pull φ₂) → ∃ T : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] (Fin h ⊕ Fin h → ℤ), (∀ x y, omegaStd (T x) (T y) ≡ m * omegaStd x y [ZMOD N]) ∧ ∀ x, (C'.lev x).left ≫ φ = (C.lev (T x)).left := by
  intro h N B _ b hN
  exact ⟨fun S s C T m hm hT => SimilitudeLevel.part_one h N B b hN S s C T m hm hT,
    fun R _ _ β m β' C C' φ φ₂ hζ hpb hsq hP => SimilitudeLevel.part_two h N B b hN R β m β' C C' φ φ₂ hζ hpb hsq hP⟩

end GlobalTheory
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_level_change_by_symplectic_similitude : ∀ (h N : ℕ) (B : Type) [CommRing B] (b : TBase B N), Odd N → (∀ (S : Scheme.{0}) (s : S ⟶ Sp B) (C : SiegPre h N (b.ζ : B) s) (T : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] (Fin h ⊕ Fin h → ℤ)) (m : ℕ), m.Coprime N → (∀ x y, omegaStd (T x) (T y) ≡ m * omegaStd x y [ZMOD N]) → ∃ (C' : SiegPre h N ((b.ζ : B) ^ m) s) (φ : C'.A.left ⟶ C.A.left) (φ₂ : (G2 C'.A).left ⟶ (G2 C.A).left), IsGrpPullback C'.A C.A (𝟙 S) φ ∧ IsSquare φ φ₂ ∧ LBIso C'.P (C.P.pull φ₂) ∧ ∀ x, (C'.lev x).left ≫ φ = (C.lev (T x)).left) ∧ ∀ (R : Type) [CommRing R] [IsLocalRing R] (β : B →+* R) (m : ℕ) (β' : B →+* R) (C : SiegPre h N (b.ζ : B) (spMap β)) (C' : SiegPre h N (b.ζ : B) (spMap β')) (φ : C'.A.left ⟶ C.A.left) (φ₂ : (G2 C'.A).left ⟶ (G2 C.A).left), β' (b.ζ : B) = β (b.ζ : B) ^ m → IsGrpPullback C'.A C.A (𝟙 _) φ → IsSquare φ φ₂ → LBIso C'.P (C.P.pull φ₂) → ∃ T : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] (Fin h ⊕ Fin h → ℤ), (∀ x y, omegaStd (T x) (T y) ≡ m * omegaStd x y [ZMOD N]) ∧ ∀ x, (C'.lev x).left ≫ φ = (C.lev (T x)).left := by
  atlas_forward_decl GlobalTheory.siegel_level_change_by_similitude
end

section
section
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SympModN

theorem omegaStd_nsmul_left {h : ℕ} (N : ℕ) (a b : Fin h ⊕ Fin h → ℤ) :
    omegaStd (N • a) b = N * omegaStd a b := by
  unfold omegaStd
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, nsmul_eq_mul]
  ring

theorem omegaStd_single_inr {h : ℕ} (a : Fin h ⊕ Fin h → ℤ) (i : Fin h) :
    omegaStd a (Pi.single (.inr i) 1) = a (.inl i) := by
  simp [omegaStd, Pi.single_apply]

theorem omegaStd_single_inl {h : ℕ} (a : Fin h ⊕ Fin h → ℤ) (i : Fin h) :
    omegaStd a (Pi.single (.inl i) 1) = -a (.inr i) := by
  simp [omegaStd, Pi.single_apply]

theorem omegaStd_add_nsmul_modEq {h : ℕ} (N : ℕ) (x y b c : Fin h ⊕ Fin h → ℤ) :
    omegaStd (x + N • b) (y + N • c) ≡ omegaStd x y [ZMOD N] := by
  rw [Int.modEq_iff_dvd]
  unfold omegaStd
  rw [← Finset.sum_sub_distrib]
  refine Finset.dvd_sum fun i _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply]
  exact ⟨-(b (.inl i) * y (.inr i) + x (.inl i) * c (.inr i) + N * b (.inl i) * c (.inr i)) +
    (b (.inr i) * y (.inl i) + x (.inr i) * c (.inl i) + N * b (.inr i) * c (.inl i)), by ring⟩

theorem exists_eq_nsmul_iff {ι : Type*} (N : ℕ) (hN : N ≠ 0) (a : ι → ℤ) :
    (∃ b, a = N • b) ↔ ∀ j, (N : ℤ) ∣ a j := by
  constructor
  · rintro ⟨b, rfl⟩ j
    simp [nsmul_eq_mul]
  · intro hd
    refine ⟨fun j => a j / N, funext fun j => ?_⟩
    simp [nsmul_eq_mul, Int.mul_ediv_cancel' (hd j)]

theorem symplecticSimilitude_modN : ∀ (h N m : ℕ) (T : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] (Fin h ⊕ Fin h → ℤ)), N ≠ 0 →
    m.Coprime N → (∀ x y, omegaStd (T x) (T y) ≡ m * omegaStd x y [ZMOD N]) →
    (∀ a, (∃ b, T a = N • b) → ∃ b, a = N • b) ∧ (∀ a, ∃ a' b, T a' = a + N • b) ∧
    ∃ T' : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] (Fin h ⊕ Fin h → ℤ), (∀ x, ∃ b, T (T' x) = x + N • b) ∧
      ∀ m' : ℕ, m * m' ≡ 1 [MOD N] → ∀ x y, omegaStd (T' x) (T' y) ≡ m' * omegaStd x y [ZMOD N] := by
  intro h N m T hN hm hT
  have h1 : ∀ a, (∃ b, T a = N • b) → ∃ b, a = N • b := by
    rintro a ⟨b, hb⟩
    have hd : ∀ y, (N : ℤ) ∣ omegaStd a y := by
      intro y
      have e := hT a y
      rw [hb, omegaStd_nsmul_left] at e
      have hdm : (N : ℤ) ∣ (m : ℤ) * omegaStd a y := by
        have h3 := Int.modEq_iff_dvd.1 e
        have h2 : (N : ℤ) ∣ (N : ℤ) * omegaStd b (T y) := dvd_mul_right _ _
        simpa using dvd_add h3 h2
      exact (Nat.isCoprime_iff_coprime.2 hm.symm).dvd_of_dvd_mul_left hdm
    refine (exists_eq_nsmul_iff N hN a).2 fun j => ?_
    rcases j with i | i
    · simpa [omegaStd_single_inr] using hd (Pi.single (.inr i) 1)
    · simpa [omegaStd_single_inl] using hd (Pi.single (.inl i) 1)
  haveI : NeZero N := ⟨hN⟩
  let red : (Fin h ⊕ Fin h → ℤ) → (Fin h ⊕ Fin h → ZMod N) := fun a j => (a j : ZMod N)
  let lift : (Fin h ⊕ Fin h → ZMod N) → (Fin h ⊕ Fin h → ℤ) := fun v j => ((v j).val : ℤ)
  have hred0 : ∀ a, red a = 0 ↔ ∃ b, a = N • b := by
    intro a
    rw [exists_eq_nsmul_iff N hN a, funext_iff]
    exact forall_congr' fun j => ZMod.intCast_zmod_eq_zero_iff_dvd _ _
  have hredlift : ∀ v, red (lift v) = v := by
    intro v; funext j; simp [red, lift]
  have hred_sub : ∀ a a', red (a - a') = red a - red a' := by
    intro a a'; funext j; simp [red]
  have finj : Function.Injective fun v => red (T (lift v)) := by
    intro v w hvw
    have e : red (T (lift v - lift w)) = 0 := by
      rw [map_sub, hred_sub]; exact sub_eq_zero.2 hvw
    obtain ⟨b', hb'⟩ := h1 _ ((hred0 _).1 e)
    have e2 : red (lift v - lift w) = 0 := (hred0 _).2 ⟨b', hb'⟩
    rw [hred_sub, hredlift, hredlift] at e2
    exact sub_eq_zero.1 e2
  have fsurj := Finite.injective_iff_surjective.1 finj
  have h2 : ∀ a, ∃ a' b, T a' = a + N • b := by
    intro a
    obtain ⟨v, hv⟩ := fsurj (red a)
    have e : red (T (lift v) - a) = 0 := by
      rw [hred_sub]; exact sub_eq_zero.2 hv
    obtain ⟨b, hb⟩ := (hred0 _).1 e
    exact ⟨lift v, b, by rw [← hb]; abel⟩
  choose v b hvb using fun i : Fin h ⊕ Fin h => h2 (Pi.single i 1)
  let T' : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] (Fin h ⊕ Fin h → ℤ) :=
    ∑ i, (LinearMap.proj i : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] ℤ).smulRight (v i)
  have hT' : ∀ x, T' x = ∑ i, x i • v i := by
    intro x; simp [T']
  have h3 : ∀ x, T (T' x) = x + N • ∑ i, x i • b i := by
    intro x
    rw [hT', map_sum]
    simp only [map_zsmul, hvb, smul_add, Finset.sum_add_distrib]
    congr 1
    · funext j
      simp [Finset.sum_apply, Pi.single_apply]
    · rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
  refine ⟨h1, h2, T', fun x => ⟨_, h3 x⟩, ?_⟩
  intro m' hmm' x y
  have e1 := hT (T' x) (T' y)
  rw [h3, h3] at e1
  have e2 := omegaStd_add_nsmul_modEq N x y (∑ i, x i • b i) (∑ i, y i • b i)
  have e3 : (m : ℤ) * omegaStd (T' x) (T' y) ≡ omegaStd x y [ZMOD N] := e1.symm.trans e2
  have hmm'' : (m : ℤ) * m' ≡ 1 [ZMOD N] := by
    unfold Nat.ModEq at hmm'
    unfold Int.ModEq
    exact_mod_cast hmm'
  calc omegaStd (T' x) (T' y) = 1 * omegaStd (T' x) (T' y) := by ring
    _ ≡ ((m : ℤ) * m') * omegaStd (T' x) (T' y) [ZMOD N] := Int.ModEq.mul_right _ hmm''.symm
    _ = m' * ((m : ℤ) * omegaStd (T' x) (T' y)) := by ring
    _ ≡ m' * omegaStd x y [ZMOD N] := Int.ModEq.mul_left _ e3

end GlobalTheory.SympModN
end

open ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symplecticSimilitude_invertible_modN : ∀ (h N m : ℕ) (T : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] (Fin h ⊕ Fin h → ℤ)), N ≠ 0 → m.Coprime N → (∀ x y, omegaStd (T x) (T y) ≡ m * omegaStd x y [ZMOD N]) → (∀ a, (∃ b, T a = N • b) → ∃ b, a = N • b) ∧ (∀ a, ∃ a' b, T a' = a + N • b) ∧ ∃ T' : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] (Fin h ⊕ Fin h → ℤ), (∀ x, ∃ b, T (T' x) = x + N • b) ∧ ∀ m' : ℕ, m * m' ≡ 1 [MOD N] → ∀ x y, omegaStd (T' x) (T' y) ≡ m' * omegaStd x y [ZMOD N] := by
  atlas_forward_decl GlobalTheory.SympModN.symplecticSimilitude_modN
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.SiegAct

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem spMap_inj {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem spMap_id' (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 (Sp A) := Spec.map_id _

theorem exists_spMap {k B : Type} [CommRing k] [CommRing B] (x : Sp k ⟶ Sp B) : ∃ β : B →+* k, x = spMap β :=
  ⟨(Spec.preimage x).hom, by rw [spMap, CommRingCat.ofHom_hom, Spec.map_preimage]⟩

theorem unit_left' {S T : Scheme.{0}} {G : Over S} (x : T ⟶ S) (σ : 𝟙_ (Over S) ⟶ G) :
    (toUnit (Over.mk x) ≫ σ).left = x ≫ σ.left := by
  simp

variable {h N m : ℕ} {B B' : Type} [CommRing B] [CommRing B'] {ζ : B} {ζ' : B'} {S : Scheme.{0}} {s : S ⟶ Sp B}

theorem lev_zero (C : SiegPre h N ζ s) : C.lev 0 = 1 := by
  have := C.lev_add 0 0
  rw [add_zero] at this
  exact left_eq_mul.1 this

theorem lev_nsmul (C : SiegPre h N ζ s) (k : ℕ) (a : Fin h ⊕ Fin h → ℤ) : C.lev (k • a) = C.lev a ^ k := by
  induction k with
  | zero => rw [zero_smul, pow_zero, lev_zero]
  | succ k ih => rw [succ_nsmul, C.lev_add, ih, pow_succ]

theorem lev_N_smul (C : SiegPre h N ζ s) (a : Fin h ⊕ Fin h → ℤ) : C.lev (N • a) = 1 := by
  rw [lev_nsmul, C.lev_tors]

def relabel (C : SiegPre h N ζ s) (T : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] (Fin h ⊕ Fin h → ℤ)) (σ : B' →+* B)
    (hN : N ≠ 0) (hζ : ζ ^ N = 1) (hσ : σ ζ' = ζ ^ m)
    (hω : ∀ x y, omegaStd (T x) (T y) ≡ m * omegaStd x y [ZMOD N])
    (hinj : ∀ a, (∃ b, T a = N • b) → ∃ b, a = N • b)
    (hsurj : ∀ a, ∃ a' b, T a' = a + N • b) : SiegPre h N ζ' (s ≫ spMap σ) where
  A := C.A
  ab := C.ab
  P := C.P
  isLB := C.isLB
  rig₁ := C.rig₁
  rig₂ := C.rig₂
  symm := C.symm
  lev x := C.lev (T x)
  lev_add a b := by rw [map_add, C.lev_add]
  lev_tors a := C.lev_tors _
  geom k _ _ x β z hx hz := by
    obtain ⟨β₀, hβ₀⟩ := exists_spMap (x ≫ s)
    have hb : β = β₀.comp σ := spMap_inj (by rw [← hx, ← Category.assoc, hβ₀, spMap_comp'])
    have h1 : β₀ ζ ^ N = 1 := by rw [← map_pow, hζ, map_one]
    let z₀ : kˣ := Units.ofPowEqOne (β₀ ζ) N h1 hN
    obtain ⟨g1, g2, g3⟩ := C.geom k x β₀ z₀ hβ₀ rfl
    have hzm : z = z₀ ^ m := Units.ext (by
      rw [hz, hb, RingHom.comp_apply, hσ, map_pow, Units.val_pow_eq_pow_val]; rfl)
    have hz₀ : z₀ ^ N = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val]; exact h1)
    refine ⟨fun a => (g1 (T a)).trans ⟨hinj a, fun ⟨b, hb⟩ => ⟨T b, by rw [hb, map_nsmul]⟩⟩, fun g hg => ?_,
      fun a b => ?_⟩
    · obtain ⟨a, ha⟩ := g2 g hg
      obtain ⟨a', b, hab⟩ := hsurj a
      refine ⟨a', ?_⟩
      show toUnit _ ≫ C.lev (T a') = g
      rw [hab, C.lev_add, MonObj.comp_mul, lev_N_smul, MonObj.comp_one, _root_.mul_one, ha]
    · have e : z₀ ^ (2 * omegaStd (T a) (T b)) = z ^ (2 * omegaStd a b) := by
        rw [hzm, ← zpow_natCast, ← zpow_mul]
        refine zpow_eq_zpow_iff_modEq.2 (Int.ModEq.of_dvd (Int.natCast_dvd_natCast.2 (orderOf_dvd_of_pow_eq_one hz₀)) ?_)
        have := (hω a b).mul_left 2
        calc 2 * omegaStd (T a) (T b) ≡ 2 * (m * omegaStd a b) [ZMOD N] := this
          _ = m * (2 * omegaStd a b) := by ring
      have := g3 (T a) (T b)
      rw [e] at this
      exact this

section Calc

open GlobalTheory.SiegelPullComp GlobalTheory.SiegelPull

variable {h n n' n'' : ℕ} {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B''] {ζ : B} {ζ' : B'} {ζ'' : B''}
  {S S' S'' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'} {s'' : S'' ⟶ Sp B''}
  {c : SiegPre h n ζ s} {c' : SiegPre h n' ζ' s'} {c'' : SiegPre h n'' ζ'' s''} {f : S' ⟶ S} {f' : S'' ⟶ S'}
  {d d' d'' : ℕ}

def Sq (c' : SiegPre h n' ζ' s') (c : SiegPre h n ζ s) (φ : c'.A.left ⟶ c.A.left) : Prop :=
  ∃ φ₂ : (G2 c'.A).left ⟶ (G2 c.A).left, IsSquare φ φ₂ ∧ LBIso c'.P (c.P.pull φ₂)

theorem Sq.comp {φ : c'.A.left ⟶ c.A.left} {ψ : c''.A.left ⟶ c'.A.left} (m : Sq c' c φ) (m' : Sq c'' c' ψ) :
    Sq c'' c (ψ ≫ φ) := by
  obtain ⟨φ₂, hs, hw⟩ := m
  obtain ⟨ψ₂, hs', hw'⟩ := m'
  refine ⟨ψ₂ ≫ φ₂, ⟨?_, ?_⟩, ?_⟩
  · rw [Category.assoc, hs.1, ← Category.assoc, hs'.1, Category.assoc]
  · rw [Category.assoc, hs.2, ← Category.assoc, hs'.2, Category.assoc]
  · exact (hw'.trans c''.isLB (pull_isLB c'.isLB _) (pull_isLB (pull_isLB c.isLB _) _) (iso_pull ψ₂ hw)).trans
      c''.isLB (pull_isLB (pull_isLB c.isLB _) _) (pull_isLB c.isLB _) (iso_pull_pull c.isLB φ₂ ψ₂)

theorem sRelBy_comp {φ : c'.A.left ⟶ c.A.left} {ψ : c''.A.left ⟶ c'.A.left} (m : SRelBy c' c d' d f φ)
    (m' : SRelBy c'' c' d'' d' f' ψ) : SRelBy c'' c d'' d (f' ≫ f) (ψ ≫ φ) := by
  obtain ⟨hφ, hs, hl⟩ := m
  obtain ⟨hψ, hs', hl'⟩ := m'
  refine ⟨hψ.comp hφ, Sq.comp (c := c) (c' := c') (c'' := c'') hs hs', fun a => ?_⟩
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ φ) (hl' a)).trans ((Category.assoc _ _ _).trans
      ((congrArg (f' ≫ ·) (hl a)).trans (Category.assoc _ _ _).symm)))

theorem pow_section {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {φ : A'.left ⟶ A.left}
    (hφ : IsGrpPullback A' A f φ) (x' : 𝟙_ (Over S') ⟶ A') (x : 𝟙_ (Over S) ⟶ A)
    (e : x'.left ≫ φ = f ≫ x.left) (k : ℕ) : (x' ^ k).left ≫ φ = f ≫ (x ^ k).left := by
  have e₁ : x' = SiegelPull.secPull hφ x := by
    refine push_injective hφ _ (Over.OverMorphism.ext ?_)
    exact e.trans (SiegelPull.secPull_left hφ x).symm
  have e₂ : x' ^ k = SiegelPull.secPull hφ (x ^ k) := push_injective hφ _ (by
    rw [map_pow, e₁, push_secPull', push_secPull', MonObj.comp_pow])
  rw [e₂, SiegelPull.secPull_left]

end Calc

section Twist

variable {h n N : ℕ}

structure Twist (F : SFam h N (zetaAway N)) (j : cycAway n →+* cycAway N)
    (T : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] (Fin h ⊕ Fin h → ℤ)) (m : ℕ) (σ : cycAway N →+* cycAway N) (f : F.X ⟶ F.X) :
    Prop where
  cop : m.Coprime N
  root : σ (zetaAway N) = zetaAway N ^ m
  fix : σ.comp j = j
  symp : ∀ x y, omegaStd (T x) (T y) ≡ m * omegaStd x y [ZMOD N]
  low : ∀ x, F.univ.lev (T x) ^ (N / n) = F.univ.lev x ^ (N / n)
  comm : f ≫ F.s = F.s ≫ spMap σ
  map : ∃ ν : F.univ.A.left ⟶ F.univ.A.left, IsGrpPullback F.univ.A F.univ.A f ν ∧ Sq F.univ F.univ ν ∧
    ∀ x, (F.univ.lev (T x)).left ≫ ν = f ≫ (F.univ.lev x).left

end Twist

end GlobalTheory.SiegAct
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.SiegAct

variable {h n N : ℕ} {F : SFam h N (zetaAway N)} {j : cycAway n →+* cycAway N}

theorem zeta_pow (hN : N ≠ 0) : zetaAway N ^ N = 1 :=
  Subtype.ext (Complex.isPrimitiveRoot_exp N hN).pow_eq_one

theorem twist_one : Twist F j LinearMap.id 1 (RingHom.id _) (𝟙 _) where
  cop := Nat.coprime_one_left N
  root := (pow_one _).symm
  fix := RingHom.id_comp j
  symp x y := by simp [Int.ModEq]
  low x := rfl
  comm := by rw [spMap_id', Category.id_comp, Category.comp_id]
  map := by
    obtain ⟨φ, φ₂, a, b, c, d⟩ := GlobalTheory.SiegelPullComp.pb_id F.univ
    exact ⟨φ, a, ⟨φ₂, b, c⟩, d⟩

theorem Twist.mul {T T' : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] (Fin h ⊕ Fin h → ℤ)} {m m' : ℕ}
    {σ σ' : cycAway N →+* cycAway N} {f f' : F.X ⟶ F.X} (t : Twist F j T m σ f) (t' : Twist F j T' m' σ' f') :
    Twist F j (T ∘ₗ T') (m * m') (σ.comp σ') (f ≫ f') where
  cop := Nat.Coprime.mul t.cop t'.cop
  root := by rw [RingHom.comp_apply, t'.root, map_pow, t.root, ← pow_mul, mul_comm]
  fix := by rw [RingHom.comp_assoc, t'.fix, t.fix]
  symp x y := by
    have h1 := t.symp (T' x) (T' y)
    have h2 := (t'.symp x y).mul_left m
    simp only [LinearMap.comp_apply]
    calc _ ≡ m * omegaStd (T' x) (T' y) [ZMOD N] := h1
      _ ≡ m * (m' * omegaStd x y) [ZMOD N] := h2
      _ = ((m * m' : ℕ) : ℤ) * omegaStd x y := by push_cast; ring
  low x := by simp only [LinearMap.comp_apply]; rw [t.low, t'.low]
  comm := by rw [Category.assoc, t'.comm, ← Category.assoc, t.comm, Category.assoc, spMap_comp']
  map := by
    obtain ⟨ν, a, b, c⟩ := t.map
    obtain ⟨ν', a', b', c'⟩ := t'.map
    refine ⟨ν ≫ ν', a.comp a', Sq.comp b' b, fun x => ?_⟩
    simp only [LinearMap.comp_apply]
    rw [← Category.assoc, c, Category.assoc, c', ← Category.assoc]

theorem Twist.siegPB {T : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] (Fin h ⊕ Fin h → ℤ)} {m : ℕ} {σ : cycAway N →+* cycAway N}
    {f : F.X ⟶ F.X} (t : Twist F j T m σ f) (hN : N ≠ 0) (hinj : ∀ a, (∃ b, T a = N • b) → ∃ b, a = N • b)
    (hsurj : ∀ a, ∃ a' b, T a' = a + N • b) :
    SiegPB (relabel F.univ T σ hN (zeta_pow hN) t.root t.symp hinj hsurj) F.univ f := by
  obtain ⟨ν, a, ⟨ν₂, b, c⟩, d⟩ := t.map
  exact ⟨ν, ν₂, a, b, c, d⟩

theorem exists_twist (hN : N ≠ 0) {T : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] (Fin h ⊕ Fin h → ℤ)} {m : ℕ}
    {σ : cycAway N →+* cycAway N} (hσi : Function.Injective σ) (cop : m.Coprime N)
    (root : σ (zetaAway N) = zetaAway N ^ m) (fix : σ.comp j = j)
    (symp : ∀ x y, omegaStd (T x) (T y) ≡ m * omegaStd x y [ZMOD N])
    (low : ∀ x, F.univ.lev (T x) ^ (N / n) = F.univ.lev x ^ (N / n)) : ∃ f, Twist F j T m σ f := by
  obtain ⟨hinj, hsurj, -⟩ := GlobalTheory.T.symplecticSimilitude_invertible_modN h N m T hN cop symp
  obtain ⟨hr, hd⟩ := F.isReduced_and_dense
  obtain ⟨f, hf, H⟩ := F.rep F.X (F.s ≫ spMap σ) (relabel F.univ T σ hN (zeta_pow hN) root symp hinj hsurj) hr
    (hd.mono fun x hx => by
      have hx' : (F.s x).asIdeal = ⊥ := hx
      show ((F.s ≫ spMap σ) x).asIdeal = ⊥
      rw [Scheme.Hom.comp_apply]
      change ((F.s x).asIdeal).comap σ = ⊥
      rw [hx']
      exact Ideal.comap_bot_of_injective σ hσi) F.princ
  obtain ⟨ν, ν₂, a, b, c, d⟩ := H
  exact ⟨f, cop, root, fix, symp, low, hf, ν, a, ⟨ν₂, b, c⟩, d⟩

theorem Twist.unique (hN : N ≠ 0) {T T' : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] (Fin h ⊕ Fin h → ℤ)} {m m' : ℕ}
    {σ σ' : cycAway N →+* cycAway N} {f f' : F.X ⟶ F.X} (t : Twist F j T m σ f) (t' : Twist F j T' m' σ' f')
    (hσ : σ = σ') (hT : ∀ x, F.univ.lev (T x) = F.univ.lev (T' x)) : f = f' := by
  obtain ⟨hinj, hsurj, -⟩ := GlobalTheory.T.symplecticSimilitude_invertible_modN h N m T hN t.cop t.symp
  refine F.hom_ext (relabel F.univ T σ hN (zeta_pow hN) t.root t.symp hinj hsurj) f f' (by rw [t.comm, t'.comm, hσ])
    (t.siegPB hN hinj hsurj) ?_
  obtain ⟨ν, a, ⟨ν₂, b, c⟩, d⟩ := t'.map
  exact ⟨ν, ν₂, a, b, c, fun x => (congrArg (fun z => z.left ≫ ν) (hT x)).trans (d x)⟩

theorem Twist.sRelBy {T : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] (Fin h ⊕ Fin h → ℤ)} {m : ℕ} {σ : cycAway N →+* cycAway N}
    {f : F.X ⟶ F.X} {ν : F.univ.A.left ⟶ F.univ.A.left} (t : Twist F j T m σ f)
    (a : IsGrpPullback F.univ.A F.univ.A f ν) (b : Sq F.univ F.univ ν)
    (c : ∀ x, (F.univ.lev (T x)).left ≫ ν = f ≫ (F.univ.lev x).left) :
    SRelBy F.univ F.univ (N / n) (N / n) f ν :=
  ⟨a, b, fun x => by
    have := pow_section a _ _ (c x) (N / n)
    rw [t.low x] at this
    exact this⟩

theorem rig (hn : 3 ≤ n) (hN : Odd N) (hnN : n ∣ N) (hj : j (zetaAway n) = zetaAway N ^ (N / n))
    {n' : ℕ} {B' : Type} [CommRing B'] {ζ' : B'} {S' : Scheme.{0}} {s' : S' ⟶ Sp B'} (c' : SiegPre h n' ζ' s')
    (g : S' ⟶ F.X) (φ φ' : c'.A.left ⟶ F.univ.A.left) (hφ : SRelBy c' F.univ (N / n) (N / n) g φ)
    (hφ' : SRelBy c' F.univ (N / n) (N / n) g φ') : φ = φ' := by
  have hN0 : N ≠ 0 := hN.pos.ne'
  have hn0 : n ≠ 0 := by omega
  obtain ⟨c₀, hC0, h0C⟩ := GlobalTheory.T.exists_siegelObject_lowered_level h n N (cycAway n) (cycAway N) (zetaAway n) (zetaAway N) j F.X F.s F.univ
    hN0 (isUnit_natCast hN0) hnN hj
  have hc₀ : c₀.Principal := (GlobalTheory.T.siegelObjectPullbackLevelPower_calculus h N n n (cycAway N) (cycAway n) (cycAway n) (zetaAway N) (zetaAway n)
    (zetaAway n) F.X F.X F.X F.s (F.s ≫ spMap j) (F.s ≫ spMap j) F.univ c₀ c₀ (𝟙 _) (𝟙 _) (N / n) 1 1 h0C).2.1 F.princ
  obtain ⟨ψ, hψ⟩ := hC0
  have e₁ := sRelBy_comp hψ hφ
  have e₂ := sRelBy_comp hψ hφ'
  have := GlobalTheory.SiegRigid.eq_of_sRelBy h n n' (N / n) (cycAway n) B' (cycBase hn0) ζ' F.X S' (F.s ≫ spMap j) s' c₀ c'
    (g ≫ 𝟙 _) (φ ≫ ψ) (φ' ≫ ψ) hn (hN.of_dvd_nat hnN) hc₀ e₁ e₂
  refine hψ.1.1.hom_ext this ?_
  rw [hφ.1.1.w, hφ'.1.1.w]

end GlobalTheory.SiegAct

namespace GlobalTheory.SiegAct

section Calc2

variable {h n n' n'' : ℕ} {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B''] {ζ : B} {ζ' : B'} {ζ'' : B''}
  {S S' S'' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'} {s'' : S'' ⟶ Sp B''}
  {c : SiegPre h n ζ s} {c' : SiegPre h n' ζ' s'} {c'' : SiegPre h n'' ζ'' s''} {f : S' ⟶ S} {f' : S'' ⟶ S'}
  {d d' d'' : ℕ}

theorem sRel_comp (h₁ : SRel c' c d' d f) (h₂ : SRel c'' c' d'' d' f') : SRel c'' c d'' d (f' ≫ f) :=
  ((GlobalTheory.T.siegelObjectPullbackLevelPower_calculus h n n' n'' B B' B'' ζ ζ' ζ'' S S' S'' s s' s'' c c' c'' f f' d d' d'' h₁).1).1 h₂

theorem sRel_cancel (h₁ : SRel c' c d' d f) (h₂ : SRel c'' c d'' d (f' ≫ f)) : SRel c'' c' d'' d' f' :=
  ((GlobalTheory.T.siegelObjectPullbackLevelPower_calculus h n n' n'' B B' B'' ζ ζ' ζ'' S S' S'' s s' s'' c c' c'' f f' d d' d'' h₁).1).2 h₂

theorem sRel_scale (h₁ : SRel c' c 1 1 f) (e : ℕ) : SRel c' c e e f := by
  simpa using (GlobalTheory.T.siegelObjectPullbackLevelPower_calculus h n n' n' B B' B' ζ ζ' ζ' S S' S' s s' s' c c' c' f (𝟙 S') 1 1 1 h₁).2.2 e

end Calc2

variable {h n N : ℕ} {F : SFam h N (zetaAway N)} {j : cycAway n →+* cycAway N}

theorem zeta_pow_congr (hN : N ≠ 0) {K : Type} [Field K] (β : cycAway N →+* K) {a b : ℕ}
    (e : β (zetaAway N) ^ a = β (zetaAway N) ^ b) : zetaAway N ^ a = zetaAway N ^ b := by
  have hp := isPrimitiveRoot_map hN β
  have hpos : 0 < N := Nat.pos_of_ne_zero hN
  rw [pow_eq_pow_mod a hp.pow_eq_one, pow_eq_pow_mod b hp.pow_eq_one] at e
  rw [pow_eq_pow_mod a (zeta_pow hN), pow_eq_pow_mod b (zeta_pow hN),
    hp.pow_inj (Nat.mod_lt _ hpos) (Nat.mod_lt _ hpos) e]

theorem exists_eq_nsmul_of_pull (hN : N ≠ 0) {R : Type} [CommRing R] [IsLocalRing R] {B' : Type} [CommRing B']
    {ζ' : B'} {s' : Sp R ⟶ Sp B'} (y : Sp R ⟶ F.X) (Cy : SiegPre h N ζ' s') (hCy : SiegPB Cy F.univ y)
    (v : Fin h ⊕ Fin h → ℤ) (hv : Cy.lev v = 1) : ∃ b, v = N • b := by
  obtain ⟨p, -, hp1, -, -, hp4⟩ := hCy
  have e : y ≫ (F.univ.lev v).left = y ≫ (1 : 𝟙_ (Over F.X) ⟶ F.univ.A).left := by
    have := pow_section hp1 _ _ (hp4 v) 0
    rw [pow_zero, pow_zero] at this
    rw [← hp4 v, hv, ← this]
  let K := AlgebraicClosure (IsLocalRing.ResidueField R)
  let z : Sp K ⟶ Sp R := spMap ((algebraMap (IsLocalRing.ResidueField R) K).comp (IsLocalRing.residue R))
  obtain ⟨β, hβ⟩ := exists_spMap ((z ≫ y) ≫ F.s)
  let u : Kˣ := Units.ofPowEqOne (β (zetaAway N)) N (by rw [← map_pow, zeta_pow hN, map_one]) hN
  obtain ⟨g1, -, -⟩ := F.univ.geom K (z ≫ y) β u hβ rfl
  refine (g1 v).1 (Over.OverMorphism.ext ?_)
  rw [unit_left', Category.assoc, e, ← Category.assoc, ← unit_left', MonObj.comp_one]

theorem Twist.eq_id_of_fixed (hn : 3 ≤ n) (hN : Odd N) (hnN : n ∣ N) (hj : j (zetaAway n) = zetaAway N ^ (N / n))
    {T : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] (Fin h ⊕ Fin h → ℤ)} {m : ℕ} {σ : cycAway N →+* cycAway N} {f : F.X ⟶ F.X}
    (t : Twist F j T m σ f) {k : Type} [Field k] [IsAlgClosed k] (y : Sp k ⟶ F.X) (hy : y ≫ f = y) : f = 𝟙 _ := by
  have hN0 : N ≠ 0 := hN.pos.ne'
  obtain ⟨β, hβ⟩ := exists_spMap (y ≫ F.s)
  have hσβ : β.comp σ = β :=
    spMap_inj (by rw [← spMap_comp', ← hβ, Category.assoc, ← t.comm, ← Category.assoc, hy])
  have e : β (zetaAway N) ^ m = β (zetaAway N) ^ 1 := by
    rw [pow_one, ← map_pow, ← t.root, ← RingHom.comp_apply, hσβ]
  have hσ1 : σ = RingHom.id _ := (cycAway_galois N hN0).2.1 _ σ (RingHom.id _) (by
    rw [t.root, RingHom.id_apply, zeta_pow_congr hN0 β e, pow_one])
  obtain ⟨ν, a, b, c⟩ := t.map
  obtain ⟨Cy, hCy⟩ := (GlobalTheory.siegPre_pullback h N (cycAway N) (zetaAway N) F.X (Sp k) F.s (y ≫ F.s) y F.univ rfl).1
  obtain ⟨p, p₂, hp1, hp2, hp3, hp4⟩ := hCy
  have hpd : SRelBy Cy F.univ (N / n) (N / n) y p := ⟨hp1, ⟨p₂, hp2, hp3⟩, fun x => pow_section hp1 _ _ (hp4 x) _⟩
  have h2 : SRelBy Cy F.univ (N / n) (N / n) y (p ≫ ν) := by
    have := sRelBy_comp (t.sRelBy a b c) hpd
    rwa [hy] at this
  have hpp : p = p ≫ ν := rig hn hN hnN hj Cy y p (p ≫ ν) hpd h2
  have hlev : ∀ x, y ≫ (F.univ.lev (T x)).left = y ≫ (F.univ.lev x).left := fun x => by
    calc y ≫ (F.univ.lev (T x)).left = (Cy.lev (T x)).left ≫ p := (hp4 _).symm
      _ = (Cy.lev (T x)).left ≫ p ≫ ν := by rw [← hpp]
      _ = y ≫ (F.univ.lev (T x)).left ≫ ν := by rw [← Category.assoc, hp4, Category.assoc]
      _ = y ≫ (F.univ.lev x).left := by rw [c, ← Category.assoc, hy]
  let z : kˣ := Units.ofPowEqOne (β (zetaAway N)) N (by rw [← map_pow, zeta_pow hN0, map_one]) hN0
  obtain ⟨g1, -, -⟩ := F.univ.geom k y β z hβ rfl
  have hT : ∀ x, F.univ.lev (T x) = F.univ.lev x := fun x => by
    have e1 : toUnit (Over.mk y) ≫ F.univ.lev (T x) = toUnit (Over.mk y) ≫ F.univ.lev x :=
      Over.OverMorphism.ext (by rw [unit_left', unit_left', hlev])
    have e2 : toUnit (Over.mk y) ≫ F.univ.lev (T x - x) = 1 := by
      have := F.univ.lev_add (T x - x) x
      rw [sub_add_cancel] at this
      rw [this, MonObj.comp_mul] at e1
      exact mul_eq_right.1 e1
    obtain ⟨b', hb'⟩ := (g1 _).1 e2
    rw [← sub_add_cancel (T x) x, F.univ.lev_add, hb', lev_N_smul, _root_.one_mul]
  exact t.unique hN0 twist_one hσ1 hT

end GlobalTheory.SiegAct

namespace GlobalTheory.SiegAct

variable {h n N : ℕ} {F : SFam h N (zetaAway N)} {j : cycAway n →+* cycAway N}

theorem exists_twist_of_points (hn : 3 ≤ n) (hN : Odd N) (hnN : n ∣ N) (hj : j (zetaAway n) = zetaAway N ^ (N / n))
    (R : Type) [CommRing R] [IsLocalRing R] (y y' : Sp R ⟶ F.X) (s' : Sp R ⟶ Sp (cycAway n))
    (c : SiegPre h n (zetaAway n) s') (hs : y ≫ F.s ≫ spMap j = y' ≫ F.s ≫ spMap j)
    (hy : SRel c F.univ 1 (N / n) y) (hy' : SRel c F.univ 1 (N / n) y') :
    ∃ T m σ f, Twist F j T m σ f ∧ y ≫ f = y' := by
  have hN0 : N ≠ 0 := hN.pos.ne'
  have hn0 : n ≠ 0 := by omega
  obtain ⟨β, hβ⟩ := exists_spMap (y ≫ F.s)
  obtain ⟨β', hβ'⟩ := exists_spMap (y' ≫ F.s)
  have G := cycAway_galois N hN0
  obtain ⟨m, hmc, hm⟩ := G.2.2 R β β'
  obtain ⟨σ, hσ⟩ := G.1 m hmc
  obtain ⟨Cy, hCy⟩ := (GlobalTheory.siegPre_pullback h N (cycAway N) (zetaAway N) F.X (Sp R) F.s (spMap β) y F.univ hβ).1
  obtain ⟨Cy', hCy'⟩ := (GlobalTheory.siegPre_pullback h N (cycAway N) (zetaAway N) F.X (Sp R) F.s (spMap β') y' F.univ hβ').1
  have k1 : SRel Cy F.univ (N / n) (N / n) y := sRel_scale ((sRel_one_one_iff _ _ _).2 hCy) _
  have k1' : SRel Cy' F.univ (N / n) (N / n) y' := sRel_scale ((sRel_one_one_iff _ _ _).2 hCy') _
  have a1 : SRel c Cy 1 (N / n) (𝟙 _) := sRel_cancel k1 (by rwa [Category.id_comp])
  have a1' : SRel c Cy' 1 (N / n) (𝟙 _) := sRel_cancel k1' (by rwa [Category.id_comp])
  have idCy' : SRel Cy' Cy' (N / n) (N / n) (𝟙 _ ≫ 𝟙 _) := by
    rw [Category.comp_id]; exact sRel_scale ((sRel_one_one_iff _ _ _).2 (GlobalTheory.SiegelPullComp.pb_id Cy')) _
  have a2 : SRel Cy' c (N / n) 1 (𝟙 _) := sRel_cancel a1' idCy'
  have a3 : SRel Cy' Cy (N / n) (N / n) (𝟙 _ ≫ 𝟙 _) := sRel_comp a1 a2
  rw [Category.comp_id] at a3
  obtain ⟨φ, hφ, ⟨φ₂, hsq, hP⟩, hl⟩ := a3
  obtain ⟨T, hTω, hTl⟩ := (GlobalTheory.T.siegel_level_change_by_symplectic_similitude h N (cycAway N) (cycBase hN0) hN).2 R β m β' Cy Cy' φ φ₂ hm hφ hsq hP

  have low : ∀ x, F.univ.lev (T x) ^ (N / n) = F.univ.lev x ^ (N / n) := fun x => by
    have e1 := pow_section hφ _ _ ((hTl x).trans (Category.id_comp _).symm) (N / n)
    have e2 : Cy.lev (T x) ^ (N / n) = Cy.lev x ^ (N / n) := Over.OverMorphism.ext (by
      have := e1.symm.trans (hl x)
      rwa [Category.id_comp, Category.id_comp] at this)
    have e3 : Cy.lev ((N / n) • (T x - x)) = 1 := by
      have := Cy.lev_add ((N / n) • (T x - x)) ((N / n) • x)
      rw [← smul_add, sub_add_cancel, lev_nsmul Cy (N / n) (T x), lev_nsmul Cy (N / n) x, e2] at this
      exact mul_eq_right.1 this.symm
    obtain ⟨b, hb⟩ := exists_eq_nsmul_of_pull hN0 y Cy hCy _ e3
    have e4 := F.univ.lev_add ((N / n) • (T x - x)) ((N / n) • x)
    rw [← smul_add, sub_add_cancel, lev_nsmul F.univ (N / n) (T x), lev_nsmul F.univ (N / n) x, hb, lev_N_smul,
      _root_.one_mul] at e4
    exact e4

  have hbj : β.comp j = β'.comp j := spMap_inj (by
    rw [← spMap_comp', ← spMap_comp', ← hβ, ← hβ', Category.assoc, Category.assoc, hs])
  let r := IsLocalRing.residue R
  have e5 : (r.comp β) (zetaAway N) ^ (N / n) = (r.comp β) (zetaAway N) ^ (m * (N / n)) := by
    have := congrArg r (RingHom.congr_fun hbj (zetaAway n))
    simp only [RingHom.comp_apply, hj, map_pow, hm] at this
    rw [RingHom.comp_apply, this, pow_mul]
  have e6 := zeta_pow_congr hN0 (r.comp β) e5
  have fix : σ.toRingHom.comp j = j := (cycAway_galois n hn0).2.1 _ _ _ (by
    rw [RingHom.comp_apply, hj, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, map_pow, hσ, ← pow_mul, e6])
  obtain ⟨f, t⟩ := exists_twist (F := F) hN0 σ.injective hmc hσ fix hTω low
  obtain ⟨hinj, hsurj, -⟩ := GlobalTheory.T.symplecticSimilitude_invertible_modN h N m T hN0 hmc hTω
  have X0 : SiegPB Cy' (relabel Cy T σ.toRingHom hN0 (zeta_pow hN0) hσ hTω hinj hsurj) (𝟙 _) :=
    ⟨φ, φ₂, hφ, hsq, hP, fun x => (hTl x).trans (Category.id_comp _).symm⟩
  obtain ⟨p, p₂, hp1, hp2, hp3, hp4⟩ := hCy
  have X1 : SiegPB (relabel Cy T σ.toRingHom hN0 (zeta_pow hN0) hσ hTω hinj hsurj)
      (relabel F.univ T σ.toRingHom hN0 (zeta_pow hN0) hσ hTω hinj hsurj) y :=
    ⟨p, p₂, hp1, hp2, hp3, fun x => hp4 (T x)⟩
  have X2 := GlobalTheory.SiegelPullComp.pb_comp (GlobalTheory.SiegelPullComp.pb_comp (t.siegPB hN0 hinj hsurj) X1) X0
  rw [Category.id_comp] at X2
  have hbs : β.comp σ.toRingHom = β' := G.2.1 R _ _ (by
    rw [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hσ, map_pow, hm])
  refine ⟨T, m, σ.toRingHom, f, t, F.inj R (y ≫ f) y' (spMap β') Cy' ?_ X2 hCy'⟩
  rw [Category.assoc, t.comm, ← Category.assoc, hβ, spMap_comp', hbs, hβ']

end GlobalTheory.SiegAct

namespace GlobalTheory.SiegAct

variable {h n N : ℕ} {F : SFam h N (zetaAway N)} {j : cycAway n →+* cycAway N}

theorem Twist.exists_inv (hN : N ≠ 0) (hN1 : 1 < N) (hn0 : n ≠ 0) (hj : j (zetaAway n) = zetaAway N ^ (N / n))
    {T : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] (Fin h ⊕ Fin h → ℤ)} {m : ℕ} {σ : cycAway N →+* cycAway N} {f : F.X ⟶ F.X}
    (t : Twist F j T m σ f) :
    ∃ (T' : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] (Fin h ⊕ Fin h → ℤ)) (m' : ℕ) (σ' : cycAway N →+* cycAway N) (f' : F.X ⟶ F.X),
      Twist F j T' m' σ' f' ∧ f ≫ f' = 𝟙 _ := by
  obtain ⟨-, -, T', hT', hω'⟩ := GlobalTheory.T.symplecticSimilitude_invertible_modN h N m T hN t.cop t.symp
  haveI : NeZero N := ⟨hN⟩
  set m' : ℕ := (((ZMod.unitOfCoprime m t.cop)⁻¹ : (ZMod N)ˣ) : ZMod N).val with hm'
  have hmm : m * m' ≡ 1 [MOD N] := by
    refine (ZMod.natCast_eq_natCast_iff _ _ _).1 ?_
    rw [Nat.cast_mul, hm', ZMod.natCast_zmod_val, Nat.cast_one, ← ZMod.coe_unitOfCoprime m t.cop]
    exact Units.mul_inv _
  have cop' : m'.Coprime N := Nat.coprime_of_mul_modEq_one m (by rwa [mul_comm])
  have G := cycAway_galois N hN
  obtain ⟨σ', hσ'⟩ := G.1 m' cop'
  have hz1 : zetaAway N ^ (m * m') = zetaAway N := by
    rw [pow_eq_pow_mod (m * m') (zeta_pow hN), show m * m' % N = 1 % N from hmm,
      ← pow_eq_pow_mod 1 (zeta_pow hN), pow_one]
  have hfix : zetaAway N ^ (m * (N / n)) = zetaAway N ^ (N / n) := by
    have := RingHom.congr_fun t.fix (zetaAway n)
    rwa [RingHom.comp_apply, hj, map_pow, t.root, ← pow_mul] at this
  have fix' : σ'.toRingHom.comp j = j := (cycAway_galois n hn0).2.1 _ _ _ (by
    rw [RingHom.comp_apply, hj, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, map_pow, hσ', ← pow_mul]
    calc zetaAway N ^ (m' * (N / n)) = (zetaAway N ^ (m * (N / n))) ^ m' := by rw [hfix, ← pow_mul, mul_comm]
      _ = (zetaAway N ^ (m * m')) ^ (N / n) := by rw [← pow_mul, ← pow_mul]; congr 1; ring
      _ = zetaAway N ^ (N / n) := by rw [hz1])
  have hTT : ∀ x, F.univ.lev (T (T' x)) = F.univ.lev x := fun x => by
    obtain ⟨b, hb⟩ := hT' x
    rw [hb, F.univ.lev_add, lev_N_smul, _root_.mul_one]
  obtain ⟨f', t'⟩ := exists_twist (F := F) hN σ'.injective cop' hσ' fix' (hω' m' hmm)
    (fun x => by rw [← t.low (T' x), hTT])
  refine ⟨T', m', σ'.toRingHom, f', t', (t.mul t').unique hN twist_one ?_ hTT⟩
  exact G.2.1 _ _ _ (by
    rw [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hσ', map_pow, t.root, ← pow_mul, hz1,
      RingHom.id_apply])

variable (F j) in

def Grp : Type := {f : F.X ⟶ F.X // ∃ T m σ, Twist F j T m σ f}

instance : One (Grp F j) := ⟨⟨𝟙 _, _, _, _, twist_one⟩⟩

instance : Mul (Grp F j) := ⟨fun a c => ⟨a.1 ≫ c.1, by
  obtain ⟨T, m, σ, t⟩ := a.2
  obtain ⟨T', m', σ', t'⟩ := c.2
  exact ⟨_, _, _, t.mul t'⟩⟩⟩

theorem Grp.exists_inv (hN : N ≠ 0) (hN1 : 1 < N) (hn0 : n ≠ 0) (hj : j (zetaAway n) = zetaAway N ^ (N / n))
    (a : Grp F j) : ∃ c : Grp F j, a * c = 1 := by
  obtain ⟨T, m, σ, t⟩ := a.2
  obtain ⟨T', m', σ', f', t', e⟩ := t.exists_inv hN hN1 hn0 hj
  exact ⟨⟨f', T', m', σ', t'⟩, Subtype.ext e⟩

@[reducible] def Grp.group (hN : N ≠ 0) (hN1 : 1 < N) (hn0 : n ≠ 0) (hj : j (zetaAway n) = zetaAway N ^ (N / n)) :
    Group (Grp F j) :=
  letI : Inv (Grp F j) := ⟨fun a => (Grp.exists_inv hN hN1 hn0 hj a).choose⟩
  Group.ofRightAxioms (fun _ _ _ => Subtype.ext (Category.assoc _ _ _)) (fun _ => Subtype.ext (Category.comp_id _))
    fun a => (Grp.exists_inv hN hN1 hn0 hj a).choose_spec

theorem lev_eq_of_cast {B : Type} [CommRing B] {ζ : B} {S : Scheme.{0}} {s : S ⟶ Sp B} (C : SiegPre h N ζ s)
    {v w : Fin h ⊕ Fin h → ℤ} (e : ∀ k, ((v k : ℤ) : ZMod N) = ((w k : ℤ) : ZMod N)) : C.lev v = C.lev w := by
  have hd : ∀ k, (N : ℤ) ∣ v k - w k := fun k => (ZMod.intCast_eq_intCast_iff_dvd_sub (w k) (v k) N).1 (e k).symm
  have : v = w + N • fun k => (v k - w k) / N := by
    funext k
    rw [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul, Int.mul_ediv_cancel' (hd k)]
    ring
  rw [this, C.lev_add, lev_N_smul, _root_.mul_one]

theorem Grp.finite (hN : N ≠ 0) : Finite (Grp F j) := by
  haveI : NeZero N := ⟨hN⟩
  choose T m σ t using fun a : Grp F j => a.2
  have key : ∀ (U : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] (Fin h ⊕ Fin h → ℤ)) x k, ((U x k : ℤ) : ZMod N) =
      ∑ i, ((x i : ℤ) : ZMod N) * ((U (fun l => if i = l then 1 else 0) k : ℤ) : ZMod N) := by
    intro U x k
    conv_lhs => rw [LinearMap.pi_apply_eq_sum_univ U x]
    simp [Finset.sum_apply]
  refine Finite.of_injective (β := (Fin h ⊕ Fin h → Fin h ⊕ Fin h → ZMod N) × ZMod N)
    (fun a => (fun i k => (((T a) (fun l => if i = l then 1 else 0) k : ℤ) : ZMod N), (m a : ZMod N)))
    fun a c hac => Subtype.ext ?_
  simp only [Prod.mk.injEq] at hac
  obtain ⟨h1, h2⟩ := hac
  refine (t a).unique hN (t c) ?_ fun x => lev_eq_of_cast F.univ fun k => ?_
  · apply (cycAway_galois N hN).2.1
    rw [(t a).root, (t c).root, pow_eq_pow_mod (m a) (zeta_pow hN), pow_eq_pow_mod (m c) (zeta_pow hN),
      (ZMod.natCast_eq_natCast_iff' _ _ _).1 h2]
  · rw [key, key]
    exact Finset.sum_congr rfl fun i _ => by rw [congrFun (congrFun h1 i) k]

theorem siegel_group_action : ∀ (h n N : ℕ) (F : SFam h N (zetaAway N)) (j : cycAway n →+* cycAway N), 3 ≤ n → Odd N → n ∣ N → j (zetaAway n) = zetaAway N ^ (N / n) → ∃ (Ga : Type) (_ : Group Ga) (_ : Finite Ga) (ρ : Ga → (F.X ⟶ F.X)) (ν : Ga → (F.univ.A.left ⟶ F.univ.A.left)), ρ 1 = 𝟙 _ ∧ (∀ a c, ρ (a * c) = ρ a ≫ ρ c) ∧ ν 1 = 𝟙 _ ∧ (∀ a c, ν (a * c) = ν a ≫ ν c) ∧ (∀ a, ρ a ≫ F.s ≫ spMap j = F.s ≫ spMap j) ∧ (∀ a, SRelBy F.univ F.univ (N / n) (N / n) (ρ a) (ν a)) ∧ (∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ F.X) (a : Ga), y ≫ ρ a = y → a = 1) ∧ ∀ (R : Type) [CommRing R] [IsLocalRing R] (y y' : Sp R ⟶ F.X) (s' : Sp R ⟶ Sp (cycAway n)) (c : SiegPre h n (zetaAway n) s'), y ≫ F.s ≫ spMap j = y' ≫ F.s ≫ spMap j → SRel c F.univ 1 (N / n) y → SRel c F.univ 1 (N / n) y' → ∃ a, y ≫ ρ a = y' := by
  intro h n N F j hn hN hnN hj
  have hN0 : N ≠ 0 := hN.pos.ne'
  have hn0 : n ≠ 0 := by omega
  have hN1 : 1 < N := by have := Nat.le_of_dvd hN.pos hnN; omega
  letI G := Grp.group (F := F) (j := j) hN0 hN1 hn0 hj
  have hν : ∀ a : Grp F j, ∃ ν : F.univ.A.left ⟶ F.univ.A.left, SRelBy F.univ F.univ (N / n) (N / n) a.1 ν :=
    fun a => by
      obtain ⟨T, m, σ, t⟩ := a.2
      obtain ⟨ν, x, y, z⟩ := t.map
      exact ⟨ν, t.sRelBy x y z⟩
  choose ν hν using hν
  have idpb : SRelBy F.univ F.univ (N / n) (N / n) (𝟙 _) (𝟙 _) :=
    ⟨⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy =>
      (mul_left_congr (G := F.univ.A) (Category.comp_id T.hom) x₀ y₀ x y (hx.trans (Category.comp_id _))
        (hy.trans (Category.comp_id _))).trans (Category.comp_id _).symm⟩,
      ⟨𝟙 _, ⟨by simp, by simp⟩, GlobalTheory.SiegelPullComp.iso_pull_id F.univ.isLB⟩, fun x => by simp⟩
  refine ⟨Grp F j, G, Grp.finite hN0, fun a => a.1, ν, rfl, fun _ _ => rfl, ?_, fun a c => ?_, fun a => ?_, hν,
    fun k _ _ y a hy => ?_, fun R _ _ y y' s' c hs h1 h2 => ?_⟩
  · exact rig hn hN hnN hj F.univ (𝟙 _) _ _ (hν 1) idpb
  · exact rig hn hN hnN hj F.univ _ _ _ (hν (a * c)) (sRelBy_comp (hν c) (hν a))
  · obtain ⟨T, m, σ, t⟩ := a.2
    rw [← Category.assoc, t.comm, Category.assoc, spMap_comp', t.fix]
  · obtain ⟨T, m, σ, t⟩ := a.2
    exact Subtype.ext (t.eq_id_of_fixed hn hN hnN hj y hy)
  · obtain ⟨T, m, σ, f, t, e⟩ := exists_twist_of_points hn hN hnN hj R y y' s' c hs h1 h2
    exact ⟨⟨f, T, m, σ, t⟩, e⟩

end GlobalTheory.SiegAct
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelFamily_similitudeGroup_action_free_transitive : ∀ (h n N : ℕ) (F : SFam h N (zetaAway N)) (j : cycAway n →+* cycAway N), 3 ≤ n → Odd N → n ∣ N → j (zetaAway n) = zetaAway N ^ (N / n) → ∃ (Ga : Type) (_ : Group Ga) (_ : Finite Ga) (ρ : Ga → (F.X ⟶ F.X)) (ν : Ga → (F.univ.A.left ⟶ F.univ.A.left)), ρ 1 = 𝟙 _ ∧ (∀ a c, ρ (a * c) = ρ a ≫ ρ c) ∧ ν 1 = 𝟙 _ ∧ (∀ a c, ν (a * c) = ν a ≫ ν c) ∧ (∀ a, ρ a ≫ F.s ≫ spMap j = F.s ≫ spMap j) ∧ (∀ a, SRelBy F.univ F.univ (N / n) (N / n) (ρ a) (ν a)) ∧ (∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ F.X) (a : Ga), y ≫ ρ a = y → a = 1) ∧ ∀ (R : Type) [CommRing R] [IsLocalRing R] (y y' : Sp R ⟶ F.X) (s' : Sp R ⟶ Sp (cycAway n)) (c : SiegPre h n (zetaAway n) s'), y ≫ F.s ≫ spMap j = y' ≫ F.s ≫ spMap j → SRel c F.univ 1 (N / n) y → SRel c F.univ 1 (N / n) y' → ∃ a, y ≫ ρ a = y' := by
  first | exact @GlobalTheory.SiegAct.siegel_group_action | exact GlobalTheory.SiegAct.siegel_group_action | (intros; apply GlobalTheory.SiegAct.siegel_group_action <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isQProjOver_target_galoisCover_noetherian : ∀ (K : Type) [CommRing K] [IsNoetherianRing K] (X Y : Scheme.{0}) (π : X ⟶ Y) (sY : Y ⟶ Sp K) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)), IsGaloisCover Ga ρ π → IsSeparated sY → LocallyOfFiniteType sY → IsQProjOver (π ≫ sY) → IsQProjOver sY := by
  first | exact @GlobalTheory.GaloisQuotientRing.isQProjOver_of_isGaloisCover | exact GlobalTheory.GaloisQuotientRing.isQProjOver_of_isGaloisCover | (intros; apply GlobalTheory.GaloisQuotientRing.isQProjOver_of_isGaloisCover <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isQProjOver_of_relAmple_over_qproj_noetherian : ∀ (K : Type) [CommRing K] [IsNoetherianRing K] (X : Scheme.{0}) (s : X ⟶ Sp K) (A : Over X) (L : LB A.left), IsQProjOver s → L.IsLB → Out.RelAmple A L → IsQProjOver (A.hom ≫ s) := by
  first | exact @GlobalTheory.RelAmpleQProjNoeth.isQProjOver_of_relAmple_noeth | exact GlobalTheory.RelAmpleQProjNoeth.isQProjOver_of_relAmple_noeth | (intros; apply GlobalTheory.RelAmpleQProjNoeth.isQProjOver_of_relAmple_noeth <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_descends_galoisCover_noetherian_base : ∀ (K : Type) [CommRing K] [IsNoetherianRing K] (X Y : Scheme.{0}) (π : X ⟶ Y) (sY : Y ⟶ Sp K) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (G : Over X) [GrpObj G] (ν : Ga → (G.left ⟶ G.left)), IsGaloisCover Ga ρ π → IsQProjOver (G.hom ≫ π ≫ sY) → IsAbelianScheme G → (∀ a, IsGrpPullback G G (ρ a) (ν a)) → ν 1 = 𝟙 _ → (∀ a c, ν (a * c) = ν a ≫ ν c) → ∃ (G' : Over Y) (_ : GrpObj G') (φ : G.left ⟶ G'.left), IsAbelianScheme G' ∧ IsGrpPullback G G' π φ ∧ IsGaloisCover Ga ν φ := by
  first | exact @GlobalTheory.abelianScheme_descends_galoisCover_noetherian | exact GlobalTheory.abelianScheme_descends_galoisCover_noetherian | (intros; apply GlobalTheory.abelianScheme_descends_galoisCover_noetherian <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_squareBundle_descent_galoisCover : ∀ (X Y : Scheme.{0}) (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (A : Over X) [GrpObj A] (A₀ : Over Y) [GrpObj A₀] (φ : A.left ⟶ A₀.left) (ν : Ga → (A.left ⟶ A.left)) (P : LB (G2 A).left), IsGaloisCover Ga ρ π → IsAbelianScheme A → IsAbelianScheme A₀ → IsGrpPullback A A₀ π φ → IsGaloisCover Ga ν φ → (∀ a, IsGrpPullback A A (ρ a) (ν a)) → ν 1 = 𝟙 _ → (∀ a c, ν (a * c) = ν a ≫ ν c) → P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∀ a, ∃ φ₂ : (G2 A).left ⟶ (G2 A).left, IsSquare (ν a) φ₂ ∧ LBIso P (P.pull φ₂)) → ∃ (P₀ : LB (G2 A₀).left) (φ₂ : (G2 A).left ⟶ (G2 A₀).left), P₀.IsLB ∧ IsSquare φ φ₂ ∧ LBIso P (P₀.pull φ₂) ∧ ∃ t : (P₀.pull (eSec (G2 A₀))).Gen, t.IsGen := by
  first | exact @GlobalTheory.SquareDescent.exists_bundle_descent | exact GlobalTheory.SquareDescent.exists_bundle_descent | (intros; apply GlobalTheory.SquareDescent.exists_bundle_descent <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.SiegLev

theorem descData_transport_id : ∀ (h n N d : ℕ) (B B' : Type) [CommRing B] [CommRing B'] (ζ : B) (ζ' : B') (X Y : Scheme.{0}) (s : X ⟶ Sp B) (s' : X ⟶ Sp B') (C : SiegPre h N ζ' s') (c : SiegPre h n ζ s) (π : X ⟶ Y) (A₀ : Over Y) [GrpObj A₀] (φ : C.A.left ⟶ A₀.left) (φ₂ : (G2 C.A).left ⟶ (G2 A₀).left) (P₀ : LB (G2 A₀).left) (lev₀ : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over Y) ⟶ A₀)), SRel C c d 1 (𝟙 X) → IsGrpPullback C.A A₀ π φ → IsSquare φ φ₂ → P₀.IsLB → LBIso C.P (P₀.pull φ₂) → (∀ a, (C.lev a ^ d).left ≫ φ = π ≫ (lev₀ a).left) → ∃ (φ' : c.A.left ⟶ A₀.left) (φ₂' : (G2 c.A).left ⟶ (G2 A₀).left), IsGrpPullback c.A A₀ π φ' ∧ IsSquare φ' φ₂' ∧ LBIso c.P (P₀.pull φ₂') ∧ ∀ a, (c.lev a).left ≫ φ' = π ≫ (lev₀ a).left := by
  intro h n N d B B' _ _ ζ ζ' X Y s s' C c π A₀ _ φ φ₂ P₀ lev₀ hS hA hsq hP₀ hw hlev
  obtain ⟨ψ, hψ, ⟨ψ₂, hsqψ, hC⟩, hlevψ⟩ := hS
  haveI : IsMonHom (Iso.refl c.A).hom := inferInstanceAs (IsMonHom (𝟙 c.A))
  obtain ⟨e, he, heψ⟩ := grpPullback_iso (isGrpPullback_of_iso (Iso.refl c.A)) hψ
  haveI := he
  have heψ' : e.hom.left ≫ ψ = 𝟙 _ := by simpa using heψ
  have hie : e.inv.left ≫ e.hom.left = 𝟙 _ := by rw [← Over.comp_left, e.inv_hom_id, Over.id_left]
  have hψe : ψ = e.inv.left := by
    rw [← Category.id_comp ψ, ← hie, Category.assoc, heψ', Category.comp_id]
  let E₂ : G2 c.A ⟶ G2 C.A := lift (fst c.A c.A ≫ e.hom) (snd c.A c.A ≫ e.hom)
  have hE₂ : E₂.left ≫ ψ₂ = 𝟙 _ := by
    have := GlobalTheory.SiegelDescent.lift_square hsqψ (τ := 𝟙 (G2 c.A).left) (a := fst c.A c.A ≫ e.hom)
      (b := snd c.A c.A ≫ e.hom) (a₀ := fst c.A c.A) (b₀ := snd c.A c.A)
      (by rw [Over.comp_left, Category.assoc, heψ', Category.comp_id, Category.id_comp])
      (by rw [Over.comp_left, Category.assoc, heψ', Category.comp_id, Category.id_comp])
    rw [this, lift_fst_snd, Over.id_left, Category.comp_id]
  refine ⟨e.hom.left ≫ φ, E₂.left ≫ φ₂, ((isGrpPullback_of_iso e).comp hA).congr (Category.id_comp π) rfl, ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [Category.assoc, hsq.1, ← Category.assoc, ← Over.comp_left, lift_fst, Over.comp_left, Category.assoc]
  · rw [Category.assoc, hsq.2, ← Category.assoc, ← Over.comp_left, lift_snd, Over.comp_left, Category.assoc]
  · have h1 : LBIso (C.P.pull E₂.left) (P₀.pull (E₂.left ≫ φ₂)) :=
      LBIso.chartPull (chartPullPull C.P E₂.left)
        (chartPullSame P₀ _ (fun _ => φ₂) _ E₂.left fun _ => rfl) hw
    have h2 : LBIso (C.P.pull E₂.left) (c.P.pull (E₂.left ≫ ψ₂)) :=
      LBIso.chartPull (chartPullPull C.P E₂.left)
        (chartPullSame c.P _ (fun _ => ψ₂) _ E₂.left fun _ => rfl) hC
    have h3 : LBIso (c.P.pull (E₂.left ≫ ψ₂)) (P₀.pull (E₂.left ≫ φ₂)) :=
      LBIso.trans (pull_isLB c.isLB _) (pull_isLB C.isLB _) (pull_isLB hP₀ _) h2.symm h1
    exact LBIso.chartPull (chartPullUnpull c.P _ hE₂)
      (chartPullSame P₀ _ _ _ (𝟙 _) fun _ => (Category.id_comp _).symm) h3
  · intro a
    have h₀ := hlevψ a
    rw [pow_one, Category.id_comp, hψe] at h₀
    rw [← h₀, Category.assoc, ← Category.assoc e.inv.left, hie, Category.id_comp, hlev a]

end GlobalTheory.SiegLev
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.descendedData_transport_identity_levelChange : ∀ (h n N d : ℕ) (B B' : Type) [CommRing B] [CommRing B'] (ζ : B) (ζ' : B') (X Y : Scheme.{0}) (s : X ⟶ Sp B) (s' : X ⟶ Sp B') (C : SiegPre h N ζ' s') (c : SiegPre h n ζ s) (π : X ⟶ Y) (A₀ : Over Y) [GrpObj A₀] (φ : C.A.left ⟶ A₀.left) (φ₂ : (G2 C.A).left ⟶ (G2 A₀).left) (P₀ : LB (G2 A₀).left) (lev₀ : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over Y) ⟶ A₀)), SRel C c d 1 (𝟙 X) → IsGrpPullback C.A A₀ π φ → IsSquare φ φ₂ → P₀.IsLB → LBIso C.P (P₀.pull φ₂) → (∀ a, (C.lev a ^ d).left ≫ φ = π ≫ (lev₀ a).left) → ∃ (φ' : c.A.left ⟶ A₀.left) (φ₂' : (G2 c.A).left ⟶ (G2 A₀).left), IsGrpPullback c.A A₀ π φ' ∧ IsSquare φ' φ₂' ∧ LBIso c.P (P₀.pull φ₂') ∧ ∀ a, (c.lev a).left ≫ φ' = π ≫ (lev₀ a).left := by
  atlas_forward_decl GlobalTheory.SiegLev.descData_transport_id
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_siegelObject_of_galois_descended_data : ∀ (h M : ℕ) (o : Type) [CommRing o] (ζ : o) (X Y : Scheme.{0}) (π : X ⟶ Y) (s : X ⟶ Sp o) (sY : Y ⟶ Sp o) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (c : SiegPre h M ζ s) (A₀ : Over Y) [GrpObj A₀] (φ : c.A.left ⟶ A₀.left) (φ₂ : (G2 c.A).left ⟶ (G2 A₀).left) (P₀ : LB (G2 A₀).left) (lev₀ : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over Y) ⟶ A₀)), s = π ≫ sY → IsGaloisCover Ga ρ π → IsAbelianScheme A₀ → IsGrpPullback c.A A₀ π φ → IsSquare φ φ₂ → P₀.IsLB → LBIso c.P (P₀.pull φ₂) → (∃ t : (P₀.pull (eSec (G2 A₀))).Gen, t.IsGen) → (∀ a, (c.lev a).left ≫ φ = π ≫ (lev₀ a).left) → ∃ c₀ : SiegPre h M ζ sY, SiegPB c c₀ π := by
  first | exact @GlobalTheory.exists_siegPre_of_galois_descended_data | exact GlobalTheory.exists_siegPre_of_galois_descended_data | (intros; apply GlobalTheory.exists_siegPre_of_galois_descended_data <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.SiegLevDescent

theorem principal_of_sRel_finite_etale : ∀ (h M M₀ d d₀ : ℕ) (B B₀ : Type) [CommRing B] [CommRing B₀] (ζ : B) (ζ₀ : B₀) (X Y : Scheme.{0}) [IsLocallyNoetherian Y] (s : X ⟶ Sp B) (s₀ : Y ⟶ Sp B₀) (π : X ⟶ Y) (c : SiegPre h M ζ s) (c₀ : SiegPre h M₀ ζ₀ s₀), IsFinite π → Etale π → Surjective π → SRel c c₀ d d₀ π → c.Principal → c₀.Principal := by
  intro h M M₀ d d₀ B B₀ _ _ ζ ζ₀ X Y _ s s₀ π c c₀ hfin het hsurj m hc
  obtain ⟨φ, pb, ⟨φ₂, sq, iso⟩, -⟩ := m
  obtain ⟨h₁, h₂⟩ := hc
  refine ⟨(relAmple_kTriv_of_finite_etale_cover Y X π c₀.A c.A φ c₀.diag c.diag hfin het hsurj c₀.ab
    (pull_isLB c₀.isLB _) (pull_isLB c.isLB _) pb (GlobalTheory.SiegelPull.diag_iso sq iso)).1 h₁, ?_⟩
  intro T x ⟨t, ht⟩
  haveI := het
  haveI := hsurj
  let T' : Over X := Over.mk (pullback.snd T.hom π)
  let p : T'.left ⟶ T.left := pullback.fst T.hom π
  have hp : p ≫ T.hom = T'.hom ≫ π := pullback.condition
  haveI : Epi p := Flat.epi_of_flat_of_surjective _
  obtain ⟨ρ, hρ⟩ := GlobalTheory.SiegelDescent.exists_liftHom pb T' T p hp
  have hx' : (ρ x).left ≫ φ = p ≫ x.left := (hρ x (ρ x)).1 rfl
  have w₁ : (fst c.A T').left ≫ φ ≫ c₀.A.hom = ((snd c.A T').left ≫ p) ≫ T.hom := by
    rw [pb.1.w, ← Category.assoc, Over.w (fst c.A T'), Category.assoc, hp, ← Category.assoc,
      Over.w (snd c.A T')]
  let χ : (c.A ⊗ T').left ⟶ (c₀.A ⊗ T).left := pullback.lift ((fst c.A T').left ≫ φ) ((snd c.A T').left ≫ p) w₁
  have χ₁ : χ ≫ (fst c₀.A T).left = (fst c.A T').left ≫ φ := pullback.lift_fst _ _ _
  have χ₂ : χ ≫ (snd c₀.A T).left = (snd c.A T').left ≫ p := pullback.lift_snd _ _ _
  have e : (lift (snd c.A T' ≫ ρ x) (fst c.A T')).left ≫ φ₂ = χ ≫ (lift (snd c₀.A T ≫ x) (fst c₀.A T)).left :=
    GlobalTheory.SiegelDescent.lift_square sq (τ := χ)
      (by rw [Over.comp_left, Over.comp_left, Category.assoc, hx', ← Category.assoc χ, χ₂, Category.assoc])
      χ₁.symm
  have H := GlobalTheory.SiegelDescent.lbIso_square c.isLB c₀.isLB iso e
  obtain ⟨t₁, ht₁⟩ := gen_chartPull (chartPullPull (c₀.P.pull (lift (snd c₀.A T ≫ x) (fst c₀.A T)).left) χ) t ht
  have hg := GlobalTheory.SiegelDescent.exists_gen_of_lbIso (pull_isLB (pull_isLB c₀.isLB _) _) (pull_isLB c.isLB _)
    H.symm ⟨t₁, ht₁⟩
  have h₃ : ρ x = 1 := h₂ T' (ρ x) hg
  have h₄ : p ≫ x.left = p ≫ (1 : T ⟶ c₀.A).left := by
    rw [← hx', h₃, GlobalTheory.SiegelDescent.one_comp pb T' T p hp]
  exact Over.OverMorphism.ext ((cancel_epi p).1 h₄)

end GlobalTheory.SiegLevDescent
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principal_descent_finite_etale_surjective : ∀ (h M M₀ d d₀ : ℕ) (B B₀ : Type) [CommRing B] [CommRing B₀] (ζ : B) (ζ₀ : B₀) (X Y : Scheme.{0}) [IsLocallyNoetherian Y] (s : X ⟶ Sp B) (s₀ : Y ⟶ Sp B₀) (π : X ⟶ Y) (c : SiegPre h M ζ s) (c₀ : SiegPre h M₀ ζ₀ s₀), IsFinite π → Etale π → Surjective π → SRel c c₀ d d₀ π → c.Principal → c₀.Principal := by
  atlas_forward_decl GlobalTheory.SiegLevDescent.principal_of_sRel_finite_etale
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.PrincipalDescent

theorem principal_descends : ∀ (h n N : ℕ) (o o' : Type) [CommRing o] [IsNoetherianRing o] [CommRing o'] (b : TBase o n) (ζ' : o') (j : o →+* o') (X Y : Scheme.{0}) (s' : X ⟶ Sp o') (π : X ⟶ Y) (sY : Y ⟶ Sp o) (C : SiegPre h N ζ' s') (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (ν : Ga → (C.A.left ⟶ C.A.left)), N ≠ 0 → IsUnit (N : o') → n ∣ N → j (b.ζ : o) = ζ' ^ (N / n) → π ≫ sY = s' ≫ spMap j → IsGaloisCover Ga ρ π → IsQProjOver (π ≫ sY) → LocallyOfFiniteType sY → C.Principal → ν 1 = 𝟙 _ → (∀ a c, ν (a * c) = ν a ≫ ν c) → (∀ a, SRelBy C C (N / n) (N / n) (ρ a) (ν a)) → ∃ c : SiegPre h n (b.ζ : o) sY, c.Principal ∧ SRel C c (N / n) 1 π := by
  intro h n N o o' _ _ _ b ζ' j X Y s' π sY C Ga _ ρ ν hN hNu hdiv hζ hbase hπ hq hft hP ν1 νm hν
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  obtain ⟨c, hCc, -⟩ := GlobalTheory.T.exists_siegelObject_lowered_level h n N o o' b.ζ ζ' j X s' C hN hNu hdiv hζ
  have hqA : IsQProjOver (C.A.hom ≫ π ≫ sY) := GlobalTheory.T.isQProjOver_of_relAmple_over_qproj_noetherian o X (π ≫ sY) C.A C.diag hq (pull_isLB C.isLB _) hP.1
  obtain ⟨A₀, _, φ, hA₀, gp, hφ⟩ := GlobalTheory.T.abelianScheme_descends_galoisCover_noetherian_base o X Y π sY Ga ρ C.A ν hπ hqA C.ab (fun a => (hν a).1) ν1 νm
  obtain ⟨P₀, φ₂, hP₀, sq, iso, norm⟩ := GlobalTheory.T.exists_squareBundle_descent_galoisCover X Y π Ga ρ C.A A₀ φ ν C.P hπ C.ab hA₀ gp hφ (fun a => (hν a).1) ν1 νm
    C.isLB C.rig₁ (fun a => (hν a).2.1)
  have hlev : ∀ a, ∃ x₀ : 𝟙_ (Over Y) ⟶ A₀, (C.lev a ^ (N / n)).left ≫ φ = π ≫ x₀.left := by
    intro a
    obtain ⟨f, hf, -⟩ := hπ.existsUnique_desc ((C.lev a ^ (N / n)).left ≫ φ) (fun g => by
      rw [← Category.assoc, ← (hν g).2.2 a, Category.assoc, hφ.inv g])
    have hf' : f ≫ A₀.hom = 𝟙 Y := by
      have := hπ.fin
      have := hπ.etale
      have := hπ.onto
      have : Epi π := Flat.epi_of_flat_of_surjective _
      rw [← cancel_epi π, ← Category.assoc, hf, Category.assoc, gp.1.w, ← Category.assoc, Over.w]
      simp
    exact ⟨Over.homMk f hf', hf.symm⟩
  choose lev₀ hlev₀ using hlev
  obtain ⟨φ', φ₂', gp', sq', iso', hlev'⟩ := GlobalTheory.T.descendedData_transport_identity_levelChange h n N (N / n) o o' b.ζ ζ' X Y (s' ≫ spMap j) s' C c π A₀ φ φ₂ P₀ lev₀
    hCc gp sq hP₀ iso hlev₀
  obtain ⟨c₀, hpb⟩ := GlobalTheory.T.exists_siegelObject_of_galois_descended_data h n o b.ζ X Y π (s' ≫ spMap j) sY Ga ρ c A₀ φ' φ₂' P₀ lev₀ hbase.symm hπ hA₀ gp' sq' hP₀
    iso' norm hlev'
  have hR : SRel C c₀ (N / n) 1 π := by
    have e := ((GlobalTheory.T.siegelObjectPullbackLevelPower_calculus h n n N o o o' b.ζ b.ζ ζ' Y X X sY (s' ≫ spMap j) s' c₀ c C π (𝟙 X) 1 1 (N / n)
      ((sRel_one_one_iff c c₀ π).2 hpb)).1).1 hCc
    rwa [Category.id_comp] at e
  exact ⟨c₀, GlobalTheory.T.principal_descent_finite_etale_surjective h N n (N / n) 1 o' o ζ' b.ζ X Y s' sY π C c₀ hπ.fin hπ.etale hπ.onto hR hP, hR⟩

end GlobalTheory.PrincipalDescent
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principal_siegel_lower_level_descends_galois : ∀ (h n N : ℕ) (o o' : Type) [CommRing o] [IsNoetherianRing o] [CommRing o'] (b : TBase o n) (ζ' : o') (j : o →+* o') (X Y : Scheme.{0}) (s' : X ⟶ Sp o') (π : X ⟶ Y) (sY : Y ⟶ Sp o) (C : SiegPre h N ζ' s') (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (ν : Ga → (C.A.left ⟶ C.A.left)), N ≠ 0 → IsUnit (N : o') → n ∣ N → j (b.ζ : o) = ζ' ^ (N / n) → π ≫ sY = s' ≫ spMap j → IsGaloisCover Ga ρ π → IsQProjOver (π ≫ sY) → LocallyOfFiniteType sY → C.Principal → ν 1 = 𝟙 _ → (∀ a c, ν (a * c) = ν a ≫ ν c) → (∀ a, SRelBy C C (N / n) (N / n) (ρ a) (ν a)) → ∃ c : SiegPre h n (b.ζ : o) sY, c.Principal ∧ SRel C c (N / n) 1 π := by
  atlas_forward_decl GlobalTheory.PrincipalDescent.principal_descends
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SmoothDescent

theorem smoothOfRelativeDimension_of_etale_cover_noetherian :
    ∀ (K : Type) [CommRing K] [IsNoetherianRing K] (X Y : Scheme.{0}) (π : X ⟶ Y) (s : Y ⟶ Sp K) (d : ℕ), Etale π → Surjective π → LocallyOfFiniteType s → SmoothOfRelativeDimension d (π ≫ s) → SmoothOfRelativeDimension d s := by
  intro K _ _ X Y π s d _ _ _ hd
  have : Smooth (π ≫ s) := SmoothOfRelativeDimension.smooth d _
  have : Smooth s := smooth_of_comp_of_etale_of_surjective π s
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension d) := HasRingHomProperty.instIsZariskiLocalAtSource
  choose n W hW hn using H1.exists_dim s
  have key (y : Y) : n y = d := by
    obtain ⟨x, rfl⟩ := π.surjective y
    have := hn (π x)
    have h₁ : SmoothOfRelativeDimension (0 + n (π x)) ((π ∣_ W (π x)) ≫ (W (π x)).ι ≫ s) := inferInstance
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc] at h₁
    have h₂ : SmoothOfRelativeDimension (0 + d) ((π ⁻¹ᵁ W (π x)).ι ≫ π ≫ s) := inferInstance
    simpa using H1.dim_unique _ h₁ h₂ ⟨x, hW (π x)⟩
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension d) W ?_ fun y => key y ▸ hn y
  rw [← top_le_iff]
  rintro y -
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hW y⟩

end GlobalTheory.SmoothDescent
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothOfRelativeDimension_descent_etaleCover : ∀ (K : Type) [CommRing K] [IsNoetherianRing K] (X Y : Scheme.{0}) (π : X ⟶ Y) (s : Y ⟶ Sp K) (d : ℕ), Etale π → Surjective π → LocallyOfFiniteType s → SmoothOfRelativeDimension d (π ≫ s) → SmoothOfRelativeDimension d s := by
  atlas_forward_decl GlobalTheory.SmoothDescent.smoothOfRelativeDimension_of_etale_cover_noetherian
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.SiegLev

theorem nonempty_sQuot : ∀ (h n N : ℕ) (F : SFam h N (zetaAway N)) (j : cycAway n →+* cycAway N), 3 ≤ n → Odd N → n ∣ N →
    j (zetaAway n) = zetaAway N ^ (N / n) → IsFinite (spMap j) → Etale (spMap j) → Nonempty (SQuot F n (zetaAway n) j) := by
  intro h n N F j hn hN hdvd hj hfin het
  have hn0 : n ≠ 0 := by omega
  have hN0 : N ≠ 0 := by rintro rfl; exact (Nat.not_odd_zero hN)
  haveI : IsDedekindDomain (cycAway n) := GlobalTheory.CycAwayReg.isDedekindDomain_cycAway n
  obtain ⟨Ga, _, _, ρ, ν, h1, hmul, hν1, hνmul, hover, hlow, hfree, htrans⟩ := GlobalTheory.T.siegelFamily_similitudeGroup_action_free_transitive h n N F j hn hN hdvd hj
  have hjf : j.Finite := (IsFinite.SpecMap_iff _).1 hfin
  have hq : IsQProjOver (F.s ≫ spMap j) :=
    (GlobalTheory.isQProjOver_baseChange_and_finite_restrict _ _ j F.X (F.s ≫ spMap j)).2 F.s hjf F.qproj
  obtain ⟨Y, π, sY, hπ, hG, hsep, hft, -⟩ :=
    GlobalTheory.T.exists_galoisCover_quotient_freeFiniteAction (cycAway n) F.X (F.s ≫ spMap j) Ga ρ hq h1 hmul hover hfree
  have hqY : IsQProjOver sY := GlobalTheory.T.isQProjOver_target_galoisCover_noetherian (cycAway n) F.X Y π sY Ga ρ hG hsep hft (by rw [hπ]; exact hq)
  have hsm : SmoothOfRelativeDimension (h * (h + 1) / 2) (π ≫ sY) := by
    rw [hπ]
    haveI := F.smooth
    haveI : SmoothOfRelativeDimension 0 (spMap j) := inferInstance
    have := smoothOfRelativeDimension_comp (h * (h + 1) / 2) 0 F.s (spMap j)
    rwa [Nat.add_zero] at this
  have hsY : SmoothOfRelativeDimension (h * (h + 1) / 2) sY :=
    GlobalTheory.T.smoothOfRelativeDimension_descent_etaleCover (cycAway n) F.X Y π sY _ hG.etale hG.onto hft hsm
  obtain ⟨c, hc, hlowc⟩ := GlobalTheory.T.principal_siegel_lower_level_descends_galois h n N (cycAway n) (cycAway N) (cycBase hn0) (zetaAway N) j F.X Y F.s π sY F.univ
    Ga ρ ν hN0 (isUnit_natCast hN0) hdvd (by rw [cycBase_ζ]; exact hj) hπ hG (by rw [hπ]; exact hq) hft F.princ hν1
    hνmul hlow
  refine ⟨⟨Y, sY, hsY, hqY, c, hc, π, hπ, hG.fin, hG.etale, hG.onto, hlowc, ?_⟩⟩
  intro R _ _ y y' s' c' h₀ h₁ h₂
  obtain ⟨a, rfl⟩ := htrans R y y' s' c' h₀ h₁ h₂
  rw [Category.assoc, hG.inv]

example : ∀ (h n N : ℕ) (F : SFam h N (zetaAway N)) (j : cycAway n →+* cycAway N), 3 ≤ n → Odd N → n ∣ N → j (zetaAway n) = zetaAway N ^ (N / n) → IsFinite (spMap j) → Etale (spMap j) → Nonempty (SQuot F n (zetaAway n) j) := nonempty_sQuot

end GlobalTheory.SiegLev

end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_siegelLevelLoweringQuotientFamily : ∀ (h n N : ℕ) (F : SFam h N (zetaAway N)) (j : cycAway n →+* cycAway N), 3 ≤ n → Odd N → n ∣ N → j (zetaAway n) = zetaAway N ^ (N / n) → IsFinite (spMap j) → Etale (spMap j) → Nonempty (SQuot F n (zetaAway n) j) := by
  first | exact @GlobalTheory.SiegLev.nonempty_sQuot | exact GlobalTheory.SiegLev.nonempty_sQuot | (intros; apply GlobalTheory.SiegLev.nonempty_sQuot <;> assumption)
end
