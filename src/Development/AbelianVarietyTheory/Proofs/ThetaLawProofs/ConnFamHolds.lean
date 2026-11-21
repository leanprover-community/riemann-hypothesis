import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.AtOfNumberField
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyDataNearTwoPrimes
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemNonzeroLocusOfUnit
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyPBOn
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LieBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.GeomIntegralBaseChangeAndLocalization
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.PolarizedFamilyOfThetaUniformization
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaUniformisationComplexAbelianVarieties
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TorusAlgebraicHolds

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_keyData_near_two_primes : Out.Laws → Out.Laws2 → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (Q : Out.PolAV (Sp R)) (p q : PrimeSpectrum R), 1 ≤ Q.g → ∃ r : R, r ∉ p.asIdeal ∧ r ∉ q.asIdeal ∧ ∃ (y : KeyIn (Localization.Away r)) (φ : y.P.A.left ⟶ Q.A.left), PolPB y.P Q (spMap (algebraMap R (Localization.Away r))) φ := by
  first | exact @GlobalTheory.KeyFam.exists_keyIn_near_two | exact GlobalTheory.KeyFam.exists_keyIn_near_two | (intros; apply GlobalTheory.KeyFam.exists_keyIn_near_two <;> assumption)
end

section
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

noncomputable section
namespace GlobalTheory.KeyFam

theorem GeomInt.mvPolynomial {k S : Type} [Field k] [CommRing S] [Algebra k S] (σ : Type) [Finite σ]
    (h : GeomInt k S) : GeomInt k (MvPolynomial σ S) := by
  have h₀ := h.1
  have h₁ : Algebra.Smooth S (MvPolynomial σ S) := ⟨inferInstance, inferInstance⟩
  refine ⟨Algebra.Smooth.comp k S _, fun K _ _ => ?_⟩
  have := h.2 K
  let e₁ : K ⊗[k] MvPolynomial σ S ≃ₐ[k] K ⊗[k] (S ⊗[k] MvPolynomial σ k) :=
    Algebra.TensorProduct.congr AlgEquiv.refl ((MvPolynomial.algebraTensorAlgEquiv k S).symm.restrictScalars k)
  let e₂ : (K ⊗[k] S) ⊗[k] MvPolynomial σ k ≃ₐ[k] K ⊗[k] (S ⊗[k] MvPolynomial σ k) :=
    Algebra.TensorProduct.assoc k k k K S (MvPolynomial σ k)
  let e₃ := MvPolynomial.algebraTensorAlgEquiv (σ := σ) k (K ⊗[k] S)
  exact ((e₁.trans e₂.symm).toMulEquiv.trans e₃.toMulEquiv).isDomain _

theorem exists_univ_scalars {k S : Type} [Field k] [CommRing S] [Algebra k S] (h : GeomInt k S) (s : S →+* ℂ)
    (s₀ : S →ₐ[k] k) (n : ℕ) (a : ℂˣ) (N : Matrix (Fin n) (Fin n) ℂ) (hN : IsUnit N.det) :
    ∃ (S' : Type) (_ : CommRing S') (_ : Algebra k S') (j : S →ₐ[k] S') (s' : S' →+* ℂ) (s₀' : S' →ₐ[k] k)
      (b : S'ˣ) (M : Matrix (Fin n) (Fin n) S'), GeomInt k S' ∧ s'.comp j.toRingHom = s ∧ s₀'.comp j = s₀ ∧
      IsUnit M.det ∧ s' b = a ∧ ∀ i l, s' (M i l) = N i l := by
  let T := MvPolynomial (Option (Fin n × Fin n)) S
  let M₀ : Matrix (Fin n) (Fin n) T := fun i l => MvPolynomial.X (some (i, l))
  let r : T := MvPolynomial.X none * M₀.det
  have key : ∀ {L : Type} [CommRing L] (f : S →+* L) (c : L) (B : Matrix (Fin n) (Fin n) L),
      ∃ F : T →+* L, (∀ z, F (MvPolynomial.C z) = f z) ∧ F (MvPolynomial.X none) = c ∧
        (∀ i l, F (M₀ i l) = B i l) ∧ F r = c * B.det := by
    intro L _ f c B
    let F : T →+* L := MvPolynomial.eval₂Hom f (fun o => o.elim c fun p => B p.1 p.2)
    have h₁ : F (MvPolynomial.X none) = c := MvPolynomial.eval₂Hom_X' _ _ _
    have h₂ : ∀ i l, F (M₀ i l) = B i l := fun i l => MvPolynomial.eval₂Hom_X' _ _ _
    refine ⟨F, fun z => MvPolynomial.eval₂Hom_C _ _ _, h₁, h₂, ?_⟩
    rw [map_mul, h₁, RingHom.map_det]
    congr 2
    ext i l
    exact h₂ i l
  obtain ⟨F, hF₁, hF₂, hF₃, hF₄⟩ := key s a N
  obtain ⟨G, hG₁, -, -, hG₄⟩ := key s₀.toRingHom 1 1
  have uF : IsUnit (F r) := hF₄ ▸ a.isUnit.mul hN
  have uG : IsUnit (G r) := by rw [hG₄]; simp
  have hr : r ≠ 0 := fun e => uG.ne_zero (by rw [e, map_zero])
  let S' := Localization.Away r
  have ur : IsUnit (algebraMap T S' r) := IsLocalization.Away.algebraMap_isUnit r
  rw [map_mul, IsUnit.mul_iff] at ur
  obtain ⟨⟨b, hb⟩, uM⟩ := ur
  let j : S →ₐ[k] S' := (IsScalarTower.toAlgHom k T S').comp (IsScalarTower.toAlgHom k S T)
  have hj : ∀ z, j z = algebraMap T S' (MvPolynomial.C z) := fun _ => rfl
  let g₀ : S' →+* k := IsLocalization.Away.lift r uG
  have hg : ∀ z, g₀ (j z) = s₀ z := fun z => by
    rw [hj, IsLocalization.Away.lift_eq, hG₁]; rfl
  refine ⟨S', inferInstance, inferInstance, j, IsLocalization.Away.lift r uF,
    { g₀ with commutes' := fun c => ?_ }, b, (algebraMap T S').mapMatrix M₀,
    (GlobalTheory.KeyFam.geomInt_baseChange_and_away k k T (h.mvPolynomial _)).2 r hr, RingHom.ext fun z => ?_, AlgHom.ext hg, ?_, ?_, fun i l => ?_⟩
  · change g₀ _ = _
    rw [← j.commutes, hg, s₀.commutes]
  · change IsLocalization.Away.lift r uF (j z) = _
    rw [hj, IsLocalization.Away.lift_eq, hF₁]
  · rwa [← RingHom.map_det]
  · rw [hb, IsLocalization.Away.lift_eq, hF₂]
  · change IsLocalization.Away.lift r uF (algebraMap T S' (M₀ i l)) = _
    rw [IsLocalization.Away.lift_eq, hF₃]

theorem exists_polPB_of_keyPB {R R' : Type} [CommRing R] [CommRing R'] {x' : KeyIn R'} {x : KeyIn R} {f : R →+* R'}
    (h : KeyPB x' x f) : ∃ φ, PolPB x'.P x.P (spMap f) φ := by
  obtain ⟨φ, -, w, hg, -, hp, hw, -⟩ := h
  exact ⟨φ, hp, hg, w, hw⟩

theorem exists_univ_frames : Out.Laws → ∀ (k S : Type) [Field k] [CommRing S] [Algebra k S] (y : KeyIn S) (x : KeyIn ℂ) (s : S →+* ℂ) (φ : x.P.A.left ⟶ y.P.A.left) (s₀ : S →ₐ[k] k), GeomInt k S → PolPB x.P y.P (spMap s) φ → ∃ (S' : Type) (_ : CommRing S') (_ : Algebra k S') (j : S →ₐ[k] S') (y' : KeyIn S') (s' : S' →+* ℂ) (s₀' : S' →ₐ[k] k) (ψ : y'.P.A.left ⟶ y.P.A.left), GeomInt k S' ∧ KeyPB x y' s' ∧ PolPB y'.P y.P (spMap j.toRingHom) ψ ∧ s₀'.comp j = s₀ := by
  intro hL k S _ _ _ y x s φ s₀ hS hφ
  obtain ⟨Q, hg, rig', hr', th', hth', v', hv'⟩ := x
  dsimp only at φ hφ
  obtain ⟨rig, hr, th, hth, v, hv, H⟩ := KeyTf.exists_keyPB_on S ℂ s y Q φ hg hφ.2.1 hφ.1 hφ.2.2
  obtain ⟨a, t, ht, hat, Hid⟩ := (KeyOnPol.main hL ℂ).2 ⟨Q, hg, rig, hr, th, hth, v, hv⟩ rig' hr' th' hth' v' hv'
  choose N hN using fun i => (hv.2 _ (hv'.1 i)).exists
  have := Q.isAb.comm
  have uN : IsUnit (Matrix.det (N : Matrix _ _ ℂ)) :=
    ((LieComb.lieComb_algebra ℂ Q.A Q.g v hv.1).2.2.2.2 N v' hv hN).1 hv'
  obtain ⟨S', _, _, j, s', s₀', b, M, hS', hs, hs₀, uM, hb, hM⟩ := exists_univ_scalars hS s s₀ Q.g a N uN
  obtain ⟨y₁, H₁⟩ := exists_keyPB_ring y j.toRingHom
  have H₂ := KeyCancel.keyPB_cancel _ _ _ y y₁ _ _ s' H₁ (hs ▸ H)
  obtain ⟨ψ, hψ⟩ := exists_polPB_of_keyPB H₁
  have e : Q.g = y₁.P.g := KeyGalDesc.g_eq H₂
  have := y₁.P.isAb.comm
  let M' : Matrix (Fin y₁.P.g) (Fin y₁.P.g) S' := Matrix.reindex (finCongr e) (finCongr e) M
  have uM' : IsUnit M'.det := by rwa [Matrix.det_reindex_self]
  obtain ⟨ex, -, -, -, bas⟩ := LieComb.lieComb_algebra S' y₁.P.A y₁.P.g y₁.v y₁.basis.1
  choose v₁ hv₁ using fun i => (ex (M' i)).exists
  obtain ⟨t₁, ht₁, -, hle⟩ := exists_sec_div y₁.P.A.hom b.inv_mul y₁.th
  refine ⟨S', _, _, j, ⟨y₁.P, y₁.g_pos, y₁.rig, y₁.rig_gen, t₁,
    fun p => (y₁.th_ne p).imp fun z hz => ⟨hz.1, hle hz.2⟩, v₁, (bas M' v₁ y₁.basis hv₁).2 uM'⟩, s', s₀', ψ, hS', ?_, hψ, hs₀⟩
  rw [← RingHom.id_comp s']
  refine keyPB_trans _ _ _ _ _ _ _ _ ?_ Hid
  refine KeyPBScale.keyPB_scale S' ℂ s' y₁.P y₁.g_pos y₁.rig y₁.rig_gen y₁.th y₁.th_ne y₁.v y₁.basis t₁ _ v₁ _ b M' Q e
    hg rig hr th hth v hv t ht v' hv' ht₁ hv₁ (hb ▸ hat) (fun i => ?_) H₂
  convert hN i using 2 with l
  exact hM i l

end GlobalTheory.KeyFam
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaKeyFamily_universal_frames : Out.Laws → ∀ (k S : Type) [Field k] [CommRing S] [Algebra k S] (y : KeyIn S) (x : KeyIn ℂ) (s : S →+* ℂ) (φ : x.P.A.left ⟶ y.P.A.left) (s₀ : S →ₐ[k] k), GeomInt k S → PolPB x.P y.P (spMap s) φ → ∃ (S' : Type) (_ : CommRing S') (_ : Algebra k S') (j : S →ₐ[k] S') (y' : KeyIn S') (s' : S' →+* ℂ) (s₀' : S' →ₐ[k] k) (ψ : y'.P.A.left ⟶ y.P.A.left), GeomInt k S' ∧ KeyPB x y' s' ∧ PolPB y'.P y.P (spMap j.toRingHom) ψ ∧ s₀'.comp j = s₀ := by
  atlas_forward_decl GlobalTheory.KeyFam.exists_univ_frames
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geom_integral_base_change_and_localization : ∀ (K K' R : Type) [Field K] [Field K'] [Algebra K K'] [CommRing R] [Algebra K R], GeomInt K R → GeomInt K' (K' ⊗[K] R) ∧ ∀ r : R, r ≠ 0 → GeomInt K (Localization.Away r) := by
  first | exact @GlobalTheory.KeyFam.geomInt_baseChange_and_away | exact GlobalTheory.KeyFam.geomInt_baseChange_and_away | (intros; apply GlobalTheory.KeyFam.geomInt_baseChange_and_away <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

namespace GlobalTheory.KeyFam.Frames

variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R'']

theorem spMap_comp (f : R →+* R') (f' : R' →+* R'') : spMap (f'.comp f) = spMap f' ≫ spMap f := by
  show Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem polPB_comp {P : Out.PolAV (Sp R)} {P' : Out.PolAV (Sp R')} {P'' : Out.PolAV (Sp R'')} {f : R →+* R'}
    {f' : R' →+* R''} {g : R →+* R''} (e : f'.comp f = g) (h' : ∃ φ', PolPB P'' P' (spMap f') φ')
    (h : ∃ φ, PolPB P' P (spMap f) φ) : ∃ ψ, PolPB P'' P (spMap g) ψ := by
  obtain ⟨φ', hc', hg', w', hw'⟩ := h'
  obtain ⟨φ, hc, hg, w, hw⟩ := h
  subst e
  obtain ⟨w'', T⟩ := exists_comp P'.isLB w w' ((isGen_iff w).1 hw) ((isGen_iff w').1 hw') P.isLB P''.isLB
  exact ⟨φ' ≫ φ, (hc'.comp hc).congr (spMap_comp f f').symm rfl, hg'.trans hg, w'',
    (isGen_iff w'').2 (T.pgen_comp P'.isLB ((isGen_iff w).1 hw) ((isGen_iff w').1 hw'))⟩

theorem polPB_cancel {P : Out.PolAV (Sp R)} {P' : Out.PolAV (Sp R')} {P'' : Out.PolAV (Sp R'')} {f : R →+* R'}
    {f' : R' →+* R''} {g : R →+* R''} (e : f'.comp f = g) (h : ∃ φ, PolPB P' P (spMap f) φ)
    (h'' : ∃ ψ, PolPB P'' P (spMap g) ψ) : ∃ φ', PolPB P'' P' (spMap f') φ' := by
  obtain ⟨φ'', hc'', hg'', w'', hw''⟩ := h''
  obtain ⟨φ, hc, hg, w, hw⟩ := h
  subst e
  have hsp := spMap_comp f f'
  have hp := hc.1
  obtain ⟨φ', hφ, hw0⟩ : ∃ φ' : P''.A.left ⟶ P'.A.left, φ' ≫ φ = φ'' ∧
      φ' ≫ P'.A.hom = P''.A.hom ≫ spMap f' :=
    ⟨hp.lift φ'' (P''.A.hom ≫ spMap f') (by rw [hc''.1.w, Category.assoc, hsp]), hp.lift_fst _ _ _,
      hp.lift_snd _ _ _⟩
  subst hφ
  have g := (isGen_iff w).1 hw
  have g'' := (isGen_iff w'').1 hw''
  obtain ⟨w', T⟩ := exists_cancel P.isLB w w'' g g'' P'.isLB P''.isLB
  exact ⟨φ', hc.cancel (hc''.congr hsp rfl) hw0, hg''.trans hg.symm, w',
    (isGen_iff w').2 (T.pgen_cancel P.isLB g g'')⟩

theorem polPB_exists (hB : Out.PolBaseChangeSt) (P : Out.PolAV (Sp R)) (f : R →+* R') :
    ∃ (P' : Out.PolAV (Sp R')) (φ : P'.A.left ⟶ P.A.left), PolPB P' P (spMap f) φ := by
  obtain ⟨P', φ, hφ, hg, hm, t, ht⟩ := hB _ _ (spMap f) P
  refine ⟨P', φ, ⟨hφ, fun T x y x₀ y₀ hx hy => ?_⟩, hg, LBIso.symm ⟨t, ht⟩⟩
  rw [(Over.OverMorphism.ext hx : x₀ = Out.toBase hφ.w x), (Over.OverMorphism.ext hy : y₀ = Out.toBase hφ.w y), ← hm]
  rfl

theorem polPB_of_keyPB {x : KeyIn R} {x' : KeyIn R'} {f : R →+* R'} (h : KeyPB x' x f) :
    ∃ φ, PolPB x'.P x.P (spMap f) φ :=
  let ⟨φ, _, w, hg, _, hc, hw, _⟩ := h
  ⟨φ, hc, hg, w, hw⟩

theorem exists_points (K K' R : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
    [CommRing R] [Algebra K R] (s : R →+* ℂ) (s₀ : R →ₐ[K] K) :
    ∃ (i : R →+* K' ⊗[K] R) (s' : K' ⊗[K] R →+* ℂ) (s₀' : K' ⊗[K] R →ₐ[K'] K'),
      s'.comp i = s ∧ s₀'.toRingHom.comp i = (algebraMap K K').comp s₀.toRingHom := by
  letI : Algebra K ℂ := (s.comp (algebraMap K R)).toAlgebra
  haveI : Algebra.IsAlgebraic K K' := Algebra.IsAlgebraic.tower_top (K := ℚ) K
  let e : K' →ₐ[K] ℂ := IsAlgClosed.lift
  let sA : R →ₐ[K] ℂ := { s with commutes' := fun _ => rfl }
  refine ⟨Algebra.TensorProduct.includeRight.toRingHom,
    (Algebra.TensorProduct.lift e sA fun _ _ => Commute.all _ _).toRingHom,
    Algebra.TensorProduct.lift (AlgHom.id K' K') ((Algebra.ofId K K').comp s₀) fun _ _ => Commute.all _ _,
    RingHom.ext fun r => ?_, RingHom.ext fun r => ?_⟩
  · simp [sA]
  · simp

end GlobalTheory.KeyFam.Frames

namespace GlobalTheory.KeyFam
open Frames

theorem connFam_of_polFam : Out.Laws → Out.Laws2 → PolFam → GlobalTheory.KeyKa.ConnFam := by
  intro hL hL2 hF x
  obtain ⟨K, _, _, R, _, _, Q, s, s₀, φ, hG, hP, hK⟩ := hF x.P x.g_pos
  obtain ⟨P₀, φ₀, hP₀⟩ := polPB_exists hL.polBaseChange Q s₀.toRingHom
  obtain ⟨K', _, _, j, hKn⟩ := hK P₀ φ₀ hP₀
  letI : Algebra K K' := j.toAlgebra
  obtain ⟨i, s', s₀', hs', hs₀'⟩ := exists_points K K' R s s₀
  obtain ⟨Q', ψ, hQ'⟩ := polPB_exists hL.polBaseChange Q i
  have hG' : GeomInt K' (K' ⊗[K] R) := (GlobalTheory.T.geom_integral_base_change_and_localization K K' R hG).1
  haveI := hG'.1
  haveI : IsNoetherianRing (K' ⊗[K] R) := Algebra.FiniteType.isNoetherianRing K' _
  obtain ⟨r, hr, hr₀, y, χ, hy⟩ := GlobalTheory.T.exists_keyData_near_two_primes hL hL2 (K' ⊗[K] R) Q' ⟨RingHom.ker s', RingHom.ker_isPrime _⟩
    ⟨RingHom.ker s₀'.toRingHom, RingHom.ker_isPrime _⟩ (by rw [hQ'.2.1, ← hP.2.1]; exact x.g_pos)
  have hu : IsUnit (s' r) := isUnit_iff_ne_zero.2 hr
  have hu₀ : IsUnit (s₀'.toRingHom r) := isUnit_iff_ne_zero.2 hr₀
  have hS : GeomInt K' (Localization.Away r) :=
    (GlobalTheory.T.geom_integral_base_change_and_localization K' K' _ hG').2 r fun h => hr (h ▸ Ideal.zero_mem _)
  let t : Localization.Away r →+* ℂ := IsLocalization.Away.lift r hu
  have ht : t.comp (algebraMap _ _) = s' := IsLocalization.Away.lift_comp r hu
  let u : Localization.Away r →+* K' := IsLocalization.Away.lift r hu₀
  have hu' : u.comp (algebraMap _ _) = s₀'.toRingHom := IsLocalization.Away.lift_comp r hu₀
  let t₀ : Localization.Away r →ₐ[K'] K' :=
    { u with
      commutes' := fun a => by
        rw [IsScalarTower.algebraMap_apply K' (K' ⊗[K] R) (Localization.Away r)]
        exact (RingHom.congr_fun hu' _).trans (s₀'.commutes a) }
  have hyQ := polPB_comp rfl ⟨χ, hy⟩ ⟨ψ, hQ'⟩
  obtain ⟨φ₁, hφ₁⟩ := polPB_cancel (f' := t) (by rw [← RingHom.comp_assoc, ht, hs']) hyQ ⟨φ, hP⟩
  obtain ⟨S', _, _, j', y', v, v₀, ψ', hS', hx, hy', hv₀⟩ := GlobalTheory.T.exists_thetaKeyFamily_universal_frames hL K' _ y x t φ₁ t₀ hS hφ₁
  obtain ⟨y₀, hy₀⟩ := exists_keyPB_ring y' v₀.toRingHom
  have e₁ : v₀.toRingHom.comp j'.toRingHom = u := congrArg AlgHom.toRingHom hv₀
  have h₁ := polPB_comp e₁ (polPB_of_keyPB hy₀) ⟨ψ', hy'⟩
  have h₂ := polPB_comp (g := ((RingHom.id K').comp j).comp s₀.toRingHom)
    (by rw [← RingHom.comp_assoc, hu', hs₀']; rfl) h₁ hyQ
  obtain ⟨φ₂, hφ₂⟩ := polPB_cancel rfl ⟨φ₀, hP₀⟩ h₂
  obtain ⟨c, hc⟩ := hKn K' (RingHom.id K') y₀ φ₂ hφ₂
  exact ⟨K', _, ‹_›, S', _, _, y', v, v₀, c, hS'.1, hS'.2, hx, fun e x₀ h =>
    hc e x₀ (KeyCancel.keyPB_cancel _ _ _ y' y₀ x₀ _ _ hy₀ h)⟩

end GlobalTheory.KeyFam
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.keyDatumConnectedFamily_of_polarizedArithmeticFamily : Out.Laws → Out.Laws2 → PolFam → GlobalTheory.KeyKa.ConnFam := by
  atlas_forward_decl GlobalTheory.KeyFam.connFam_of_polFam
end

section
namespace GlobalTheory.KeyFam

theorem connFam_holds : GlobalTheory.KeyKa.ConnFam :=
  GlobalTheory.T.keyDatumConnectedFamily_of_polarizedArithmeticFamily GlobalTheory.abelianSchemeLaws_all.1 GlobalTheory.abelianSchemeLaws_all.2
    (GlobalTheory.T.polarized_family_of_theta_uniformization GlobalTheory.abelianSchemeLaws_all.1 GlobalTheory.abelianSchemeLaws_all.2 GlobalTheory.thetaUnifAV_closed
      GlobalTheory.torusAlgebraic_holds)

end GlobalTheory.KeyFam
end
