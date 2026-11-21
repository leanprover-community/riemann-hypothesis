import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.BlockTheory.AbelianSchemeLaw.SemiAbelianSchemes
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.FrobFieldExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerEqRangeOfRangeEqKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompEqZeroOfNotIsIsogeny
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionTowerAndHeightEqTwoDim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfNormProdAevalEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicativePolynomialFunctionEqNormFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyEndCharpolySpecStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetAevalEqProdArootsCharpolyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegAevalEqProdAroots
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConnectedDieudonneFunctorQuasiLogarithms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleDieudonneBaseByCartierDuality
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualIsConnOfIsEtPDivGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSeriesEvalAtNilpotentXEqCoordinate
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CounitCotangentClassPowerSeriesEvalAtNilpotent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsConnIsEtSplitting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomEqZeroOfIsConnOfIsEt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamVectorExtension

section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.DieuCharpoly

open Polynomial

theorem mem_range_zmod_of_pow_eq_self (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [CharP k p]
    (c : k) (hc : c ^ p = c) : c ∈ Set.range ((ZMod.castHom (dvd_refl p) k)) := by
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  have hroots := FiniteField.roots_X_pow_card_sub_X (ZMod p)
  rw [ZMod.card p] at hroots
  have hdeg : (X ^ p - X : (ZMod p)[X]).natDegree = p := FiniteField.X_pow_card_sub_X_natDegree_eq _ hp
  have hcard : Multiset.card (X ^ p - X : (ZMod p)[X]).roots = (X ^ p - X : (ZMod p)[X]).natDegree := by
    rw [hroots, hdeg, Finset.card_val, Finset.card_univ, ZMod.card]
  have hmap := Polynomial.roots_map_of_injective_of_card_eq_natDegree
    ((ZMod.castHom (dvd_refl p) k)).injective hcard
  have hmem : c ∈ ((X ^ p - X : (ZMod p)[X]).map ((ZMod.castHom (dvd_refl p) k))).roots := by
    rw [Polynomial.mem_roots]
    · simp [hc]
    · simpa using FiniteField.X_pow_card_sub_X_ne_zero k hp
  rw [← hmap, hroots, Multiset.mem_map] at hmem
  obtain ⟨a, -, ha⟩ := hmem
  exact ⟨a, ha⟩

theorem exists_map_eq_of_frobenius_eq (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [CharP k p]
    (x : WittVector p k) (hx : WittVector.frobenius x = x) :
    ∃ y : WittVector p (ZMod p), WittVector.map ((ZMod.castHom (dvd_refl p) k)) y = x := by
  have hc : ∀ n, ∃ a : ZMod p, (ZMod.castHom (dvd_refl p) k) a = x.coeff n := by
    intro n
    have h := congrArg (fun z => z.coeff n) hx
    simp only [WittVector.frobenius_eq_map_frobenius, WittVector.map_coeff, frobenius_def] at h
    exact mem_range_zmod_of_pow_eq_self p _ h
  choose a ha using hc
  refine ⟨WittVector.mk p a, ?_⟩
  ext n
  simp [WittVector.map_coeff, ha]

theorem padicInt_ringHom_ext (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [CharP k p]
    [PerfectRing k p] (f g : ℤ_[p] →+* WittVector p k) : f = g := by
  refine RingHom.ext fun x => ?_
  rw [← sub_eq_zero]
  have hI : Ideal.span {(p : WittVector p k)} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]; exact (WittVector.irreducible p).not_isUnit
  have h := Ideal.iInf_pow_eq_bot_of_isDomain _ hI
  rw [← Ideal.mem_bot, ← h, Ideal.mem_iInf]
  intro m
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec m x)
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  refine ⟨f y - g y, ?_⟩
  have h1 : x = ((x.appr m : ℕ) : ℤ_[p]) + y * (p : ℤ_[p]) ^ m := by rw [hy]; ring
  rw [h1]
  simp only [map_add, map_mul, map_pow, map_natCast]
  ring

end GlobalTheory.DieuCharpoly

namespace GlobalTheory.DieuCharpoly

open Polynomial

theorem charpoly_map_eq_of_commute_semilinear {R : Type} [CommRing R] [IsDomain R]
    (σ : R →+* R) (hσ : Function.Surjective σ) (N : Type) [AddCommGroup N] [Module R N]
    [Module.Free R N] [Module.Finite R N] (F : N →ₛₗ[σ] N) (u : N →ₗ[R] N)
    (hF : Function.Injective F) (hu : ∀ x, u (F x) = F (u x)) :
    u.charpoly.map σ = u.charpoly := by
  classical
  let b := Module.Free.chooseBasis R N
  let U := LinearMap.toMatrix b b u
  let Φ : Matrix _ _ R := fun i j => b.repr (F (b j)) i
  have hFrepr : ∀ x i, b.repr (F x) i = ∑ j, Φ i j * σ (b.repr x j) := by
    intro x i
    conv_lhs => rw [← b.sum_repr x]
    simp only [map_sum, LinearMap.map_smulₛₗ, Finsupp.coe_finset_sum, Finset.sum_apply,
      map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hurepr : ∀ y i, b.repr (u y) i = ∑ l, U i l * b.repr y l := by
    intro y i
    rw [← LinearMap.toMatrix_mulVec_repr b b u y]
    rfl
  have hcomm : U * Φ = Φ * U.map σ := by
    refine Matrix.ext fun i j => ?_
    have h := congrArg (fun z => b.repr z i) (hu (b j))
    rw [hurepr, hFrepr] at h
    rw [Matrix.mul_apply, Matrix.mul_apply]
    refine h.trans (Finset.sum_congr rfl fun l _ => ?_)
    rw [Matrix.map_apply, show U l j = b.repr (u (b j)) l from LinearMap.toMatrix_apply b b u l j]
  have hdet : Φ.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    choose w hw using fun j => hσ (v j)
    let x := b.repr.symm (Finsupp.equivFunOnFinite.symm w)
    have hx : ∀ j, b.repr x j = w j := by simp [x]
    have hFx : F x = 0 := by
      apply b.repr.injective
      refine Finsupp.ext fun i => ?_
      rw [hFrepr, map_zero, Finsupp.coe_zero, Pi.zero_apply]
      have := congrFun hv i
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at this
      rw [← this]
      exact Finset.sum_congr rfl fun j _ => by rw [hx, hw]
    have hx0 : x = 0 := hF (by rw [hFx, map_zero])
    apply hv0
    funext j
    rw [← hw j, Pi.zero_apply, ← hx j, hx0, map_zero, Finsupp.coe_zero, Pi.zero_apply, map_zero]
  rw [← LinearMap.charpoly_toMatrix u b, ← Matrix.charpoly_map]
  have hm : U.charmatrix * (Polynomial.C : R →+* _).mapMatrix Φ =
      (Polynomial.C : R →+* _).mapMatrix Φ * (U.map σ).charmatrix := by
    rw [Matrix.charmatrix, Matrix.charmatrix, sub_mul, mul_sub, ← map_mul, hcomm, map_mul,
      (Matrix.scalar_commute _ (fun _ => Commute.all _ _) _).eq]
  have hd := congrArg Matrix.det hm
  rw [Matrix.det_mul, Matrix.det_mul, ← RingHom.map_det] at hd
  have hC : Polynomial.C Φ.det ≠ 0 := Polynomial.C_ne_zero.2 hdet
  rw [mul_comm] at hd
  exact (mul_left_cancel₀ hC hd).symm

end GlobalTheory.DieuCharpoly

namespace GlobalTheory.DieuCharpoly

open Polynomial

theorem exists_monic_map_eq_charpoly : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    [PerfectRing k p] (N : Type) [AddCommGroup N] [Module (WittVector p k) N]
    [Module.Free (WittVector p k) N] [Module.Finite (WittVector p k) N]
    (F : N →ₛₗ[(WittVector.frobenius : WittVector p k →+* WittVector p k)] N)
    (ψ : ℤ_[p] →+* (WittVector p k)) (u : N →ₗ[(WittVector p k)] N),
    Function.Injective F → (∀ x, u (F x) = F (u x)) →
      ∃ P : Polynomial ℤ_[p], P.Monic ∧ P.map ψ = u.charpoly := by
  intro p _ k _ _ _ N _ _ _ _ F ψ u hF hu
  have hfix := charpoly_map_eq_of_commute_semilinear _
    (WittVector.frobenius_bijective p k).surjective N F u hF hu
  have hψ : ψ = (WittVector.map (ZMod.castHom (dvd_refl p) k)).comp
      (WittVector.equiv p).symm.toRingHom := padicInt_ringHom_ext p _ _
  have hl : u.charpoly ∈ Polynomial.lifts ψ := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    have h : WittVector.frobenius (u.charpoly.coeff n) = u.charpoly.coeff n := by
      conv_rhs => rw [← hfix]
      rw [Polynomial.coeff_map]
    obtain ⟨y, hy⟩ := exists_map_eq_of_frobenius_eq p _ h
    refine ⟨WittVector.equiv p y, ?_⟩
    rw [hψ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingEquiv.symm_apply_apply, hy]
  obtain ⟨P, hP, -, hPm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl (LinearMap.charpoly_monic u)
  exact ⟨P, hPm, hP⟩

end GlobalTheory.DieuCharpoly
end

section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_padicInt_charpoly_commute_frobeniusSemilinear : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (N : Type) [AddCommGroup N] [Module (WittVector p k) N] [Module.Free (WittVector p k) N] [Module.Finite (WittVector p k) N] (F : N →ₛₗ[(WittVector.frobenius : WittVector p k →+* WittVector p k)] N) (ψ : ℤ_[p] →+* (WittVector p k)) (u : N →ₗ[(WittVector p k)] N), Function.Injective F → (∀ x, u (F x) = F (u x)) → ∃ P : Polynomial ℤ_[p], P.Monic ∧ P.map ψ = u.charpoly := by
  first | exact @GlobalTheory.DieuCharpoly.exists_monic_map_eq_charpoly | exact GlobalTheory.DieuCharpoly.exists_monic_map_eq_charpoly | (intros; apply GlobalTheory.DieuCharpoly.exists_monic_map_eq_charpoly; all_goals assumption)
end

section
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.AV GlobalTheory.AV.AbVar
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torsionTower_and_height_eq_two_dim : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] (A : AbVar k), (∃ G : PDivGroup p k, Nonempty (G.TorsionTower A.X)) ∧ ∀ (G : PDivGroup p k) (t : G.TorsionTower A.X), G.height = 2 * A.dim := by
  first | exact @GlobalTheory.AVTower.exists_tower_and_height_eq | exact GlobalTheory.AVTower.exists_tower_and_height_eq | (intros; apply GlobalTheory.AVTower.exists_tower_and_height_eq <;> assumption)
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_of_norm_prod_aeval_eq' : ∀ (l : ℕ) [Fact l.Prime] (P Q : Polynomial ℚ_[l]), P.Monic → Q.Monic → P.natDegree = Q.natDegree → (∀ F : Polynomial ℤ, ‖((P.aroots (PadicAlgCl l)).map (fun a => Polynomial.aeval a F)).prod‖ = ‖((Q.aroots (PadicAlgCl l)).map (fun a => Polynomial.aeval a F)).prod‖) → P = Q := by
  first | exact @GlobalTheory.PadicRootNorm.eq_of_norm_prod_aeval_eq | exact GlobalTheory.PadicRootNorm.eq_of_norm_prod_aeval_eq | (intros; apply GlobalTheory.PadicRootNorm.eq_of_norm_prod_aeval_eq; all_goals assumption)
end

section
section
namespace GlobalTheory
open Polynomial

theorem aeval_int_eq_eval₂ {A : Type} [Ring A] [inst : Algebra ℤ A] (x : A) (R : ℤ[X]) :
    @aeval ℤ A _ _ inst x R = eval₂ (Int.castRingHom A) x R := by
  rw [aeval_def]
  congr 1
  exact RingHom.ext_int _ _

theorem prod_aeval_aroots_padic_eq_det : ∀ (p : ℕ) [Fact p.Prime] (S : Type) [CommRing S] [IsDomain S] (N : Type) [AddCommGroup N] [Module S N] [Module.Free S N] [Module.Finite S N] (ψ : ℤ_[p] →+* S) (u : N →ₗ[S] N) (P : Polynomial ℤ_[p]) (R : Polynomial ℤ) (d : ℤ_[p]), Function.Injective ψ → P.map ψ = u.charpoly → LinearMap.det (Polynomial.aeval u R) = ψ d → (((P.map (algebraMap ℤ_[p] ℚ_[p])).aroots (PadicAlgCl p)).map (fun a => Polynomial.aeval a R)).prod = algebraMap ℚ_[p] (PadicAlgCl p) (d : ℚ_[p]) := by
  intro p _ S _ _ N _ _ _ _ ψ u P R d hψ hP hd
  let K := FractionRing S
  have hg : Function.Injective ((algebraMap S K).comp ψ) :=
    (IsFractionRing.injective S K).comp hψ
  let ψ' : ℚ_[p] →+* K := IsFractionRing.lift hg
  have hψ' : ψ'.comp (algebraMap ℤ_[p] ℚ_[p]) = (algebraMap S K).comp ψ :=
    IsLocalization.lift_comp _
  let Ω := AlgebraicClosure K
  letI : Algebra ℚ_[p] Ω := ((algebraMap K Ω).comp ψ').toAlgebra
  have hΩ : algebraMap ℚ_[p] Ω = (algebraMap K Ω).comp ψ' := rfl
  let j : PadicAlgCl p →ₐ[ℚ_[p]] Ω := IsAlgClosed.lift
  have hj : Function.Injective j := j.toRingHom.injective
  let uK : Module.End K (TensorProduct S K N) := u.baseChange K
  have key := GlobalTheory.T.det_aeval_eq_prod_aroots_charpoly' K Ω (TensorProduct S K N) uK (R.map (Int.castRingHom K))
  have hF : ∀ {A : Type} [Ring A] [Algebra K A] (x : A), aeval x (R.map (Int.castRingHom K)) = aeval x R := by
    intro A _ _ x
    rw [← algebraMap_int_eq, aeval_map_algebraMap]
  simp only [hF] at key
  have hbc : aeval uK R = (aeval u R).baseChange K := by
    have := aeval_algHom_apply (Module.End.baseChangeHom S K N).toRingHom.toIntAlgHom u R
    exact this
  rw [hbc, LinearMap.det_baseChange, hd] at key
  have hch : uK.charpoly.aroots Ω = (P.map (algebraMap ℤ_[p] ℚ_[p])).aroots Ω := by
    rw [LinearMap.charpoly_baseChange, ← hP, aroots_def, aroots_def, map_map, map_map, map_map, hΩ]
    simp only [RingHom.comp_assoc, hψ']
  rw [hch] at key
  apply hj
  set Q := P.map (algebraMap ℤ_[p] ℚ_[p])
  have hroots : Q.aroots Ω = (Q.aroots (PadicAlgCl p)).map j := by
    have h := (IsAlgClosed.splits (Q.map (algebraMap ℚ_[p] (PadicAlgCl p)))).roots_map (j : PadicAlgCl p →+* Ω)
    rw [map_map, AlgHom.comp_algebraMap] at h
    rw [aroots_def, aroots_def, h]
    rfl
  rw [hroots, Multiset.map_map] at key
  rw [map_multiset_prod, Multiset.map_map, AlgHom.commutes]
  simp only [aeval_int_eq_eval₂] at key ⊢
  have e1 : ∀ a : PadicAlgCl p, j (eval₂ (Int.castRingHom _) a R) = eval₂ (Int.castRingHom Ω) (j a) R := by
    intro a
    change (j : PadicAlgCl p →+* Ω) (eval₂ (Int.castRingHom _) a R) = _
    rw [Polynomial.hom_eval₂]
    congr 1
    exact RingHom.ext_int _ _
  simp only [Function.comp_def, e1] at key ⊢
  refine key.symm.trans ?_
  rw [hΩ, RingHom.comp_apply]
  congr 1
  exact (RingHom.congr_fun hψ' d).symm

end GlobalTheory
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prod_aeval_padicRoots_charpoly_eq_det : ∀ (p : ℕ) [Fact p.Prime] (S : Type) [CommRing S] [IsDomain S] (N : Type) [AddCommGroup N] [Module S N] [Module.Free S N] [Module.Finite S N] (ψ : ℤ_[p] →+* S) (u : N →ₗ[S] N) (P : Polynomial ℤ_[p]) (R : Polynomial ℤ) (d : ℤ_[p]), Function.Injective ψ → P.map ψ = u.charpoly → LinearMap.det (Polynomial.aeval u R) = ψ d → (((P.map (algebraMap ℤ_[p] ℚ_[p])).aroots (PadicAlgCl p)).map (fun a => Polynomial.aeval a R)).prod = algebraMap ℚ_[p] (PadicAlgCl p) (d : ℚ_[p]) := by
  atlas_forward_decl GlobalTheory.prod_aeval_aroots_padic_eq_det
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deg_aeval_end_eq_prod_aroots : ∀ (K : Type) [Field K] (A : AbVar K) (f : End A) (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra ℚ Ω] (R : Polynomial ℤ), algebraMap ℚ Ω (deg (A := A) (B := A) (Polynomial.aeval f R) : ℚ) = ((((charpoly f).map (Int.castRingHom ℚ)).aroots Ω).map (fun a => Polynomial.aeval a R)).prod := by
  first | exact @GlobalTheory.AV.AbVar.deg_aeval_eq_prod_aroots | exact GlobalTheory.AV.AbVar.deg_aeval_eq_prod_aroots | (intros; apply GlobalTheory.AV.AbVar.deg_aeval_eq_prod_aroots <;> assumption)
end

section
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.AV GlobalTheory.AV.AbVar
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj CategoryTheory.MonObj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Dieu.CharpolyAV

section Rho

variable {p : ℕ} [Fact p.Prime] (T : Theory p) {k : Type} [Field k] [CharP k p] [PerfectRing k p]
  {A : AbVar k} {G : PDivGroup p k} (t : G.TorsionTower A.X)

def rho : End A →+ Module.End (WittVector p k) (T.M G) :=
  AddMonoidHom.mk' (fun g => T.map (t.map t (Hom.hom g))) fun g h => by
    have hfun := base_functor_props p (fun _ _ _ => True) T.base k G G G trivial trivial trivial
    haveI : IsMonHom (Hom.hom g * Hom.hom h) := inferInstanceAs (IsMonHom (Hom.hom (g + h)))
    show T.map (t.map t (Hom.hom g * Hom.hom h)) = _
    rw [TorsionTower.map_mul]
    exact hfun.2.2.1 _ _

theorem rho_apply (g : End A) : rho T t g = T.map (t.map t (Hom.hom g)) := rfl

theorem rho_pow (f : End A) (n : ℕ) : rho T t (f ^ n) = rho T t f ^ n := by
  have hfun := base_functor_props p (fun _ _ _ => True) T.base k G G G trivial trivial trivial
  induction n with
  | zero =>
    rw [pow_zero, pow_zero, rho_apply]
    show T.map (t.map t (𝟙 A.X)) = _
    rw [TorsionTower.map_id]
    exact hfun.1
  | succ n ih =>
    rw [pow_succ, pow_succ', ← ih, rho_apply, rho_apply, rho_apply]
    show T.map (t.map t (Hom.hom f ≫ Hom.hom (f ^ n))) = _
    rw [TorsionTower.map_comp t t t]
    exact hfun.2.1 _ _

theorem rho_aeval (f : End A) (R : Polynomial ℤ) :
    rho T t (Polynomial.aeval f R) = Polynomial.aeval (rho T t f) R := by
  induction R using Polynomial.induction_on' with
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]
  | monomial n a =>
    rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, eq_intCast (algebraMap ℤ (End A)),
      eq_intCast (algebraMap ℤ (Module.End (WittVector p k) (T.M G))), ← zsmul_eq_mul, ← zsmul_eq_mul, map_zsmul, rho_pow]

end Rho

theorem charpoly_map_eq : ∀ (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k] [CharP k p] [PerfectRing k p] (A : AbVar k) (G : PDivGroup p k) (t : G.TorsionTower A.X) [Module.Free (WittVector p k) (T.M G)] [Module.Finite (WittVector p k) (T.M G)] (f : End A), (T.map (t.map t (Hom.hom f))).charpoly = (charpoly f).map (Int.castRingHom (WittVector p k)) := by
  intro p _ T k _ _ _ A G t _ _ f
  have hfun := base_functor_props p (fun _ _ _ => True) T.base k G G G trivial trivial trivial
  have hFc : ∀ (g : End A) (x : T.M G), T.map (t.map t (Hom.hom g)) (T.F G x) = T.F G (T.map (t.map t (Hom.hom g)) x) :=
    fun g x => hfun.2.2.2.2.2.2.1 _ x
  have hFinj : Function.Injective (T.F G) := (GlobalTheory.T.dieudonneTheory_V_eq_verschiebung_injective p T k G).1
  let ψ : ℤ_[p] →+* WittVector p k :=
    (WittVector.map (ZMod.castHom (dvd_refl p) k)).comp (WittVector.equiv p).symm.toRingHom
  have hψ : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hx0
    rw [PadicInt.unitCoeff_spec hx0, map_mul, map_pow, map_natCast] at hx
    have hu : IsUnit (ψ (PadicInt.unitCoeff hx0 : ℤ_[p])) := (Units.isUnit _).map ψ
    have hpn : ((p : WittVector p k)) ^ x.valuation ≠ 0 := pow_ne_zero _ (WittVector.p_nonzero p k)
    exact hpn ((hu.mul_right_eq_zero).1 hx)
  have hrank : Module.finrank (WittVector p k) (T.M G) = 2 * A.dim :=
    hfun.2.2.2.2.2.2.2.1.trans ((GlobalTheory.T.exists_torsionTower_and_height_eq_two_dim p k A).2 G t)
  obtain ⟨P, hPm, hP⟩ := GlobalTheory.T.exists_padicInt_charpoly_commute_frobeniusSemilinear p k (T.M G) (T.F G) ψ (T.map (t.map t (Hom.hom f))) hFinj (hFc f)
  obtain ⟨⟨hQm, hQdeg, -⟩, -⟩ := GlobalTheory.T.abelianVarietyEndCharpoly_spec k A f
  have hPdeg : P.natDegree = 2 * A.dim := by
    rw [← hPm.natDegree_map ψ, hP, LinearMap.charpoly_natDegree, hrank]
  have key : P.map (algebraMap ℤ_[p] ℚ_[p]) = (charpoly f).map (Int.castRingHom ℚ_[p]) := by
    refine GlobalTheory.T.eq_of_norm_prod_aeval_eq' p _ _ (hPm.map _) (hQm.map _) ?_ ?_
    · rw [hPm.natDegree_map, hQm.natDegree_map, hPdeg, hQdeg]
    · intro R
      obtain ⟨PR, -, hPR⟩ := GlobalTheory.T.exists_padicInt_charpoly_commute_frobeniusSemilinear p k (T.M G) (T.F G) ψ
        (T.map (t.map t (Hom.hom (Polynomial.aeval f R)))) hFinj (hFc _)
      set d : ℤ_[p] := (-1) ^ Module.finrank (WittVector p k) (T.M G) * PR.coeff 0 with hd_def
      have hd : LinearMap.det (T.map (t.map t (Hom.hom (Polynomial.aeval f R)))) = ψ d := by
        rw [LinearMap.det_eq_sign_charpoly_coeff, ← hPR, Polynomial.coeff_map, hd_def, map_mul, map_pow,
          map_neg, map_one]
      have habs := GlobalTheory.Dieu.AbsDet.norm_det_eq_norm_deg p T k A G t ψ (Polynomial.aeval f R) d hd
      have hd' : LinearMap.det (Polynomial.aeval (T.map (t.map t (Hom.hom f))) R) = ψ d := by
        rw [← hd]; exact congrArg LinearMap.det (rho_aeval T t f R).symm
      rw [GlobalTheory.T.prod_aeval_padicRoots_charpoly_eq_det p (WittVector p k) (T.M G) ψ _ P R d hψ hP hd']
      have hQ : (charpoly f).map (Int.castRingHom ℚ_[p]) =
          ((charpoly f).map (Int.castRingHom ℚ)).map (algebraMap ℚ ℚ_[p]) := by
        rw [Polynomial.map_map]; congr 1 <;> exact RingHom.ext_int _ _
      have h2 := GlobalTheory.T.deg_aeval_end_eq_prod_aroots k A f (PadicAlgCl p) R
      rw [hQ, Polynomial.aroots_map]
      erw [← h2]
      rw [PadicAlgCl.norm_extends, map_natCast, ← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)), PadicAlgCl.norm_extends]
      rw [PadicInt.padic_norm_e_of_padicInt, habs]
      rw [← PadicInt.padic_norm_e_of_padicInt]; push_cast; rfl
  have hP' : P = (charpoly f).map (Int.castRingHom ℤ_[p]) := by
    apply Polynomial.map_injective (algebraMap ℤ_[p] ℚ_[p]) (IsFractionRing.injective ℤ_[p] ℚ_[p])
    rw [key, Polynomial.map_map]; congr 1 <;> exact RingHom.ext_int _ _
  rw [← hP, hP', Polynomial.map_map]; congr 1 <;> exact RingHom.ext_int _ _

end GlobalTheory.Dieu.CharpolyAV
end
end

section
open CategoryTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_connected_dieudonne_functor_quasiLogarithms : ∀ (p : ℕ) [Fact p.Prime], ∃ B : GlobalTheory.Dieu.Base p (fun _ _ G => G.IsConn), B.Katz := by
  first | (exact @GlobalTheory.exists_base_isConn_katz) | (exact GlobalTheory.exists_base_isConn_katz) | (intros; apply GlobalTheory.exists_base_isConn_katz  <;> assumption)
end

section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory

theorem mvPowerSeries_algHom_isNilpotent_of_constantCoeff_zero :
    ∀ (k : Type) [CommRing k] (σ : Type) [Finite σ] (A : Type) [CommRing A] [Algebra k A],
      ∀ φ : MvPowerSeries σ k →ₐ[k] A, (∀ i, IsNilpotent (φ (X i))) →
        ∀ a : MvPowerSeries σ k, constantCoeff a = 0 → IsNilpotent (φ a) := by
  intro k _ σ _ A _ _ φ hφ a ha
  classical
  haveI := Fintype.ofFinite σ
  have hc : ∀ α : σ →₀ ℕ, ∃ o : Option σ, (α = 0 ∧ o = none) ∨ ∃ i, o = some i ∧ α i ≠ 0 := by
    intro α
    by_cases h : α = 0
    · exact ⟨none, Or.inl ⟨h, rfl⟩⟩
    · obtain ⟨i, hi⟩ := Finsupp.ne_iff.1 h
      exact ⟨some i, Or.inr ⟨i, rfl, by simpa using hi⟩⟩
  choose c hc using hc
  let g : σ → MvPowerSeries σ k := fun i α => if c α = some i then coeff α a else 0
  have hg : ∀ i α, coeff α (g i) = if c α = some i then coeff α a else 0 := fun _ _ => rfl
  have hsum : a = ∑ i, g i := by
    ext α
    rw [map_sum]
    simp only [hg]
    rcases hc α with ⟨h0, h1⟩ | ⟨i, h1, -⟩
    · rw [h1, h0]
      simpa using ha
    · rw [h1]
      simp
  rw [hsum, map_sum]
  refine isNilpotent_sum fun i _ => ?_
  have hd : (X i : MvPowerSeries σ k) ∣ g i := by
    rw [X_dvd_iff]
    intro m hm
    rw [hg, if_neg]
    intro h
    rcases hc m with ⟨-, h1⟩ | ⟨j, h1, h2⟩
    · rw [h1] at h; cases h
    · rw [h1] at h
      cases h
      exact h2 hm
  obtain ⟨b, hb⟩ := hd
  rw [hb, map_mul]
  exact (Commute.all _ _).isNilpotent_mul_right (hφ i)

end GlobalTheory
end

section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Dieu

theorem isConn_of_chart {p : ℕ} {k : Type} [CommRing k] (G : PDivGroup p k) {d : ℕ}
    (c : Katz.Chart G d) : G.IsConn := by
  intro n a ha
  obtain ⟨f, rfl⟩ := c.presents.1 n a
  have h0 : Coalgebra.counit (R := k) (Katz.evA k (c.x n) (c.nil n) f) = 0 := by
    have := RingHom.mem_ker.1 ha
    simpa using this
  have hf : MvPowerSeries.constantCoeff f = 0 := by
    rw [← (Katz.counit_dUnit_evA k d (G.A n) (c.x n) (c.nil n) (c.aug n) f).1]; exact h0
  exact mvPowerSeries_algHom_isNilpotent_of_constantCoeff_zero k (Fin d) (G.A n)
    (Katz.evA k (c.x n) (c.nil n)) (fun i => by rw [Katz.evA_X]; exact c.nil n i) f hf

end GlobalTheory.Dieu

namespace GlobalTheory.Dieu

theorem katz_etDual_of_iso : ∀ (p : ℕ) [Fact p.Prime] (B : Base p (fun _ _ G => G.IsConn))
    (C : Base p (fun _ _ G => G.IsEt)) (D : Base p (fun _ _ _ => True)), B.Katz → C.EtDual B →
    (∃ e : ∀ {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k) (h : G.IsConn),
      D.M G trivial ≃ₗ[WittVector p k] B.M G h, ∀ (k k' : Type) [Field k] [CharP k p] [PerfectRing k p]
      [Field k'] [CharP k' p] [PerfectRing k' p] (σ : k →+* k') (G' : PDivGroup p k') (G : PDivGroup p k)
      (h' : G'.IsConn) (h : G.IsConn) (s : SemiHom σ G' G) (m : D.M G trivial),
      e G' h' (D.smap trivial trivial s m) = B.smap h' h s (e G h m)) →
    (∃ e : ∀ {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k) (h : G.IsEt),
      D.M G trivial ≃ₗ[WittVector p k] C.M G h, ∀ (k k' : Type) [Field k] [CharP k p] [PerfectRing k p]
      [Field k'] [CharP k' p] [PerfectRing k' p] (σ : k →+* k') (G' : PDivGroup p k') (G : PDivGroup p k)
      (h' : G'.IsEt) (h : G.IsEt) (s : SemiHom σ G' G) (m : D.M G trivial),
      e G' h' (D.smap trivial trivial s m) = C.smap h' h s (e G h m)) →
    D.Katz ∧ D.EtDual D := by
  intro p _ B C D hB hC ⟨eB, neB⟩ ⟨eC, neC⟩
  obtain ⟨κ, hκ⟩ := hB
  obtain ⟨δ, hδ⟩ := hC

  have FB : ∀ {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k) (h : G.IsConn)
      (t : True) (m : D.M G trivial), eB G h (D.F G t m) = B.F G h (eB G h m) := fun G h _ m =>
    neB _ _ _ G G h h _ m
  have FC : ∀ {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k) (h : G.IsEt)
      (t : True) (m : D.M G trivial), eC G h (D.F G t m) = C.F G h (eC G h m) := fun G h _ m =>
    neC _ _ _ G G h h _ m
  have MB : ∀ {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G H : PDivGroup p k) (h : G.IsConn)
      (h' : H.IsConn) (f : G ⟶ H) (t t' : True) (m : D.M H trivial),
      eB G h (D.map t t' f m) = B.map h h' f (eB H h' m) := fun G H h h' f _ _ m =>
    neB _ _ _ G H h h' _ m
  have MC : ∀ {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G H : PDivGroup p k) (h : G.IsEt)
      (h' : H.IsEt) (f : G ⟶ H) (t t' : True) (m : D.M H trivial),
      eC G h (D.map t t' f m) = C.map h h' f (eC H h' m) := fun G H h h' f _ _ m =>
    neC _ _ _ G H h h' _ m
  refine ⟨⟨fun {_} _ _ _ G _ {_} c {_} hμ hc => (eB G (isConn_of_chart G c)).trans (κ G _ c hμ hc), ?_⟩,
    ⟨fun G _ _ hG => (eC G hG).trans ((δ G hG (PDivGroup.dual_isConn_of_isEt p _ G hG) hG).trans
      (eB G.dual (PDivGroup.dual_isConn_of_isEt p _ G hG)).dualMap), ?_⟩⟩
  · intro k _ _ _ G _ d c μ hμ hc
    obtain ⟨h1, h2⟩ := hκ G (isConn_of_chart G c) c hμ hc
    refine ⟨?_, ?_⟩
    · convert h1 using 1
      funext x
      rw [LinearEquiv.trans_apply, LinearEquiv.symm_trans_apply, FB, LinearEquiv.apply_symm_apply]
    · intro H _ d' c' ν hν hc' f φ hφ hm
      convert h2 H (isConn_of_chart H c') c' hν hc' f φ hφ hm using 1
      funext x
      rw [LinearEquiv.trans_apply, LinearEquiv.symm_trans_apply,
        MB G H (isConn_of_chart G c) (isConn_of_chart H c'), LinearEquiv.apply_symm_apply]
  · intro k _ _ _ G _ _ hG
    obtain ⟨h1, h2⟩ := hδ G hG (PDivGroup.dual_isConn_of_isEt p _ G hG) hG
    refine ⟨fun x y => ?_, fun H _ _ hH f x y => ?_⟩
    · simp only [LinearEquiv.trans_apply, LinearEquiv.dualMap_apply, FB, FC]
      exact h1 _ _
    · obtain ⟨-, h3⟩ := hδ H hH (PDivGroup.dual_isConn_of_isEt p _ H hH) hH
      simp only [LinearEquiv.trans_apply, LinearEquiv.dualMap_apply]
      rw [MC G H hG hH f, MB H.dual G.dual (PDivGroup.dual_isConn_of_isEt p _ H hH)
        (PDivGroup.dual_isConn_of_isEt p _ G hG) (G.dualHom H f)]
      exact h2 H hH _ hH f _ _

end GlobalTheory.Dieu
end
end

section
section
open CategoryTheory GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

open TensorProduct Coalgebra Bialgebra WithConv

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

theorem PDivGroup.semiHom_app_eq_conn_part :
    ∀ (p : ℕ) [Fact p.Prime] (k k' : Type) [Field k] [CharP k p] [PerfectRing k p]
    [Field k'] [CharP k' p] [PerfectRing k' p] (σ : k →+* k') (G' G'₀ G'₁ : PDivGroup p k') (C : PDivGroup p k)
    (i₀ : G'₀ ⟶ G') (q₀ : G' ⟶ G'₀) (i₁ : G'₁ ⟶ G') (q₁ : G' ⟶ G'₁), G'₁.IsEt → C.IsConn →
    q₀ ≫ i₀ + q₁ ≫ i₁ = 𝟙 G' → ∀ (x : SemiHom σ G' C) (n : ℕ) (a : C.A n),
      q₀.app n (i₀.app n (x.app n a)) = x.app n a := by
  intro p _ k k' _ _ _ _ _ _ σ G' G'₀ G'₁ C i₀ q₀ i₁ q₁ hEt hConn hsplit x n a
  have h1 : ∀ c : C.A n,
      i₁.app n (x.app n c) = algebraMap k' (G'₁.A n) (σ (counit (R := k) c)) := by
    intro c
    haveI := hEt n
    have hmem : c - algebraMap k (C.A n) (counit (R := k) c) ∈ augIdeal k (C.A n) := by
      rw [mem_augIdeal_iff', map_sub, ← Bialgebra.counitAlgHom_apply (R := k),
        ← Bialgebra.counitAlgHom_apply (R := k), AlgHom.commutes, Algebra.algebraMap_self,
        RingHom.id_apply, sub_self]
    have h := (((hConn n _ hmem).map (x.app n).toRingHom).map (i₁.app n)).eq_zero
    change i₁.app n (x.app n (c - _)) = 0 at h
    rw [map_sub, SemiBialgHom.map_algebraMap, map_sub, AlgHomClass.commutes, sub_eq_zero] at h
    exact h
  have hP₁ : ∀ c : C.A n, (q₁ ≫ i₁).app n (x.app n c) =
      algebraMap k' (G'.A n) (σ (counit (R := k) c)) := by
    intro c
    rw [comp_app, BialgHom.comp_apply, h1, AlgHomClass.commutes]
  have hid : ∀ b : G'.A n, ((q₀ ≫ i₀).conv n * (q₁ ≫ i₁).conv n).ofConv b = b := by
    intro b
    have h := congrArg (fun f : G' ⟶ G' => f.app n b) hsplit
    exact h
  have key : ∀ c : C.A n ⊗[k] C.A n,
      Algebra.TensorProduct.lift ((q₀ ≫ i₀).app n : G'.A n →ₐ[k'] G'.A n)
        ((q₁ ≫ i₁).app n : G'.A n →ₐ[k'] G'.A n) (fun _ _ => .all _ _) ((x.app n).two c) =
      (q₀ ≫ i₀).app n (x.app n (TensorProduct.rid k (C.A n)
        (LinearMap.lTensor (C.A n) (counit (R := k)) c))) := by
    intro c
    induction c with
    | zero => simp
    | add c d hc hd => simp only [map_add, hc, hd]
    | tmul b c =>
      rw [TensorProduct.map_tmul, Algebra.TensorProduct.lift_tmul, LinearMap.lTensor_tmul,
        TensorProduct.rid_tmul, SemiBialgHom.lin_apply, SemiBialgHom.lin_apply]
      change _ * (q₁ ≫ i₁).app n (x.app n c) = _
      rw [hP₁, (x.app n).smul_map, map_smul, Algebra.smul_def, mul_comm]
      rfl
  have e : (toPts ((q₀ ≫ i₀).conv n * (q₁ ≫ i₁).conv n)).ofConv (x.app n a) = x.app n a :=
    hid (x.app n a)
  rw [map_mul, AlgHom.convMul_apply, toPts_ofConv, toPts_ofConv, ← (x.app n).two_comul] at e
  have e2 := key (comul (R := k) a)
  rw [Coalgebra.lTensor_counit_comul, TensorProduct.rid_tmul, one_smul] at e2
  exact e2.symm.trans e

end GlobalTheory
end
end

open CategoryTheory GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semilinearHom_connected_factor_through_part : ∀ (p : ℕ) [Fact p.Prime] (k k' : Type) [Field k] [CharP k p] [PerfectRing k p]
    [Field k'] [CharP k' p] [PerfectRing k' p] (σ : k →+* k') (G' G'₀ G'₁ : PDivGroup p k') (C : PDivGroup p k)
    (i₀ : G'₀ ⟶ G') (q₀ : G' ⟶ G'₀) (i₁ : G'₁ ⟶ G') (q₁ : G' ⟶ G'₁), G'₁.IsEt → C.IsConn →
    q₀ ≫ i₀ + q₁ ≫ i₁ = 𝟙 G' → ∀ (x : SemiHom σ G' C) (n : ℕ) (a : C.A n),
      q₀.app n (i₀.app n (x.app n a)) = x.app n a := by
  atlas_forward_decl GlobalTheory.PDivGroup.semiHom_app_eq_conn_part
end

section
section
open CategoryTheory GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

open TensorProduct Coalgebra Bialgebra WithConv

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PDivGroup

theorem app_app_eq_algebraMap_counit_of_isConn_of_isEt {p : ℕ} [Fact p.Prime] {k k' : Type}
    [Field k] [CharP k p] [PerfectRing k p] [Field k'] {σ : k →+* k'} {G' G'₀ : PDivGroup p k'}
    {C : PDivGroup p k} (i₀ : G'₀ ⟶ G') (hG : G'₀.IsConn) (hC : C.IsEt) (x : SemiHom σ G' C)
    (n : ℕ) (a : C.A n) :
    i₀.app n (x.app n a) = algebraMap k' (G'₀.A n) (σ (counit (R := k) a)) := by
  have hmem : a - algebraMap k (C.A n) (counit (R := k) a) ∈ augIdeal k (C.A n) := by
    rw [mem_augIdeal_iff', map_sub, ← Bialgebra.counitAlgHom_apply (R := k),
      ← Bialgebra.counitAlgHom_apply (R := k), AlgHom.commutes, Algebra.algebraMap_self,
      RingHom.id_apply, sub_self]
  suffices h : i₀.app n ((x.app n).toRingHom (a - algebraMap k (C.A n) (counit (R := k) a))) = 0 by
    rw [map_sub, map_sub, sub_eq_zero] at h
    refine h.trans ?_
    change i₀.app n ((x.app n) (algebraMap k (C.A n) (counit (R := k) a))) = _
    rw [(x.app n).map_algebraMap, AlgHomClass.commutes]
  haveI := hC n
  haveI : IsNoetherianRing (G'₀.A n) := isNoetherian_of_tower k' inferInstance
  obtain ⟨N, hN⟩ := (Ideal.FG.isNilpotent_iff_le_nilradical
    (IsNoetherian.noetherian (augIdeal k' (G'₀.A n)))).2 fun y hy => mem_nilradical.2 (hG n y hy)
  obtain ⟨b, hb, hab⟩ := exists_augIdeal_pow_eq (A := C.A n) N _ hmem
  have hfb : i₀.app n ((x.app n).toRingHom b) ∈ augIdeal k' (G'₀.A n) := by
    rw [mem_augIdeal_iff', CoalgHomClass.counit_comp_apply]
    change counit (R := k') ((x.app n) b) = 0
    rw [(x.app n).counit_map, (mem_augIdeal_iff' b).1 hb, map_zero]
  have hle : N ≤ p ^ N := (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le
  have h1 := Ideal.pow_le_pow_right hle (Ideal.pow_mem_pow hfb (p ^ N))
  rw [hN] at h1
  rw [hab, map_pow, map_pow]
  exact (Submodule.mem_bot _).1 h1

theorem add_app_eq_lift_comul {p : ℕ} {k : Type} [CommRing k] {G H : PDivGroup p k}
    (f g : G ⟶ H) (n : ℕ) (c : H.A n) :
    Hom.app (f + g) n c = Algebra.TensorProduct.lift (f.app n : H.A n →ₐ[k] G.A n)
      (g.app n : H.A n →ₐ[k] G.A n) (fun _ _ => .all _ _) (comul c) := by
  have h := DFunLike.congr_fun (congrArg ofConv (map_mul toPts (f.conv n) (g.conv n))) c
  rw [AlgHom.convMul_apply] at h
  exact h

end GlobalTheory.PDivGroup

theorem GlobalTheory.PDivGroup.semiHom_factor_of_isConn_of_isEt :
    ∀ (p : ℕ) [Fact p.Prime] (k k' : Type) [Field k] [CharP k p] [PerfectRing k p]
    [Field k'] [CharP k' p] [PerfectRing k' p] (σ : k →+* k') (G' G'₀ G'₁ : PDivGroup p k') (C : PDivGroup p k)
    (i₀ : G'₀ ⟶ G') (q₀ : G' ⟶ G'₀) (i₁ : G'₁ ⟶ G') (q₁ : G' ⟶ G'₁), G'₀.IsConn → C.IsEt →
    q₀ ≫ i₀ + q₁ ≫ i₁ = 𝟙 G' → ∀ (x : SemiHom σ G' C) (n : ℕ) (a : C.A n),
      q₁.app n (i₁.app n (x.app n a)) = x.app n a := by
  intro p _ k k' _ _ _ _ _ _ σ G' G'₀ G'₁ C i₀ q₀ i₁ q₁ hG hC hs x n a
  have key : ∀ t : C.A n ⊗[k] C.A n,
      Algebra.TensorProduct.lift ((q₀ ≫ i₀).app n : G'.A n →ₐ[k'] G'.A n)
        ((q₁ ≫ i₁).app n : G'.A n →ₐ[k'] G'.A n) (fun _ _ => .all _ _) ((x.app n).two t) =
      (q₁ ≫ i₁).app n (x.app n (TensorProduct.lid k _ (LinearMap.rTensor _ counit t))) := by
    intro t
    induction t with
    | zero => simp
    | add u v hu hv =>
      rw [map_add, map_add, hu, hv, map_add, map_add, ← map_add, ← map_add]
    | tmul a₁ a₂ =>
      rw [TensorProduct.map_tmul, SemiBialgHom.lin_apply, SemiBialgHom.lin_apply,
        Algebra.TensorProduct.lift_tmul, LinearMap.rTensor_tmul, TensorProduct.lid_tmul]
      change q₀.app n (i₀.app n (x.app n a₁)) * _ = _
      rw [app_app_eq_algebraMap_counit_of_isConn_of_isEt i₀ hG hC x n a₁, AlgHomClass.commutes,
        ← Algebra.smul_def, (x.app n).smul_map]
      change _ = ((q₁ ≫ i₁).app n : G'.A n →ₐ[k'] G'.A n) (σ (counit a₁) • x.app n a₂)
      rw [map_smul]
  have h1 : x.app n a = Hom.app (q₀ ≫ i₀ + q₁ ≫ i₁) n (x.app n a) := by rw [hs]; rfl
  rw [add_app_eq_lift_comul, ← SemiBialgHom.two_comul, key, Coalgebra.rTensor_counit_comul,
    TensorProduct.lid_tmul, one_smul] at h1
  exact h1.symm
end
end

open CategoryTheory GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semilinearHom_etale_factor_through_part : ∀ (p : ℕ) [Fact p.Prime] (k k' : Type) [Field k] [CharP k p] [PerfectRing k p]
    [Field k'] [CharP k' p] [PerfectRing k' p] (σ : k →+* k') (G' G'₀ G'₁ : PDivGroup p k') (C : PDivGroup p k)
    (i₀ : G'₀ ⟶ G') (q₀ : G' ⟶ G'₀) (i₁ : G'₁ ⟶ G') (q₁ : G' ⟶ G'₁), G'₀.IsConn → C.IsEt →
    q₀ ≫ i₀ + q₁ ≫ i₁ = 𝟙 G' → ∀ (x : SemiHom σ G' C) (n : ℕ) (a : C.A n),
      q₁.app n (i₁.app n (x.app n a)) = x.app n a := by
  atlas_forward_decl GlobalTheory.PDivGroup.semiHom_factor_of_isConn_of_isEt
end

section
section
open CategoryTheory GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Dieu.Glue

variable {p : ℕ}

def semiThrough {k k' : Type} [CommRing k] [CommRing k'] {σ : k →+* k'} {G' A' : PDivGroup p k'}
    {G A : PDivGroup p k} (i : A' ⟶ G') (s : SemiHom σ G' G) (q : G ⟶ A) : SemiHom σ A' A :=
  (SemiHom.ofHom i).comp (s.comp (SemiHom.ofHom q))

@[simp] theorem semiThrough_app {k k' : Type} [CommRing k] [CommRing k'] {σ : k →+* k'} {G' A' : PDivGroup p k'}
    {G A : PDivGroup p k} (i : A' ⟶ G') (s : SemiHom σ G' G) (q : G ⟶ A) (n : ℕ) (a : A.A n) :
    (semiThrough i s q).app n a = i.app n (s.app n (q.app n a)) := rfl

theorem semiThrough_ofHom {k : Type} [CommRing k] {A' G' G A : PDivGroup p k} (i : A' ⟶ G') (f : G' ⟶ G)
    (q : G ⟶ A) : semiThrough i (SemiHom.ofHom f) q = SemiHom.ofHom (i ≫ f ≫ q) :=
  SemiHom.ext_apply fun _ _ => rfl

section Base

variable [Fact p.Prime] {P : ∀ (k : Type) [CommRing k], PDivGroup p k → Prop} (B : Base p P)
  {k : Type} [Field k] [CharP k p] [PerfectRing k p]

theorem map_comp {G H K : PDivGroup p k} (hG : P k G) (hH : P k H) (hK : P k K) (f : G ⟶ H)
    (g : H ⟶ K) (m : B.M K hK) : B.map hG hK (f ≫ g) m = B.map hG hH f (B.map hH hK g m) :=
  B.smap_comp hG hH hK (SemiHom.ofHom g) (SemiHom.ofHom f) (SemiHom.ofHom (f ≫ g)) (fun _ _ => rfl) m

theorem eq_zero_of_id_eq_zero {G : PDivGroup p k} (hG : P k G) (h0 : 𝟙 G = 0) (m : B.M G hG) : m = 0 := by
  have h := B.smap_add hG hG 0 0 m
  rw [add_zero] at h
  have h2 : B.smap hG hG (SemiHom.ofHom 0) m = 0 := by simpa using h
  rw [← B.smap_id G hG m, h0]
  exact h2

theorem rigExtMap_rigExtMap {k : Type} [CommRing k] {X Y Z : PDivGroup p k} (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : Z.RigExt) : rigExtMap f (rigExtMap g x) = rigExtMap (f ≫ g) x := by
  rw [rigExtMap_comp]; rfl

theorem rigExtMap_zero' {X Y : PDivGroup p k} : rigExtMap (0 : X ⟶ Y) = 0 := by
  have h := (rigExtMap_add_and_natCast_smul_id p k (CharP.cast_eq_zero k p) X Y).1 0 0
  rw [add_zero] at h
  simpa using h

theorem rig_split₀ {G G₀ G₁ : PDivGroup p k} (i₀ : G₀ ⟶ G) (q₀ : G ⟶ G₀) (q₁ : G ⟶ G₁)
    (h₀ : i₀ ≫ q₀ = 𝟙 G₀) (z : i₀ ≫ q₁ = 0) (r₀ : G₀.RigExt) (r₁ : G₁.RigExt) :
    rigExtMap i₀ (rigExtMap q₀ r₀ + rigExtMap q₁ r₁) = r₀ := by
  rw [LinearMap.map_add, rigExtMap_rigExtMap, rigExtMap_rigExtMap, h₀, z, rigExtMap_zero', rigExtMap_id]
  simp

theorem rig_split₁ {G G₀ G₁ : PDivGroup p k} (i₁ : G₁ ⟶ G) (q₀ : G ⟶ G₀) (q₁ : G ⟶ G₁)
    (h₁ : i₁ ≫ q₁ = 𝟙 G₁) (z : i₁ ≫ q₀ = 0) (r₀ : G₀.RigExt) (r₁ : G₁.RigExt) :
    rigExtMap i₁ (rigExtMap q₀ r₀ + rigExtMap q₁ r₁) = r₁ := by
  rw [LinearMap.map_add, rigExtMap_rigExtMap, rigExtMap_rigExtMap, h₁, z, rigExtMap_zero', rigExtMap_id]
  simp

def redSum {W : Type} [CommRing W] (τ : W →+* k) {M₀ M₁ : Type} [AddCommGroup M₀] [Module W M₀]
    [AddCommGroup M₁] [Module W M₁] {G G₀ G₁ : PDivGroup p k} (q₀ : G ⟶ G₀) (q₁ : G ⟶ G₁)
    (r₀ : M₀ →ₛₗ[τ] G₀.RigExt) (r₁ : M₁ →ₛₗ[τ] G₁.RigExt) : M₀ × M₁ →ₛₗ[τ] G.RigExt :=
  ((rigExtMap q₀).comp r₀).comp (LinearMap.fst W M₀ M₁) + ((rigExtMap q₁).comp r₁).comp (LinearMap.snd W M₀ M₁)

theorem redSum_apply {W : Type} [CommRing W] (τ : W →+* k) {M₀ M₁ : Type} [AddCommGroup M₀] [Module W M₀]
    [AddCommGroup M₁] [Module W M₁] {G G₀ G₁ : PDivGroup p k} (q₀ : G ⟶ G₀) (q₁ : G ⟶ G₁)
    (r₀ : M₀ →ₛₗ[τ] G₀.RigExt) (r₁ : M₁ →ₛₗ[τ] G₁.RigExt) (m : M₀ × M₁) :
    redSum τ q₀ q₁ r₀ r₁ m = rigExtMap q₀ (r₀ m.1) + rigExtMap q₁ (r₁ m.2) := rfl

theorem rig_semiThrough {k' : Type} [CommRing k'] {σ : k →+* k'} {G' A' : PDivGroup p k'} {G A : PDivGroup p k}
    (i : A' ⟶ G') (q' : G' ⟶ A') (s : SemiHom σ G' G) (q : G ⟶ A)
    (h : ∀ n a, q'.app n (i.app n (s.app n (q.app n a))) = s.app n (q.app n a)) (r : A.RigExt) :
    rigExtMap q' ((semiThrough i s q).rig r) = s.rig (rigExtMap q r) := by
  rw [← SemiHom.ofHom_rig, ← SemiHom.ofHom_rig, SemiHom.rig_rig (semiThrough i s q) (SemiHom.ofHom q') (s.comp (SemiHom.ofHom q))
    (fun n a => (h n a).symm)]
  exact SemiHom.comp_rig _ _ _

end Base

theorem exists_katz_etDual : ∀ (p : ℕ) [Fact p.Prime] (Bc : GlobalTheory.Dieu.Base p (fun _ _ G => G.IsConn))
    (Be : GlobalTheory.Dieu.Base p (fun _ _ G => G.IsEt)), Bc.Katz → Be.EtDual Bc →
    ∃ B : GlobalTheory.Dieu.Base p (fun _ _ _ => True), B.Katz ∧ B.EtDual B := by
  intro p _ Bc Be hK hE
  choose G₀ G₁ i₀ q₀ i₁ q₁ hc he h₀ h₁ hs using
    fun (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k) =>
      GlobalTheory.PDivGroup.exists_isConn_isEt_splitting p k G
  have rz : ∀ (k : Type) [Field k] [CharP k p] [PerfectRing k p] (X Y : PDivGroup p k),
      rigExtMap (0 : X ⟶ Y) = 0 := by
    intro k _ _ _ X Y
    have h := (rigExtMap_add_and_natCast_smul_id p k (CharP.cast_eq_zero k p) X Y).1 0 0
    rw [add_zero] at h
    simpa using h
  let D : Base p (fun _ _ _ => True) :=
  { M := fun {k} _ _ _ G _ =>
      ModuleCat.of (WittVector p k) (Bc.M (G₀ k G) (hc k G) × Be.M (G₁ k G) (he k G))
    smap := fun {k k'} _ _ _ _ _ _ {σ G' G} _ _ s =>
      (Bc.smap (hc k' G') (hc k G) (semiThrough (i₀ k' G') s (q₀ k G))).prodMap
        (Be.smap (he k' G') (he k G) (semiThrough (i₁ k' G') s (q₁ k G)))
    red := fun {k} _ _ _ G _ =>
      redSum _ (q₀ k G) (q₁ k G) (Bc.red (G₀ k G) (hc k G)) (Be.red (G₁ k G) (he k G))
    free := fun {k} _ _ _ G _ => by
      haveI := Bc.free (G₀ k G) (hc k G)
      haveI := Be.free (G₁ k G) (he k G)
      exact (inferInstance : Module.Free (WittVector p k) (Bc.M (G₀ k G) (hc k G) × Be.M (G₁ k G) (he k G)))
    finite := fun {k} _ _ _ G _ => by
      haveI := Bc.finite (G₀ k G) (hc k G)
      haveI := Be.finite (G₁ k G) (he k G)
      exact (inferInstance : Module.Finite (WittVector p k) (Bc.M (G₀ k G) (hc k G) × Be.M (G₁ k G) (he k G)))
    red_surjective := fun {k} _ _ _ G _ x => by
      obtain ⟨m₀, e₀⟩ := Bc.red_surjective (G₀ k G) (hc k G) (rigExtMap (i₀ k G) x)
      obtain ⟨m₁, e₁⟩ := Be.red_surjective (G₁ k G) (he k G) (rigExtMap (i₁ k G) x)
      refine ⟨(m₀, m₁), ?_⟩
      change rigExtMap (q₀ k G) (Bc.red _ _ m₀) + rigExtMap (q₁ k G) (Be.red _ _ m₁) = x
      rw [e₀, e₁, rigExtMap_rigExtMap, rigExtMap_rigExtMap, ← LinearMap.add_apply, ← (rigExtMap_add_and_natCast_smul_id p k (CharP.cast_eq_zero k p) G G).1,
        hs, rigExtMap_id, LinearMap.id_apply]
    red_eq_zero := fun {k} _ _ _ G _ m => by
      obtain ⟨m₀, m₁⟩ := m
      have ke₀ := Bc.red_eq_zero (G₀ k G) (hc k G) m₀
      have ke₁ := Be.red_eq_zero (G₁ k G) (he k G) m₁
      have z01 := (hom_eq_zero_of_isConn_of_isEt p k (G₀ k G) (G₁ k G) (hc k G) (he k G)).1 (i₀ k G ≫ q₁ k G)
      have z10 := (hom_eq_zero_of_isConn_of_isEt p k (G₀ k G) (G₁ k G) (hc k G) (he k G)).2 (i₁ k G ≫ q₀ k G)
      change rigExtMap (q₀ k G) (Bc.red _ _ m₀) + rigExtMap (q₁ k G) (Be.red _ _ m₁) = 0 ↔ _
      constructor
      · intro h
        have a₀ := (rig_split₀ (i₀ k G) (q₀ k G) (q₁ k G) (h₀ k G) z01 _ _).symm.trans
          ((congrArg (rigExtMap (i₀ k G)) h).trans (map_zero _))
        have a₁ := (rig_split₁ (i₁ k G) (q₀ k G) (q₁ k G) (h₁ k G) z10 _ _).symm.trans
          ((congrArg (rigExtMap (i₁ k G)) h).trans (map_zero _))
        obtain ⟨n₀, e₀⟩ := ke₀.1 a₀
        obtain ⟨n₁, e₁⟩ := ke₁.1 a₁
        exact ⟨(n₀, n₁), Prod.ext e₀ e₁⟩
      · rintro ⟨n, h⟩
        have h' : ((m₀, m₁) : Bc.M (G₀ k G) (hc k G) × Be.M (G₁ k G) (he k G)) = (p • n.1, p • n.2) := h
        obtain ⟨e₀, e₁⟩ := Prod.ext_iff.1 h'
        exact (congrArg₂ (fun a b => rigExtMap (q₀ k G) a + rigExtMap (q₁ k G) b) (ke₀.2 ⟨n.1, e₀⟩)
          (ke₁.2 ⟨n.2, e₁⟩)).trans (by simp)
    smap_smul := fun {k k'} _ _ _ _ _ _ {σ G' G} _ _ s a m =>
      Prod.ext (Bc.smap_smul (hc k' G') (hc k G) _ a m.1) (Be.smap_smul (he k' G') (he k G) _ a m.2)
    smap_id := fun {k} _ _ _ G _ m => by
      refine Prod.ext ?_ ?_
      · change Bc.smap _ _ (semiThrough (i₀ k G) (SemiHom.ofHom (𝟙 G)) (q₀ k G)) m.1 = m.1
        rw [semiThrough_ofHom, Category.id_comp, h₀]
        exact Bc.smap_id _ _ _
      · change Be.smap _ _ (semiThrough (i₁ k G) (SemiHom.ofHom (𝟙 G)) (q₁ k G)) m.2 = m.2
        rw [semiThrough_ofHom, Category.id_comp, h₁]
        exact Be.smap_id _ _ _
    smap_add := fun {k} _ _ _ G H _ _ f g m => by
      refine Prod.ext ?_ ?_
      · change Bc.smap _ _ (semiThrough (i₀ k G) (SemiHom.ofHom (f + g)) (q₀ k H)) m.1 =
          Bc.smap _ _ (semiThrough (i₀ k G) (SemiHom.ofHom f) (q₀ k H)) m.1 +
            Bc.smap _ _ (semiThrough (i₀ k G) (SemiHom.ofHom g) (q₀ k H)) m.1
        rw [semiThrough_ofHom, semiThrough_ofHom, semiThrough_ofHom, Preadditive.add_comp, Preadditive.comp_add]
        exact Bc.smap_add _ _ _ _ _
      · change Be.smap _ _ (semiThrough (i₁ k G) (SemiHom.ofHom (f + g)) (q₁ k H)) m.2 =
          Be.smap _ _ (semiThrough (i₁ k G) (SemiHom.ofHom f) (q₁ k H)) m.2 +
            Be.smap _ _ (semiThrough (i₁ k G) (SemiHom.ofHom g) (q₁ k H)) m.2
        rw [semiThrough_ofHom, semiThrough_ofHom, semiThrough_ofHom, Preadditive.add_comp, Preadditive.comp_add]
        exact Be.smap_add _ _ _ _ _
    smap_comp := fun {k k' k''} _ _ _ _ _ _ _ _ _ {σ τ υ G'' G' G} _ _ _ s t u hu m => by
      refine Prod.ext ?_ ?_
      · refine Bc.smap_comp (hc k'' G'') (hc k' G') (hc k G) (semiThrough (i₀ k' G') s (q₀ k G))
          (semiThrough (i₀ k'' G'') t (q₀ k' G')) (semiThrough (i₀ k'' G'') u (q₀ k G)) (fun n a => ?_) m.1
        have e := GlobalTheory.T.semilinearHom_connected_factor_through_part p k k' _ G' (G₀ k' G') (G₁ k' G') (G₀ k G) (i₀ k' G') (q₀ k' G')
          (i₁ k' G') (q₁ k' G') (he k' G') (hc k G) (hs k' G') (s.comp (SemiHom.ofHom (q₀ k G))) n a
        simp only [SemiHom.comp_app, SemiHom.ofHom_app] at e
        simp only [semiThrough_app, hu, e]
      · refine Be.smap_comp (he k'' G'') (he k' G') (he k G) (semiThrough (i₁ k' G') s (q₁ k G))
          (semiThrough (i₁ k'' G'') t (q₁ k' G')) (semiThrough (i₁ k'' G'') u (q₁ k G)) (fun n a => ?_) m.2
        have e := GlobalTheory.T.semilinearHom_etale_factor_through_part p k k' _ G' (G₀ k' G') (G₁ k' G') (G₁ k G) (i₀ k' G') (q₀ k' G')
          (i₁ k' G') (q₁ k' G') (hc k' G') (he k G) (hs k' G') (s.comp (SemiHom.ofHom (q₁ k G))) n a
        simp only [SemiHom.comp_app, SemiHom.ofHom_app] at e
        simp only [semiThrough_app, hu, e]
    red_smap := fun {k k'} _ _ _ _ _ _ {σ G' G} _ _ s m => by
      have c₀ := rig_semiThrough (i₀ k' G') (q₀ k' G') s (q₀ k G) (fun n a =>
        GlobalTheory.T.semilinearHom_connected_factor_through_part p k k' _ G' (G₀ k' G') (G₁ k' G') (G₀ k G) (i₀ k' G') (q₀ k' G')
                     (i₁ k' G') (q₁ k' G') (he k' G') (hc k G) (hs k' G') (s.comp (SemiHom.ofHom (q₀ k G))) n a)
      have c₁ := rig_semiThrough (i₁ k' G') (q₁ k' G') s (q₁ k G) (fun n a =>
        GlobalTheory.T.semilinearHom_etale_factor_through_part p k k' _ G' (G₀ k' G') (G₁ k' G') (G₁ k G) (i₀ k' G') (q₀ k' G')
                     (i₁ k' G') (q₁ k' G') (hc k' G') (he k G) (hs k' G') (s.comp (SemiHom.ofHom (q₁ k G))) n a)
      obtain ⟨m₀, m₁⟩ := m
      have a := Bc.red_smap (hc k' G') (hc k G) (semiThrough (i₀ k' G') s (q₀ k G)) m₀
      have b := Be.red_smap (he k' G') (he k G) (semiThrough (i₁ k' G') s (q₁ k G)) m₁
      refine (redSum_apply _ _ _ _ _ _).trans ?_
      refine Eq.trans ?_ (congrArg s.rig (redSum_apply _ _ _ _ _ _)).symm
      refine Eq.trans ?_ (map_add s.rig _ _).symm
      exact congrArg₂ (· + ·) ((congrArg (rigExtMap (q₀ k' G')) a).trans (c₀ _))
        ((congrArg (rigExtMap (q₁ k' G')) b).trans (c₁ _)) }
  have qz : ∀ (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k), G.IsConn →
      q₁ k G = 0 := fun k _ _ _ G hG => (hom_eq_zero_of_isConn_of_isEt p k G (G₁ k G) hG (he k G)).1 _
  have id1 : ∀ (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k), G.IsConn →
      𝟙 (G₁ k G) = 0 := by
    intro k _ _ _ G hG
    rw [← h₁ k G, qz k G hG, Limits.comp_zero]
  have qi0 : ∀ (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k), G.IsConn →
      q₀ k G ≫ i₀ k G = 𝟙 G := by
    intro k _ _ _ G hG
    have := hs k G
    rwa [qz k G hG, Limits.zero_comp, add_zero] at this
  have iz : ∀ (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k), G.IsEt →
      q₀ k G = 0 := fun k _ _ _ G hG => (hom_eq_zero_of_isConn_of_isEt p k (G₀ k G) G (hc k G) hG).2 _
  have id0 : ∀ (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k), G.IsEt →
      𝟙 (G₀ k G) = 0 := by
    intro k _ _ _ G hG
    rw [← h₀ k G, iz k G hG, Limits.comp_zero]
  have qi1 : ∀ (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k), G.IsEt →
      q₁ k G ≫ i₁ k G = 𝟙 G := by
    intro k _ _ _ G hG
    have := hs k G
    rwa [iz k G hG, Limits.zero_comp, zero_add] at this
  refine ⟨D, katz_etDual_of_iso p Bc Be D hK hE ⟨fun {k} _ _ _ G h => LinearEquiv.ofLinearMap
      ((Bc.map h (hc k G) (q₀ k G)).comp (LinearMap.fst _ _ _))
      ((LinearMap.inl _ _ _).comp (Bc.map (hc k G) h (i₀ k G)))
      (LinearMap.ext fun m => (map_comp Bc h (hc k G) h (q₀ k G) (i₀ k G) m).symm.trans (by
        rw [qi0 k G h]; exact Bc.smap_id G h m))
      (LinearMap.ext fun m => Prod.ext
        ((map_comp Bc (hc k G) h (hc k G) (i₀ k G) (q₀ k G) m.1).symm.trans (by
          rw [h₀ k G]; exact Bc.smap_id _ _ m.1))
        (eq_zero_of_id_eq_zero Be (he k G) (id1 k G h) m.2).symm), ?_⟩
    ⟨fun {k} _ _ _ G h => LinearEquiv.ofLinearMap
      ((Be.map h (he k G) (q₁ k G)).comp (LinearMap.snd _ _ _))
      ((LinearMap.inr _ _ _).comp (Be.map (he k G) h (i₁ k G)))
      (LinearMap.ext fun m => (map_comp Be h (he k G) h (q₁ k G) (i₁ k G) m).symm.trans (by
        rw [qi1 k G h]; exact Be.smap_id G h m))
      (LinearMap.ext fun m => Prod.ext
        (eq_zero_of_id_eq_zero Bc (hc k G) (id0 k G h) m.1).symm
        ((map_comp Be (he k G) h (he k G) (i₁ k G) (q₁ k G) m.2).symm.trans (by
          rw [h₁ k G]; exact Be.smap_id _ _ m.2))), ?_⟩⟩
  · intro k k' _ _ _ _ _ _ σ G' G h' h s m
    exact (Bc.smap_comp h' (hc k' G') (hc k G) (semiThrough (i₀ k' G') s (q₀ k G)) (SemiHom.ofHom (q₀ k' G'))
      (s.comp (SemiHom.ofHom (q₀ k G))) (fun n a => (GlobalTheory.T.semilinearHom_connected_factor_through_part p k k' _ G' (G₀ k' G') (G₁ k' G')
        (G₀ k G) (i₀ k' G') (q₀ k' G') (i₁ k' G') (q₁ k' G') (he k' G') (hc k G) (hs k' G')
        (s.comp (SemiHom.ofHom (q₀ k G))) n a).symm) m.1).symm.trans
      (Bc.smap_comp h' h (hc k G) (SemiHom.ofHom (q₀ k G)) s (s.comp (SemiHom.ofHom (q₀ k G)))
        (fun _ _ => rfl) m.1)
  · intro k k' _ _ _ _ _ _ σ G' G h' h s m
    exact (Be.smap_comp h' (he k' G') (he k G) (semiThrough (i₁ k' G') s (q₁ k G)) (SemiHom.ofHom (q₁ k' G'))
      (s.comp (SemiHom.ofHom (q₁ k G))) (fun n a => (GlobalTheory.T.semilinearHom_etale_factor_through_part p k k' _ G' (G₀ k' G') (G₁ k' G')
        (G₁ k G) (i₀ k' G') (q₀ k' G') (i₁ k' G') (q₁ k' G') (hc k' G') (he k G) (hs k' G')
        (s.comp (SemiHom.ofHom (q₁ k G))) n a).symm) m.2).symm.trans
      (Be.smap_comp h' h (he k G) (SemiHom.ofHom (q₁ k G)) s (s.comp (SemiHom.ofHom (q₁ k G)))
        (fun _ _ => rfl) m.2)

end GlobalTheory.Dieu.Glue
end
end

open CategoryTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dieudonneFunctor_glued_connected_etale : ∀ (p : ℕ) [Fact p.Prime] (Bc : GlobalTheory.Dieu.Base p (fun _ _ G => G.IsConn)) (Be : GlobalTheory.Dieu.Base p (fun _ _ G => G.IsEt)), Bc.Katz → Be.EtDual Bc → ∃ B : GlobalTheory.Dieu.Base p (fun _ _ _ => True), B.Katz ∧ B.EtDual B := by
  atlas_forward_decl GlobalTheory.Dieu.Glue.exists_katz_etDual
end

section
section
set_option autoImplicit false

open CategoryTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.Dieu

section FrobInv

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [PerfectRing k p]

theorem wittMap_frobeniusEquiv_symm (x : WittVector p k) :
    WittVector.map ((frobeniusEquiv k p).symm : k →+* k) x = (WittVector.frobeniusEquiv p k).symm x := by
  apply (WittVector.frobeniusEquiv p k).injective
  rw [RingEquiv.apply_symm_apply]
  ext n
  simp [WittVector.coeff_frobenius_charP, WittVector.map_coeff]

noncomputable def frobInv (G : PDivGroup p k) :
    SemiHom ((frobeniusEquiv k p).symm : k →+* k) G (frobTwist (p_eq_zero p k) G) :=
  letI := (frobRing (p_eq_zero p k)).toAlgebra
  (SemiHom.ofHom (𝟙 G)).liftOver _ fun r => by
    change r = (frobeniusEquiv k p).symm (frobRing (p_eq_zero p k) r)
    rw [frobRing_apply, ← frobenius_def, frobeniusEquiv_symm_apply_frobenius]

theorem frobInv_frobProj (G : PDivGroup p k) (n : ℕ) (a : G.A n) :
    (frobInv G).app n ((frobProj (p_eq_zero p k) G).app n a) = a := by
  letI := (frobRing (p_eq_zero p k)).toAlgebra
  refine (SemiHom.liftOver_app _ _ _ n 1 a).trans ?_
  simp

theorem frobInv_app_pow (G : PDivGroup p k) (n : ℕ) (y : (frobTwist (p_eq_zero p k) G).A n) :
    ((frobInv G).app n y) ^ p = (relFrob (p_eq_zero p k) G).app n y := by
  have h0 : (p : G.A n) = 0 := natCast_eq_zero_of_algebra (p_eq_zero p k) _
  induction y using frobTwist_induction (p_eq_zero p k) n with
  | h0 => simp [zero_pow (Fact.out : p.Prime).ne_zero]
  | h1 r a =>
    rw [(frobInv G).app n |>.smul_map, frobInv_frobProj, map_smul, relFrob_app_frobProj, smul_pow]
    congr 1
    exact frobeniusEquiv_symm_pow_p k p r
  | h2 x y hx hy =>
    rw [map_add, map_add, ← hx, ← hy]
    simpa using map_add (frobRing h0) ((frobInv G).app n x) ((frobInv G).app n y)

omit [CharP k p] [PerfectRing k p] in

theorem Base.smap_ofHom_nsmul_id {P : ∀ (k : Type) [CommRing k], PDivGroup p k → Prop} (B : Base p P)
    [CharP k p] [PerfectRing k p] (G : PDivGroup p k) (h : P k G) (n : ℕ) (m : B.M G h) :
    B.smap h h (SemiHom.ofHom (n • 𝟙 G)) m = n • m := by
  induction n with
  | zero =>
    have e := B.smap_add h h 0 0 m
    rw [add_zero] at e
    rw [zero_smul, zero_smul]
    simpa using e
  | succ n ih => rw [succ_nsmul, B.smap_add, ih, B.smap_id, succ_nsmul]

noncomputable def Base.verOp (B : Base p fun _ _ _ => True) (G : PDivGroup p k) :
    B.M G trivial →ₛₗ[((WittVector.frobeniusEquiv p k).symm : WittVector p k →+* WittVector p k)]
      B.M G trivial where
  toFun m := B.smap trivial trivial (frobInv G) (B.map trivial trivial (verschiebung (p_eq_zero p k) G) m)
  map_add' x y := by rw [map_add, map_add]
  map_smul' a m := by
    rw [LinearMap.map_smul, B.smap_smul, wittMap_frobeniusEquiv_symm]
    rfl

theorem Base.F_verOp (B : Base p fun _ _ _ => True) (G : PDivGroup p k) (m : B.M G trivial) :
    B.F G trivial (B.verOp G m) = p • m := by
  change B.smap trivial trivial (absFrob (p_eq_zero p k) G) (B.smap trivial trivial (frobInv G)
    (B.smap trivial trivial (SemiHom.ofHom (verschiebung (p_eq_zero p k) G)) m)) = _
  rw [← B.smap_comp trivial trivial trivial (SemiHom.ofHom (verschiebung (p_eq_zero p k) G)) (frobInv G)
    ((frobInv G).comp (SemiHom.ofHom (verschiebung (p_eq_zero p k) G))) (fun n a => rfl)]
  rw [← B.smap_comp trivial trivial trivial ((frobInv G).comp (SemiHom.ofHom (verschiebung (p_eq_zero p k) G)))
    (absFrob (p_eq_zero p k) G) (SemiHom.ofHom (relFrob (p_eq_zero p k) G ≫ verschiebung (p_eq_zero p k) G)) ?_]
  · rw [relFrob_comp_verschiebung, Nat.cast_smul_eq_nsmul, B.smap_ofHom_nsmul_id]
  · intro n a
    rw [SemiHom.ofHom_app, absFrob_app, SemiHom.comp_app, SemiHom.ofHom_app, frobInv_app_pow]
    rfl

theorem Base.verOp_F (B : Base p fun _ _ _ => True) (G : PDivGroup p k) (m : B.M G trivial) :
    B.verOp G (B.F G trivial m) = p • m := by
  change B.smap trivial trivial (frobInv G)
    (B.smap trivial trivial (SemiHom.ofHom (verschiebung (p_eq_zero p k) G))
      (B.smap trivial trivial (absFrob (p_eq_zero p k) G) m)) = _
  rw [← B.smap_comp trivial trivial trivial (SemiHom.ofHom (verschiebung (p_eq_zero p k) G)) (frobInv G)
    ((frobInv G).comp (SemiHom.ofHom (verschiebung (p_eq_zero p k) G))) (fun n a => rfl)]
  rw [← B.smap_comp trivial trivial trivial (absFrob (p_eq_zero p k) G)
    ((frobInv G).comp (SemiHom.ofHom (verschiebung (p_eq_zero p k) G)))
    (SemiHom.ofHom (relFrob (p_eq_zero p k) G ≫ verschiebung (p_eq_zero p k) G)) ?_]
  · rw [relFrob_comp_verschiebung, Nat.cast_smul_eq_nsmul, B.smap_ofHom_nsmul_id]
  · intro n a
    rw [SemiHom.ofHom_app, absFrob_app, SemiHom.comp_app, SemiHom.ofHom_app]
    rw [map_pow, map_pow, frobInv_app_pow]
    rfl

end FrobInv

theorem exists_V_of_base : ∀ (p : ℕ) [Fact p.Prime] (B : GlobalTheory.Dieu.Base p (fun _ _ _ => True)),
    ∃ V : ∀ {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G : GlobalTheory.PDivGroup p k),
      B.M G trivial →ₛₗ[((WittVector.frobeniusEquiv p k).symm : WittVector p k →+* WittVector p k)] B.M G trivial,
      (∀ {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G : GlobalTheory.PDivGroup p k) (m : B.M G trivial),
        B.F G trivial (V G m) = p • m) ∧
      ∀ {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G : GlobalTheory.PDivGroup p k) (m : B.M G trivial),
        V G (B.F G trivial m) = p • m :=
  fun _ _ B => ⟨fun G => B.verOp G, fun G m => B.F_verOp G m, fun G m => B.verOp_F G m⟩

end GlobalTheory.Dieu
end

open CategoryTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_verschiebung_of_dieudonneFunctorBase : ∀ (p : ℕ) [Fact p.Prime] (B : GlobalTheory.Dieu.Base p (fun _ _ _ => True)), ∃ V : ∀ {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G : GlobalTheory.PDivGroup p k), B.M G trivial →ₛₗ[((WittVector.frobeniusEquiv p k).symm : WittVector p k →+* WittVector p k)] B.M G trivial, (∀ {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G : GlobalTheory.PDivGroup p k) (m : B.M G trivial), B.F G trivial (V G m) = p • m) ∧ ∀ {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G : GlobalTheory.PDivGroup p k) (m : B.M G trivial), V G (B.F G trivial m) = p • m := by
  atlas_forward_decl GlobalTheory.Dieu.exists_V_of_base
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.Dieu

def theory (p : ℕ) [Fact p.Prime] : Theory p :=
  let Bc := (GlobalTheory.T.exists_connected_dieudonne_functor_quasiLogarithms p).choose
  let Be := (GlobalTheory.T.exists_etaleDieudonneBase_by_cartierDuality p Bc).choose
  let hB := GlobalTheory.T.exists_dieudonneFunctor_glued_connected_etale p Bc Be (GlobalTheory.T.exists_connected_dieudonne_functor_quasiLogarithms p).choose_spec (GlobalTheory.T.exists_etaleDieudonneBase_by_cartierDuality p Bc).choose_spec
  let hV := GlobalTheory.T.exists_verschiebung_of_dieudonneFunctorBase p hB.choose
  { base := hB.choose, katz := hB.choose_spec.1, etDual := hB.choose_spec.2, V := hV.choose,
    F_V := hV.choose_spec.1, V_F := hV.choose_spec.2 }

end GlobalTheory.Dieu
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DeRhamCharpolyP

theorem charpoly_of_red {R K M V : Type} [CommRing R] [Field K] [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M] [AddCommGroup V] [Module K V]
    (π : R →+* K) (hπ : Function.Surjective π) (c : ℕ) (hc : (c : K) = 0)
    (red : M →ₛₗ[π] V) (hs : Function.Surjective red) (hk : ∀ m, red m = 0 ↔ ∃ n, m = c • n)
    (φ : Module.End R M) (ψ : Module.End K V) (h : ∀ m, red (φ m) = ψ (red m)) :
    ∃ _ : Module.Finite K V, ψ.charpoly = φ.charpoly.map π := by
  classical
  let b := Module.Free.chooseBasis R M
  let v : Module.Free.ChooseBasisIndex R M → V := fun i => red (b i)
  have hred : ∀ m, red m = ∑ i, π (b.repr m i) • v i := fun m => by
    conv_lhs => rw [← b.sum_repr m]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => map_smulₛₗ red _ _
  have hli : LinearIndependent K v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    let a : Module.Free.ChooseBasisIndex R M → R := fun j => Function.surjInv hπ (g j)
    have ha : ∀ j, π (a j) = g j := fun j => Function.surjInv_eq hπ (g j)
    have h0 : red (∑ j, a j • b j) = 0 := by
      rw [map_sum]
      simp_rw [map_smulₛₗ, ha]
      exact hg
    obtain ⟨n, hn⟩ := (hk _).1 h0
    have hai : a i = (c : R) * b.repr n i := by
      have := congrArg (fun m => b.repr m i) hn
      simp only [map_sum, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply,
        Module.Basis.repr_self, smul_eq_mul, map_nsmul, Finsupp.coe_smul, Pi.smul_apply] at this
      rw [Finset.sum_eq_single i (fun j _ hj => by simp [Finsupp.single_apply, hj])
        (fun hi => absurd (Finset.mem_univ i) hi)] at this
      simpa [nsmul_eq_mul] using this
    rw [← ha i, hai, map_mul, map_natCast, hc, zero_mul]
  have hsp : ⊤ ≤ Submodule.span K (Set.range v) := by
    intro x _
    obtain ⟨m, rfl⟩ := hs x
    rw [hred m]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let bV : Module.Basis (Module.Free.ChooseBasisIndex R M) K V := Module.Basis.mk hli hsp
  have hbV : ∀ i, bV i = red (b i) := fun i => Module.Basis.mk_apply hli hsp i
  haveI : Module.Finite K V := Module.Finite.of_basis bV
  refine ⟨this, ?_⟩
  have hmat : LinearMap.toMatrix bV bV ψ = (LinearMap.toMatrix b b φ).map π := by
    ext i j
    rw [Matrix.map_apply, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply, hbV j, ← h, hred]
    have hv : ∀ i', v i' = bV i' := fun i' => (hbV i').symm
    simp only [hv, map_sum, map_smul, Module.Basis.repr_self, Finsupp.coe_finset_sum, Finset.sum_apply,
      Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    exact mul_one _
  rw [← LinearMap.charpoly_toMatrix ψ bV, hmat, Matrix.charpoly_map, LinearMap.charpoly_toMatrix]

theorem charpoly_dualMap {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Module.Finite K (Module.Dual K V)] (f : Module.End K V) : (f.dualMap).charpoly = f.charpoly := by
  classical
  rw [← LinearMap.charpoly_toMatrix f (Module.finBasis K V),
    ← LinearMap.charpoly_toMatrix f.dualMap (Module.finBasis K V).dualBasis, ← Matrix.charpoly_transpose,
    LinearMap.dualMap_def, LinearMap.toMatrix_transpose, Matrix.transpose_transpose]

end GlobalTheory.DeRhamCharpolyP

namespace GlobalTheory.DeRhamCharpolyP

open GlobalTheory.AV GlobalTheory.PDivGroup in

theorem charpoly_push : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p]
    (B : GlobalTheory.AV.AbVar k) (f : B ⟶ B) [Module.Finite k (HdR B.X)],
    LinearMap.charpoly (push (dp0 k) (𝟙 _) f.hom) = (GlobalTheory.AV.AbVar.charpoly f).map (Int.castRingHom k) := by
  intro p _ k _ _ _ B f _
  obtain ⟨G, -, ⟨t⟩⟩ := GlobalTheory.AVTower.exists_tower p k B
  let T := GlobalTheory.Dieu.theory p
  haveI : Module.Free (WittVector p k) (T.M G) := T.base.free G trivial
  haveI : Module.Finite (WittVector p k) (T.M G) := T.base.finite G trivial
  have h1 := GlobalTheory.Dieu.CharpolyAV.charpoly_map_eq p T k B G t f
  have hπ : Function.Surjective (WittVector.constantCoeff : WittVector p k →+* k) := fun x =>
    ⟨WittVector.teichmuller p x, by simp⟩
  obtain ⟨hfin, h2⟩ := charpoly_of_red (WittVector.constantCoeff : WittVector p k →+* k) hπ p
    (CharP.cast_eq_zero k p) (T.red G) (T.base.red_surjective G trivial) (T.base.red_eq_zero G trivial)
    (T.map (t.map t f.hom)) (rigExtMap (t.map t f.hom)) (fun m => by
      have := T.base.red_smap trivial trivial (SemiHom.ofHom (t.map t f.hom)) m
      rw [SemiHom.ofHom_rig] at this
      exact this)
  obtain ⟨e, he, -, -⟩ := GlobalTheory.deRhamVectorExtension p
  have hR : IsNilpotent (p : k) := by rw [CharP.cast_eq_zero]; exact IsNilpotent.zero
  let E := e hR B.ab t
  haveI : Module.Finite k (primDR B.X) := Module.Finite.equiv E.symm
  have hconj : primPull (dp0 k) (𝟙 _) f.hom = E.symm.conj (rigExtMap (t.map t f.hom)) := by
    refine LinearMap.ext fun c => ?_
    rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_symm, LinearEquiv.eq_symm_apply]
    exact he.primPull hR B.ab B.ab t t f.hom c
  have h3 : (primPull (dp0 k) (𝟙 _) f.hom).charpoly = (rigExtMap (t.map t f.hom)).charpoly := by
    rw [hconj, LinearEquiv.charpoly_conj]
  calc LinearMap.charpoly (push (dp0 k) (𝟙 _) f.hom)
      = ((primPull (dp0 k) (𝟙 _) f.hom).dualMap).charpoly := rfl
    _ = (primPull (dp0 k) (𝟙 _) f.hom).charpoly := charpoly_dualMap _
    _ = (rigExtMap (t.map t f.hom)).charpoly := h3
    _ = ((GlobalTheory.AV.AbVar.charpoly f).map (Int.castRingHom (WittVector p k))).map WittVector.constantCoeff := by
        rw [h2, h1]
    _ = (GlobalTheory.AV.AbVar.charpoly f).map (Int.castRingHom k) := by
        rw [Polynomial.map_map]; congr 1; exact RingHom.ext_int _ _

end GlobalTheory.DeRhamCharpolyP
end
end
