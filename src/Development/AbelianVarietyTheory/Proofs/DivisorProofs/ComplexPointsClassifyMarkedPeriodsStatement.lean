import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorRelDimAndDiagonalIsLineBundleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorModuliObjectPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplexUniformisationHarrisTaylor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectOfPeriodStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordBundleIsoSymmetricBirigidifiedComplStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexFibreExponentialKernelFullLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingEqExpRiemannFormAppellHumbertFrame
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFormsAddOfFactorProduct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHolomorphicUniformisationOfExponentialLatt
import Development.AbelianVarietyTheory.Definitions.Divisors.Uniformised
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeMapGivesHomomorphism
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomomorphismDescendsToAlgebraic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullGenLBIsGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorObjectPullbackCompDiagonalBundleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationAtCorrespondOfCartesianStatement

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_complexUniformisation_harrisTaylor : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (σ : R →+* ℂ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (o : Obj b N (spMap σ)) h hL, 0 < N → N.Coprime p → b.IsType σ ρ → ∃ D' t Q e, D.Cls N D' t ∧ UnifAt (o.fam h hL) σ ρ N D' t Q (𝟙 _) e := by
  first | (exact @GlobalTheory.UPel.HT.Unif.exists_unifAt) | (exact GlobalTheory.UPel.HT.Unif.exists_unifAt) | (intros; apply GlobalTheory.UPel.HT.Unif.exists_unifAt <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilPairing_eq_exp_riemannForm_appellHumbert_frame : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A →
    ∀ (L : LB A.left), L.IsLB →
    ∀ (n : ℕ) (u : HolUnif A L n) (Hm : Matrix (Fin n) (Fin n) ℂ) (χ : u.Λ → ℂ), GlobalTheory.TorusRM.IsFactorAH u Hm χ →
      ∀ (k : ℕ) (a b : Fin n → ℂ) (c : ℂˣ), 0 < k → a ∈ u.Λ → b ∈ u.Λ →
        (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (((a ⬝ᵥ Hm.mulVec (star b)).im : ℝ) : ℂ) / k) →
        Out.WeilIs A L k (u.ex ((k : ℂ)⁻¹ • a)) (u.ex ((k : ℂ)⁻¹ • b)) (unitOn c) := by
  first | exact @GlobalTheory.AHWeilFactor.weilIs_exp_riemannForm | exact GlobalTheory.AHWeilFactor.weilIs_exp_riemannForm | (intros; apply GlobalTheory.AHWeilFactor.weilIs_exp_riemannForm <;> assumption)
end

section
section
open scoped Matrix

namespace GlobalTheory

theorem matrix_eq_of_im_dotProduct_mulVec_star_eq_on_span :
    ∀ (g : ℕ) (H H' : Matrix (Fin g) (Fin g) ℂ) (S : Set (Fin g → ℂ)),
    Submodule.span ℝ S = ⊤ →
    (∀ a ∈ S, ∀ b ∈ S, (a ⬝ᵥ H.mulVec (star b)).im = (a ⬝ᵥ H'.mulVec (star b)).im) → H = H' := by
  intro g H H' S hS h
  set D := H - H' with hD
  have hS0 : ∀ a ∈ S, ∀ b ∈ S, (a ⬝ᵥ D.mulVec (star b)).im = 0 := by
    intro a ha b hb
    simp only [hD, Matrix.sub_mulVec, dotProduct_sub, Complex.sub_im, h a ha b hb, sub_self]
  let B : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ (fun a b => (a ⬝ᵥ D.mulVec (star b)).im)
      (by intro a a' b; simp [add_dotProduct])
      (by intro r a b; simp [smul_dotProduct])
      (by intro a b b'; simp [star_add, Matrix.mulVec_add, dotProduct_add])
      (by intro r a b; simp [star_smul, Matrix.mulVec_smul, dotProduct_smul])
  have hB : B = 0 := by
    apply LinearMap.ext_on hS
    intro a ha
    apply LinearMap.ext_on hS
    intro b hb
    simpa [B] using hS0 a ha b hb
  have hall : ∀ a b, (a ⬝ᵥ D.mulVec (star b)) = 0 := by
    intro a b
    have h1 : (a ⬝ᵥ D.mulVec (star b)).im = 0 := by
      have := congrArg (fun f => f a b) hB
      simpa [B] using this
    have h2 : ((Complex.I • a) ⬝ᵥ D.mulVec (star b)).im = 0 := by
      have := congrArg (fun f => f (Complex.I • a) b) hB
      simpa [B] using this
    rw [smul_dotProduct, smul_eq_mul, Complex.mul_im] at h2
    simp at h2
    exact Complex.ext h2 h1
  have hDz : D = 0 := by
    ext i j
    have := hall (Pi.single i 1) (Pi.single j 1)
    simpa [Matrix.mulVec_single_one, Pi.star_single] using this
  exact sub_eq_zero.mp hDz

end GlobalTheory
end

open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_eq_of_im_dotProduct_mulVec_star_eq_on_span' : ∀ (g : ℕ) (H H' : Matrix (Fin g) (Fin g) ℂ) (S : Set (Fin g → ℂ)),
    Submodule.span ℝ S = ⊤ →
    (∀ a ∈ S, ∀ b ∈ S, (a ⬝ᵥ H.mulVec (star b)).im = (a ⬝ᵥ H'.mulVec (star b)).im) → H = H' := by
  atlas_forward_decl GlobalTheory.matrix_eq_of_im_dotProduct_mulVec_star_eq_on_span
end

section
section
namespace GlobalTheory

theorem exists_int_sub_eq_mul_of_exp_neg_two_pi_I_div_eq (x y : ℝ) (k : ℕ) (hk : 0 < k)
    (h : Complex.exp (-(2 * Real.pi * Complex.I) * (x : ℂ) / k) =
      Complex.exp (-(2 * Real.pi * Complex.I) * (y : ℂ) / k)) :
    ∃ n : ℤ, y - x = n * k := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
  refine ⟨n, ?_⟩
  have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have : ((y - x : ℝ) : ℂ) = ((n * k : ℝ) : ℂ) := by
    push_cast
    field_simp at hn
    linear_combination hn
  exact_mod_cast this

theorem real_eq_of_exp_neg_two_pi_I_div_eq : ∀ x y : ℝ, (∀ k : ℕ, 0 < k →
    Complex.exp (-(2 * Real.pi * Complex.I) * (x : ℂ) / k) = Complex.exp (-(2 * Real.pi * Complex.I) * (y : ℂ) / k)) →
    x = y := by
  intro x y h
  obtain ⟨m, hm⟩ := exists_int_sub_eq_mul_of_exp_neg_two_pi_I_div_eq x y 1 one_pos (h 1 one_pos)
  simp only [Nat.cast_one, mul_one] at hm
  obtain ⟨n, hn⟩ := exists_int_sub_eq_mul_of_exp_neg_two_pi_I_div_eq x y (m.natAbs + 1) (Nat.succ_pos _)
    (h _ (Nat.succ_pos _))
  generalize hK : m.natAbs + 1 = K at hn
  have hmn : m = n * (K : ℤ) := by
    have : ((m : ℤ) : ℝ) = ((n * (K : ℤ) : ℤ) : ℝ) := by push_cast; rw [← hm, hn]
    exact_mod_cast this
  have hm0 : m = 0 := by
    by_contra hne
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hne (by simpa using hmn)
    have h1 : m.natAbs = n.natAbs * K := by
      rw [hmn, Int.natAbs_mul]; simp
    have h2 : 1 ≤ n.natAbs := Int.natAbs_pos.mpr hn0
    nlinarith
  have : y - x = 0 := by rw [hm, hm0]; simp
  linarith

end GlobalTheory
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_of_forall_cexp_neg_two_pi_I_mul_div_eq : ∀ x y : ℝ, (∀ k : ℕ, 0 < k →
    Complex.exp (-(2 * Real.pi * Complex.I) * (x : ℂ) / k) = Complex.exp (-(2 * Real.pi * Complex.I) * (y : ℂ) / k)) →
    x = y := by
  atlas_forward_decl GlobalTheory.real_eq_of_exp_neg_two_pi_I_div_eq
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix

set_option autoImplicit false

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.TorusRM.LamAdd GlobalTheory.ProdUnifSq in

theorem GlobalTheory.TorusRM.lbIso_lam_of_same_form : ∀ (g : ℕ) (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → IsProjOver A.hom →
    ∀ (M M' : LB A.left) (u : HolUnif A M g) (u' : HolUnif A M' g) (Hm : Matrix (Fin g) (Fin g) ℂ)
      (χ : u.Λ → ℂ) (χ' : u'.Λ → ℂ), M.IsLB → M'.IsLB → u'.ex = u.ex →
    GlobalTheory.TorusRM.IsFactorAH u Hm χ → GlobalTheory.TorusRM.IsFactorAH u' Hm χ' → LBIso (abelian₂ A M) (abelian₂ A M') := by
  intro g A _ hA hP M M' u u' Hm χ χ' h1 h2 he f1 f2
  haveI : IsCommMonObj A := hA.comm
  have hl1 : (abelian₂ A M).IsLB := LB.isLB_linComb h1 _ _
  have hl2 : (abelian₂ A M').IsLB := LB.isLB_linComb h2 _ _
  have hPP : IsProjOver (A ⊗ A).hom := GlobalTheory.ProjSpace.isProjOver_pullback hP hP
  refine GlobalTheory.HolUnifSec.hasGen_of_periodic (A ⊗ A) (AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA) hPP _
    (LB.isLB_div hl2 hl1) (g + g)
    (GlobalTheory.SameFactor.divUnif (lamUnif u u rfl) (lamUnif u u' he) rfl)
    (fun _ => 1) (differentiable_const _) (fun _ => one_ne_zero) ?_
  intro l hl p z hz
  obtain ⟨hz2, hz1⟩ := (GlobalTheory.top_le_preimage_inf _ _ _).1 hz
  have hexl : (sqUnif A u).ex (z + l) = (sqUnif A u).ex z := by
    rw [(sqUnif A u).ex_add, ((sqUnif A u).ker l).2 hl, _root_.mul_one]
  have e1 := lam_shift u u rfl h1 f1 p.2 z l hl hz1
  have e2 := lam_shift u u' he h2 f2 p.1 z l hl hz2
  have n1 := (lamUnif u u rfl).fr_ne p.2 (z + l) (by rw [lamUnif_ex, hexl]; exact hz1)
  have n2 := (lamUnif u u' he).fr_ne p.1 (z + l) (by rw [lamUnif_ex, hexl]; exact hz2)
  show 1 * ((lamUnif u u' he).fr p.1 (z + l) * ((lamUnif u u rfl).fr p.2 (z + l))⁻¹) =
    1 * ((lamUnif u u' he).fr p.1 z * ((lamUnif u u rfl).fr p.2 z)⁻¹)
  rw [e1, e2]
  have q1 := Complex.exp_ne_zero (Q Hm z l)
  field_simp
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mumfordBundleIso_of_same_appellHumbert_form : ∀ (g : ℕ) (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → IsProjOver A.hom →
    ∀ (M M' : LB A.left) (u : HolUnif A M g) (u' : HolUnif A M' g) (Hm : Matrix (Fin g) (Fin g) ℂ)
      (χ : u.Λ → ℂ) (χ' : u'.Λ → ℂ), M.IsLB → M'.IsLB → u'.ex = u.ex →
    GlobalTheory.TorusRM.IsFactorAH u Hm χ → GlobalTheory.TorusRM.IsFactorAH u' Hm χ' → LBIso (abelian₂ A M) (abelian₂ A M') := by
  atlas_forward_decl GlobalTheory.TorusRM.lbIso_lam_of_same_form
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix
open GlobalTheory.PELU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_holomorphic_uniformisation_of_exponential_lattice : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (e : (Fin g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A))
    (Λ : Submodule ℤ (Fin g → ℂ)), IsExp (𝟙 (Sp ℂ)) e → DiscreteTopology Λ →
    Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → (∀ z, e z = 1 ↔ z ∈ Λ) →
    ∃ (L₀ : LB A.left) (u₀ : HolUnif A L₀ g), u₀.ex = e := by
  first | exact @GlobalTheory.exists_holUnif_of_isExp | exact GlobalTheory.exists_holUnif_of_isExp | (intros; apply GlobalTheory.exists_holUnif_of_isExp <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

theorem GlobalTheory.biIso_of_weil : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ P P' : LB (G2 A).left, P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → P'.IsLB → (∃ t : (P'.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P'.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P' (P'.pull (lift (snd A A) (fst A A)).left) → ∀ (e : (Fin g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A)) (La : Type) [AddCommGroup La] (Q : La →+ (Fin g → ℂ)) (EF : LinearMap.BilinForm ℤ La), IsExp (𝟙 (Sp ℂ)) e → Function.Injective Q → (∀ z, e z = 1 ↔ z ∈ Q.range) → (∀ (k : ℕ) (a b : La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (EF a b : ℂ) / k) → Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) k (e ((k : ℂ)⁻¹ • Q a)) (e ((k : ℂ)⁻¹ • Q b)) (unitOn c)) → (∀ (k : ℕ) (a b : La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (EF a b : ℂ) / k) → Out.WeilIs A (P'.pull (lift (𝟙 A) (𝟙 A)).left) k (e ((k : ℂ)⁻¹ • Q a)) (e ((k : ℂ)⁻¹ • Q b)) (unitOn c)) → LBIso P P' := by
  intro A _ _ g hA hs P P' hP hP1 hP2 hPs hP' hP'1 hP'2 hP's e La _ Q EF he hQ hker hW hW'
  obtain ⟨Λ, hd, hf, hk⟩ := GlobalTheory.T.complexFibreExponential_kernel_full_lattice (Sp ℂ) A g hA hs (𝟙 _) e he
  obtain ⟨L₀, u₀, hu₀⟩ := GlobalTheory.T.exists_holomorphic_uniformisation_of_exponential_lattice A g e Λ he hd hf hk
  obtain ⟨M, hM, hPM⟩ := GlobalTheory.T.exists_mumford_bundle_iso_symmetric_birigidified_complex A g hA hs P hP hP1 hP2 hPs
  obtain ⟨M', hM', hPM'⟩ := GlobalTheory.T.exists_mumford_bundle_iso_symmetric_birigidified_complex A g hA hs P' hP' hP'1 hP'2 hP's
  obtain ⟨u, Hm, χ, hue, hF⟩ := GlobalTheory.exists_isFactorAH_frame_of_unif A hA L₀ g u₀ M hM
  obtain ⟨u', Hm', χ', hue', hF'⟩ := GlobalTheory.exists_isFactorAH_frame_of_unif A hA L₀ g u₀ M' hM'
  have hp : IsProjOver A.hom := (GlobalTheory.ProjSpace.isProjBy_iff_isProjOver A.hom).1
    (GlobalTheory.AbelianProjective.isProjBy_of_isAbelianScheme ℂ A hA)
  have hL : (abelian₂ A M).IsLB := LB.isLB_linComb hM _ _
  have hL' : (abelian₂ A M').IsLB := LB.isLB_linComb hM' _ _

  have key : ∀ (M : LB A.left) (P : LB (G2 A).left) (u : HolUnif A M g) (Hm : Matrix (Fin g) (Fin g) ℂ)
      (χ : u.Λ → ℂ), M.IsLB → P.IsLB → u.ex = e → GlobalTheory.TorusRM.IsFactorAH u Hm χ →
      LBIso P (cubeLB A ![fst A A, snd A A] M) →
      (∀ (k : ℕ) (a b : La) (c : ℂˣ), 0 < k →
        (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (EF a b : ℂ) / k) →
        Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) k (e ((k : ℂ)⁻¹ • Q a)) (e ((k : ℂ)⁻¹ • Q b)) (unitOn c)) →
      ∀ a b : La, ((Q a) ⬝ᵥ ((2 : ℂ) • Hm).mulVec (star (Q b))).im = (EF a b : ℝ) := by
    intro M P u Hm χ hM hP hue hF hPM hW a b
    have hLM : (abelian₂ A M).IsLB := LB.isLB_linComb hM _ _
    obtain ⟨ud, χd, hude, hFd⟩ := GlobalTheory.TorusRM.exists_isFactorAH_lam_diag g A hA M u Hm χ hM hF
    have mem : ∀ x : La, Q x ∈ ud.Λ := fun x => (ud.ker _).1 (by rw [hude, hue]; exact (hker _).2 ⟨x, rfl⟩)
    refine GlobalTheory.T.eq_of_forall_cexp_neg_two_pi_I_mul_div_eq _ _ fun k hk => ?_
    have h1 := hW k a b (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
    have h2 := GlobalTheory.T.weilPairing_eq_exp_riemannForm_appellHumbert_frame A hA _ (pull_isLB hLM _) g ud _ χd hFd k (Q a) (Q b)
      (Units.mk0 _ (Complex.exp_ne_zero _)) hk (mem a) (mem b) rfl
    rw [hude, hue] at h2
    have hiso : LBIso (P.pull (lift (𝟙 A) (𝟙 A)).left)
        (((abelian₂ A M).pull (lift (𝟙 A) (𝟙 A)).left).pull (𝟙 A : A ⟶ A).left) := by
      refine LBIso.trans (pull_isLB hP _) (pull_isLB hLM _) (pull_isLB (pull_isLB hLM _) _)
        (GlobalTheory.RigidBundleGlue.LBIso.pull hPM _) ?_
      exact GlobalTheory.ThetaAffineGlue.lbIso_pull_id (pull_isLB hLM _)
    have h3 := GlobalTheory.PeriodObject.weilIs_of_lbIso GlobalTheory.globalFns_holds hA (pull_isLB hP _)
      (pull_isLB hLM _) hiso h2
    have := GlobalTheory.weilIs_unique_fieldPoint (Sp ℂ) A _ (pull_isLB hP _) ℂ (𝟙 _) k _ _ _ _ h1 h3
    have := congrArg Units.val this
    simpa using this.symm
  have hH : Hm = Hm' := by
    have e2 := GlobalTheory.T.matrix_eq_of_im_dotProduct_mulVec_star_eq_on_span' g ((2 : ℂ) • Hm) ((2 : ℂ) • Hm') (Set.range Q) ?_ ?_
    · have := congrArg (fun X => (1 / 2 : ℂ) • X) e2
      simpa [smul_smul] using this
    · have hR : Set.range Q = (Λ : Set (Fin g → ℂ)) := by
        ext z
        rw [SetLike.mem_coe, ← hk, hker]
        rfl
      rw [hR]; exact hf
    · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      rw [key M P u Hm χ hM hP (hue.trans hu₀) hF hPM hW a b,
        key M' P' u' Hm' χ' hM' hP' (hue'.trans hu₀) hF' hPM' hW' a b]
  subst hH
  have hlam := GlobalTheory.T.mumfordBundleIso_of_same_appellHumbert_form g A hA hp M M' u u' Hm χ χ' hM hM' (hue'.trans hue.symm) hF hF'
  exact LBIso.trans hP hL hP' hPM (LBIso.trans hL hL' hP' hlam (LBIso.symm hPM'))
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.birigidified_bundle_iso_of_weil_pairing_eq : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ P P' : LB (G2 A).left, P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → P'.IsLB → (∃ t : (P'.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P'.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P' (P'.pull (lift (snd A A) (fst A A)).left) → ∀ (e : (Fin g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A)) (La : Type) [AddCommGroup La] (Q : La →+ (Fin g → ℂ)) (EF : LinearMap.BilinForm ℤ La), IsExp (𝟙 (Sp ℂ)) e → Function.Injective Q → (∀ z, e z = 1 ↔ z ∈ Q.range) → (∀ (k : ℕ) (a b : La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (EF a b : ℂ) / k) → Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) k (e ((k : ℂ)⁻¹ • Q a)) (e ((k : ℂ)⁻¹ • Q b)) (unitOn c)) → (∀ (k : ℕ) (a b : La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (EF a b : ℂ) / k) → Out.WeilIs A (P'.pull (lift (𝟙 A) (𝟙 A)).left) k (e ((k : ℂ)⁻¹ • Q a)) (e ((k : ℂ)⁻¹ • Q b)) (unitOn c)) → LBIso P P' := by
  atlas_forward_decl GlobalTheory.biIso_of_weil
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

namespace GlobalTheory.HomAlgAny

open MeasureTheory

theorem surjective_of_forall_sub_mem {g : ℕ} (T : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (Λ : Submodule ℤ (Fin g → ℂ))
    (hΛ : DiscreteTopology Λ) (h : ∀ x, ∃ z, x - T z ∈ Λ) : Function.Surjective T := by
  by_contra hT
  have hV : (LinearMap.range T).restrictScalars ℝ ≠ ⊤ := by
    intro h'
    apply hT
    intro x
    have hx : x ∈ (LinearMap.range T).restrictScalars ℝ := h' ▸ Submodule.mem_top
    exact LinearMap.mem_range.1 ((Submodule.restrictScalars_mem ℝ _ x).1 hx)
  haveI : Countable Λ := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have hcov : (Set.univ : Set (Fin g → ℂ)) ⊆ ⋃ l : Λ,
      (fun y => y + -(l : Fin g → ℂ)) ⁻¹' (((LinearMap.range T).restrictScalars ℝ : Submodule ℝ (Fin g → ℂ)) : Set (Fin g → ℂ)) := by
    intro x _
    obtain ⟨z, hz⟩ := h x
    refine Set.mem_iUnion.2 ⟨⟨x - T z, hz⟩, ?_⟩
    simp only [Set.mem_preimage, SetLike.mem_coe, Submodule.restrictScalars_mem]
    exact ⟨z, by abel⟩
  have h0 : volume (Set.univ : Set (Fin g → ℂ)) = 0 :=
    measure_mono_null hcov (measure_iUnion_null fun l => by
      rw [measure_preimage_add_right]
      exact Measure.addHaar_submodule volume _ hV)
  exact (isOpen_univ.measure_ne_zero volume Set.univ_nonempty) h0

theorem sub_mem_of_ex_eq {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) (a b : Fin g → ℂ)
    (h : u.ex a = u.ex b) : a - b ∈ u.Λ := by
  rw [← u.ker]
  have e := u.ex_add (a - b) b
  rw [sub_add_cancel, h] at e
  have e2 := congrArg (· * (u.ex b)⁻¹) e
  simpa using e2.symm

theorem exists_of_polAV (P P' : Out.PolAV (Sp ℂ)) (n n' : ℕ) (v : HolUnif P.A P.L n) (v' : HolUnif P'.A P'.L n')
    (F : (Fin n → ℂ) →ₗ[ℂ] (Fin n' → ℂ)) (hn : P.g = n) (hn' : P'.g = n') (hF : ∀ z ∈ v.Λ, F z ∈ v'.Λ) :
    ∃ f : P.A ⟶ P'.A, IsMonHom f ∧ ∀ z, v'.ex (F z) = v.ex z ≫ f := by
  subst hn hn'
  obtain ⟨hL, hL2⟩ := abelianSchemeLaws_all
  obtain ⟨f, ⟨hf, hfe⟩, -⟩ := existsUnique_isMonHom_of_map_lattice hL hL2 AbLaw.CubeAssembly.cube_gen
    thetaUnifAV_all P P' P.L P'.L v v' F hF
  exact ⟨f, hf, hfe⟩

open GlobalTheory.HolUnifEnd GlobalTheory.HolUnifHom in

theorem exists_isMonHom_of_map_lattice (A A' : Over (Sp ℂ)) [GrpObj A] [GrpObj A'] (g g' : ℕ)
    (hA : IsAbelianScheme A) (hA' : IsAbelianScheme A') (hgA : SmoothOfRelativeDimension g A.hom)
    (hgA' : SmoothOfRelativeDimension g' A'.hom) (L : LB A.left) (L' : LB A'.left) (u : HolUnif A L g)
    (u' : HolUnif A' L' g') (M : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (hM : ∀ x ∈ u.Λ, M x ∈ u'.Λ) :
    ∃ α : A ⟶ A', IsMonHom α ∧ ∀ w, u'.ex (M w) = u.ex w ≫ α := by
  obtain ⟨Q, v, i, r, J, R, m, hQ, hi, hr, hm, hJ, hR, hJΛ, hRΛ, hRJ⟩ := exists_linear_factor A g hA hgA L u
  obtain ⟨Q', v', i', r', J', R', m', hQ', hi', hr', hm', hJ', hR', hJΛ', hRΛ', hRJ'⟩ :=
    exists_linear_factor A' g' hA' hgA' L' u'
  obtain ⟨β, hβ, hβe⟩ := exists_of_polAV Q Q' (8 * g) (8 * g') v v' (J' ∘ₗ M ∘ₗ R) hQ hQ'
    (fun l hl => hJΛ' _ (hM _ (hRΛ _ hl)))
  haveI := hi; haveI := hr'; haveI := hβ
  have hφ : ∀ z, u.ex z ≫ i ≫ β ≫ r' = u'.ex ((m' * m) • M z) := by
    intro z
    have e := hβe (J z)
    simp only [LinearMap.comp_apply] at e
    rw [← Category.assoc, ← hJ, ← Category.assoc, ← e, ← hR', hRJ', hRJ, map_nsmul, smul_smul]
  have := hA'.proper
  obtain ⟨α, hα, hαφ⟩ := exists_factor_pow A A' hA (m' * m) (Nat.one_le_iff_ne_zero.2 (by positivity))
    (i ≫ β ≫ r') fun y hy => by
      obtain ⟨z, rfl⟩ := u.ex_onto y
      rw [← holUnif_ex_nsmul_eq_pow, u.ker] at hy
      rw [hφ, u'.ker, ← map_nsmul]
      exact hM _ hy
  refine ⟨α, hα, fun w => ?_⟩
  have hN0 : ((m' * m : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (show m' * m ≠ 0 by positivity)
  have hw : (m' * m) • (((m' * m : ℕ) : ℂ)⁻¹ • w) = w := by
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hN0, one_smul]
  calc u'.ex (M w) = u'.ex ((m' * m) • M (((m' * m : ℕ) : ℂ)⁻¹ • w)) := by rw [← map_nsmul, hw]
    _ = u.ex (((m' * m : ℕ) : ℂ)⁻¹ • w) ≫ i ≫ β ≫ r' := (hφ _).symm
    _ = u.ex (((m' * m : ℕ) : ℂ)⁻¹ • w) ≫ (𝟙 A ^ (m' * m)) ≫ α := by rw [hαφ]
    _ = u.ex w ≫ α := by
      rw [← Category.assoc, MonObj.comp_pow, Category.comp_id, ← holUnif_ex_nsmul_eq_pow, hw]

theorem existsUnique_isMonHom_of_map_ker : ∀ (A A' : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] (g g' : ℕ), IsAbelianScheme A → IsAbelianScheme A' → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g' A'.hom → ∀ (e : (Fin g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A)) (e' : (Fin g' → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A')) (M : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)), IsExp (𝟙 (Sp ℂ)) e → IsExp (𝟙 (Sp ℂ)) e' → (∀ z, e z = 1 → e' (M z) = 1) → ∃! f : A ⟶ A', IsMonHom f ∧ ∀ z, e' (M z) = e z ≫ f := by
  intro A A' _ _ _ _ g g' hA hA' hg hg' e e' M he he' hM
  obtain ⟨L, ⟨u⟩⟩ := GlobalTheory.HomDescentQb.exists_holUnif A g hA hg
  obtain ⟨L', ⟨u'⟩⟩ := GlobalTheory.HomDescentQb.exists_holUnif A' g' hA' hg'
  obtain ⟨t1, t2⟩ := GlobalTheory.TorusTransfer.tangent_bijective u hg
  obtain ⟨t1', t2'⟩ := GlobalTheory.TorusTransfer.tangent_bijective u' hg'
  obtain ⟨T, hT, -⟩ := GlobalTheory.existsUnique_linear_lift_of_isHolTo A hA L g g u t1 t2 e he.1 he.2.2.1
  obtain ⟨T', hT', -⟩ := GlobalTheory.existsUnique_linear_lift_of_isHolTo A' hA' L' g' g' u' t1' t2' e' he'.1 he'.2.2.1
  have hTs : Function.Surjective T := surjective_of_forall_sub_mem T u.Λ u.discrete fun x => by
    obtain ⟨z, hz⟩ := he.2.1 (u.ex x)
    exact ⟨z, sub_mem_of_ex_eq u _ _ (by rw [hT]; exact hz.symm)⟩
  have hTi : Function.Injective T := LinearMap.injective_iff_surjective.2 hTs
  let Te : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ) := LinearEquiv.ofBijective T ⟨hTi, hTs⟩
  have hTe : ∀ z, Te.symm (T z) = z := fun z => Te.symm_apply_apply z
  let F : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ) := T' ∘ₗ M ∘ₗ Te.symm.toLinearMap
  have hFT : ∀ z, F (T z) = T' (M z) := fun z => by simp only [F, LinearMap.comp_apply, LinearEquiv.coe_coe, hTe]
  have hF : ∀ x ∈ u.Λ, F x ∈ u'.Λ := fun x hx => by
    obtain ⟨z, rfl⟩ := hTs x
    rw [hFT, ← u'.ker, hT']
    refine hM z ?_
    rw [← hT, u.ker]
    exact hx
  obtain ⟨α, hα, hαe⟩ := exists_isMonHom_of_map_lattice A A' g g' hA hA' hg hg' L L' u u' F hF
  have hex : ∀ z, e' (M z) = e z ≫ α := fun z => by
    rw [← hT', ← hFT, hαe, hT]
  refine ⟨α, ⟨hα, hex⟩, fun f hf => ?_⟩
  haveI := hA.smooth
  haveI := hA'.proper
  haveI : IsReduced A.left := GlobalTheory.isReduced_of_smooth_complex _ A.hom hA.smooth
  refine GlobalTheory.ComplexPoints.over_hom_ext_of_complexPoints fun x => ?_
  obtain ⟨z, rfl⟩ := he.2.1 x
  rw [← hf.2, hex]

end GlobalTheory.HomAlgAny
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_isMonHom_of_linear_map_kernels : ∀ (A A' : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] (g g' : ℕ), IsAbelianScheme A → IsAbelianScheme A' → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g' A'.hom → ∀ (e : (Fin g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A)) (e' : (Fin g' → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A')) (M : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)), IsExp (𝟙 (Sp ℂ)) e → IsExp (𝟙 (Sp ℂ)) e' → (∀ z, e z = 1 → e' (M z) = 1) → ∃! f : A ⟶ A', IsMonHom f ∧ ∀ z, e' (M z) = e z ≫ f := by
  atlas_forward_decl GlobalTheory.HomAlgAny.existsUnique_isMonHom_of_map_ker
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

namespace GlobalTheory.HTIso

theorem one_comp_monHom {S : Scheme.{0}} {A A' : Over S} [GrpObj A] [GrpObj A'] (f : A ⟶ A') [IsMonHom f] :
    (1 : A ⟶ A) ≫ f = 1 := by
  rw [Hom.one_def, Hom.one_def, Category.assoc, IsMonHom.one_hom]

theorem comp_one' {S : Scheme.{0}} {A A' : Over S} [GrpObj A'] (f : A ⟶ A') : f ≫ (1 : A' ⟶ A') = 1 := by
  rw [Hom.one_def, Hom.one_def, ← Category.assoc, comp_toUnit]

theorem pull_birig : ∀ (S : Scheme.{0}) (A A' : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A']
    (f : A ⟶ A'), IsMonHom f → ∀ P : LB (G2 A').left, P.IsLB →
    (∃ t : (P.pull (lift (1 : A' ⟶ A') (𝟙 A')).left).Gen, t.IsGen) →
    (∃ t : (P.pull (lift (𝟙 A') (1 : A' ⟶ A')).left).Gen, t.IsGen) →
    LBIso P (P.pull (lift (snd A' A') (fst A' A')).left) →
    (P.pull (lift (fst A A ≫ f) (snd A A ≫ f)).left).IsLB ∧
    (∃ t : ((P.pull (lift (fst A A ≫ f) (snd A A ≫ f)).left).pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) ∧
    (∃ t : ((P.pull (lift (fst A A ≫ f) (snd A A ≫ f)).left).pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) ∧
    LBIso (P.pull (lift (fst A A ≫ f) (snd A A ≫ f)).left)
      ((P.pull (lift (fst A A ≫ f) (snd A A ≫ f)).left).pull (lift (snd A A) (fst A A)).left) := by
  intro S A A' _ _ _ _ f hf P hP ⟨t₁, ht₁⟩ ⟨t₂, ht₂⟩ hs
  haveI := hf
  set φ₂ := (lift (fst A A ≫ f) (snd A A ≫ f)).left with hφ₂
  have hP₂ : (P.pull φ₂).IsLB := pull_isLB hP _

  have triv : ∀ (l : A ⟶ G2 A) (l' : A' ⟶ G2 A'), l ≫ lift (fst A A ≫ f) (snd A A ≫ f) = f ≫ l' →
      ∀ t : (P.pull l'.left).Gen, t.IsGen → ∃ s : ((P.pull φ₂).pull l.left).Gen, s.IsGen := by
    intro l l' hl t ht
    have e₁ : LBIso (P.pull (f.left ≫ l'.left)) ((P.pull l'.left).pull f.left) :=
      GlobalTheory.GenSpread.lbIso_pull_pull hP f.left rfl
    have e₂ : LBIso (P.pull (f.left ≫ l'.left)) ((P.pull φ₂).pull l.left) :=
      GlobalTheory.GenSpread.lbIso_pull_pull hP l.left (by rw [hφ₂, ← Over.comp_left, ← Over.comp_left, hl])
    obtain ⟨s, hs⟩ := GlobalTheory.RigidTranslate.gen_of_lbIso (pull_isLB (pull_isLB hP _) _) (pull_isLB hP _) e₁.symm
      (pullGenLB t f.left) (pullGenLB_isGen ht f.left)
    exact GlobalTheory.RigidTranslate.gen_of_lbIso (pull_isLB hP _) (pull_isLB hP₂ _) e₂ s hs
  refine ⟨hP₂, triv _ _ ?_ t₁ ht₁, triv _ _ ?_ t₂ ht₂, ?_⟩
  · apply CartesianMonoidalCategory.hom_ext <;> simp [one_comp_monHom, comp_one']
  · apply CartesianMonoidalCategory.hom_ext <;> simp [one_comp_monHom, comp_one']
  · have eq : (lift (snd A A) (fst A A)).left ≫ φ₂ = φ₂ ≫ (lift (snd A' A') (fst A' A')).left := by
      rw [hφ₂, ← Over.comp_left, ← Over.comp_left]
      congr 1
      apply CartesianMonoidalCategory.hom_ext <;> simp
    have e₁ : LBIso (P.pull φ₂) ((P.pull (lift (snd A' A') (fst A' A')).left).pull φ₂) :=
      GlobalTheory.GenSpread.lbIso_pullback hs φ₂
    have e₂ : LBIso (P.pull (φ₂ ≫ (lift (snd A' A') (fst A' A')).left))
        ((P.pull (lift (snd A' A') (fst A' A')).left).pull φ₂) :=
      GlobalTheory.GenSpread.lbIso_pull_pull hP φ₂ rfl
    have e₃ : LBIso (P.pull (φ₂ ≫ (lift (snd A' A') (fst A' A')).left)) ((P.pull φ₂).pull (lift (snd A A) (fst A A)).left) :=
      GlobalTheory.GenSpread.lbIso_pull_pull hP _ eq.symm
    exact LBIso.trans hP₂ (pull_isLB (pull_isLB hP _) _) (pull_isLB hP₂ _) e₁
      (LBIso.trans (pull_isLB (pull_isLB hP _) _) (pull_isLB hP _) (pull_isLB hP₂ _) e₂.symm e₃)

theorem weil_pull_iso : ∀ (S : Scheme.{0}) (A A' : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A']
    (F : A ≅ A'), IsMonHom F.hom → ∀ P : LB (G2 A').left, P.IsLB → ∀ (T : Over S) (k : ℤ) (x y : T ⟶ A)
    (c : Γ(T.left, ⊤)ˣ), Out.WeilIs A' (P.pull (lift (𝟙 A') (𝟙 A')).left) k (x ≫ F.hom) (y ≫ F.hom) c →
    Out.WeilIs A ((P.pull (lift (fst A A ≫ F.hom) (snd A A ≫ F.hom)).left).pull (lift (𝟙 A) (𝟙 A)).left) k x y c := by
  intro S A A' _ _ _ _ F hF P hP T k x y c H
  haveI := hF
  set φ₂ := (lift (fst A A ≫ F.hom) (snd A A ≫ F.hom)).left with hφ₂
  have eq : (lift (𝟙 A) (𝟙 A)).left ≫ φ₂ = F.hom.left ≫ (lift (𝟙 A') (𝟙 A')).left := by
    rw [hφ₂, ← Over.comp_left, ← Over.comp_left]
    congr 1
    apply CartesianMonoidalCategory.hom_ext <;> simp
  have e₁ : LBIso (P.pull ((lift (𝟙 A) (𝟙 A)).left ≫ φ₂)) ((P.pull φ₂).pull (lift (𝟙 A) (𝟙 A)).left) :=
    GlobalTheory.GenSpread.lbIso_pull_pull hP _ rfl
  have e₂ : LBIso (P.pull ((lift (𝟙 A) (𝟙 A)).left ≫ φ₂)) ((P.pull (lift (𝟙 A') (𝟙 A')).left).pull F.hom.left) :=
    GlobalTheory.GenSpread.lbIso_pull_pull hP _ eq
  have iso := LBIso.trans (pull_isLB (pull_isLB hP _) _) (pull_isLB hP _) (pull_isLB (pull_isLB hP _) _) e₁.symm e₂
  let x₀ : Over.mk (T.hom ≫ 𝟙 S) ⟶ A' := Over.homMk (x.left ≫ F.hom.left) (by simp)
  let y₀ : Over.mk (T.hom ≫ 𝟙 S) ⟶ A' := Over.homMk (y.left ≫ F.hom.left) (by simp)
  refine (GlobalTheory.weilIs_iff_of_isGrpPullback_comm S S A' A (𝟙 S) F.hom.left _ _ (pull_isLB hP _)
    (pull_isLB (pull_isLB hP _) _) (isGrpPullback_of_iso F) iso T k x y x₀ y₀ c rfl rfl).2 ?_
  exact GlobalTheory.UnifPoint.weilIs_congr (Category.comp_id _).symm rfl rfl H

theorem nonempty_objMap_of_markedIsom : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (σ : R →+* ℂ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (o o' : Obj b N (spMap σ)) h hL h' hL' (D' D'' : PLat D.O D.inv) t t' Q Q' e e' (w : D'.La ≃ₗ[D.O] D''.La) (u : (Fin D.g → ℂ) ≃ₗ[ℂ] (Fin D.g → ℂ)), 0 < N → UnifAt (o.fam h hL) σ ρ N D' t Q (𝟙 _) e → UnifAt (o'.fam h' hL') σ ρ N D'' t' Q' (𝟙 _) e' → IsMarkedIsom N D' D'' t t' w → (∀ x, Q' (w x) = u (Q x)) → Nonempty (ObjMap o o' (𝟙 _)) := by
  rintro p _ D R _ b N σ ρ o o' h hL h' hL' D' D'' t t' Q Q' e e' w u hN0
    ⟨-, hP, he, hk, hl, hw, hη⟩ ⟨-, hP', he', hk', hl', hw', hη'⟩ ⟨hiso, hmark⟩ hu

  have k1 : ∀ z, e z = 1 → e' (u z) = 1 := by
    intro z hz
    obtain ⟨x, rfl⟩ := (hk z).1 hz
    exact (hk' _).2 ⟨w x, hu x⟩
  have k2 : ∀ z, e' z = 1 → e (u.symm z) = 1 := by
    intro z hz
    obtain ⟨x, rfl⟩ := (hk' z).1 hz
    refine (hk _).2 ⟨w.symm x, ?_⟩
    apply u.injective
    rw [u.apply_symm_apply, ← hu, w.apply_symm_apply]
  obtain ⟨f, ⟨hf, hfe⟩, -⟩ := GlobalTheory.T.existsUnique_isMonHom_of_linear_map_kernels o.A o'.A D.g D.g o.ab o'.ab h h' e e' u.toLinearMap he he' k1
  obtain ⟨f', ⟨hf', hfe'⟩, -⟩ := GlobalTheory.T.existsUnique_isMonHom_of_linear_map_kernels o'.A o.A D.g D.g o'.ab o.ab h' h e' e u.symm.toLinearMap he' he k2
  obtain ⟨f₀, -, uid⟩ := GlobalTheory.T.existsUnique_isMonHom_of_linear_map_kernels o.A o.A D.g D.g o.ab o.ab h h e e LinearMap.id he he (fun z hz => hz)
  obtain ⟨f₀', -, uid'⟩ := GlobalTheory.T.existsUnique_isMonHom_of_linear_map_kernels o'.A o'.A D.g D.g o'.ab o'.ab h' h' e' e' LinearMap.id he' he' (fun z hz => hz)
  have hfe2 : ∀ z, e' (u z) = e z ≫ f := hfe
  have hfe2' : ∀ z, e (u.symm z) = e' z ≫ f' := hfe'
  haveI := hf
  haveI := hf'
  have c1 : f ≫ f' = 𝟙 _ := by
    rw [uid (f ≫ f') ⟨inferInstance, fun z => ?_⟩, uid (𝟙 _) ⟨inferInstance, fun z => (Category.comp_id _).symm⟩]
    refine Eq.trans ?_ (Category.assoc (e z) f f')
    rw [← hfe2]
    exact (by rw [u.symm_apply_apply]; rfl : e (LinearMap.id z) = e (u.symm (u z))).trans (hfe2' (u z))
  have c2 : f' ≫ f = 𝟙 _ := by
    rw [uid' (f' ≫ f) ⟨inferInstance, fun z => ?_⟩, uid' (𝟙 _) ⟨inferInstance, fun z => (Category.comp_id _).symm⟩]
    refine Eq.trans ?_ (Category.assoc (e' z) f' f)
    rw [← hfe2']
    exact (by rw [u.apply_symm_apply]; rfl : e' (LinearMap.id z) = e' (u (u.symm z))).trans (hfe2 (u.symm z))
  let F : o.A ≅ o'.A := ⟨f, f', c1, c2⟩
  haveI : IsMonHom F.hom := hf

  have hcomm : ∀ (c : D.O) z, u (ρ c *ᵥ z) = ρ c *ᵥ u z := by
    intro c
    have := LinearMap.ext_on_range (R := ℝ) (v := fun x => Q x) hP.2.2.2.1
      (f := (u.toLinearMap ∘ₗ Matrix.toLin' (ρ c)).restrictScalars ℝ)
      (g := (Matrix.toLin' (ρ c) ∘ₗ u.toLinearMap).restrictScalars ℝ) (fun x => by
        simp only [LinearMap.restrictScalars_apply, LinearMap.comp_apply, Matrix.toLin'_apply, LinearEquiv.coe_coe]
        rw [← hP.1, ← hu, ← hu, w.map_smul, hP'.1])
    intro z
    simpa using LinearMap.congr_fun this z
  have hact : ∀ c, o.act.act c ≫ f = f ≫ o'.act.act c := by
    intro c
    haveI := o.act.hom c
    haveI := o'.act.hom c
    obtain ⟨fa, -, ua⟩ := GlobalTheory.T.existsUnique_isMonHom_of_linear_map_kernels o.A o'.A D.g D.g o.ab o'.ab h h' e e'
      (u.toLinearMap ∘ₗ Matrix.toLin' (ρ c)) he he' (fun z hz => by
        obtain ⟨x, rfl⟩ := (hk z).1 hz
        simp only [LinearMap.comp_apply, Matrix.toLin'_apply, LinearEquiv.coe_coe]
        rw [← hP.1]
        exact k1 _ ((hk _).2 ⟨_, rfl⟩))
    rw [ua (o.act.act c ≫ f) ⟨inferInstance, fun z => ?_⟩, ua (f ≫ o'.act.act c) ⟨inferInstance, fun z => ?_⟩]
    · simp only [LinearMap.comp_apply, Matrix.toLin'_apply, LinearEquiv.coe_coe]
      refine Eq.trans ?_ (Category.assoc (e z) f (o'.act.act c))
      rw [← hfe2, hcomm]
      exact hl' c (u z)
    · simp only [LinearMap.comp_apply, Matrix.toLin'_apply, LinearEquiv.coe_coe]
      refine Eq.trans ?_ (Category.assoc (e z) (o.act.act c) f)
      rw [hfe2]
      exact congrArg (· ≫ f) (hl c z)
  have hT : (toUnit (Over.mk (𝟙 (Sp ℂ)))).left = 𝟙 _ := by
    simpa using Over.w (toUnit (Over.mk (𝟙 (Sp ℂ))))
  have heta : ∀ y, (o.eta y).left ≫ f.left = 𝟙 _ ≫ (o'.eta y).left := by
    intro y
    obtain ⟨e₀, he₀⟩ := hmark y
    have hN : (N : ℂ) ≠ 0 := by exact_mod_cast hN0.ne'
    have hη2 : toUnit (Over.mk (𝟙 (Sp ℂ))) ≫ o.eta y = e ((N : ℂ)⁻¹ • Q (t y)) := hη y
    have hη2' : toUnit (Over.mk (𝟙 (Sp ℂ))) ≫ o'.eta y = e' ((N : ℂ)⁻¹ • Q' (t' y)) := hη' y
    have a1 : (toUnit (Over.mk (𝟙 (Sp ℂ))) ≫ o.eta y) ≫ f = toUnit (Over.mk (𝟙 (Sp ℂ))) ≫ o'.eta y := by
      refine (congrArg (· ≫ f) hη2).trans ((hfe2 _).symm.trans (Eq.trans ?_ hη2'.symm))
      have hz : (N : ℂ)⁻¹ • N • Q' e₀ = Q' e₀ := by
        rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hN, one_smul]
      rw [map_smul, ← hu, he₀, map_add, map_nsmul, smul_add, hz, he'.1, (hk' (Q' e₀)).2 ⟨e₀, rfl⟩, _root_.mul_one]
    have a2 := congrArg (fun q => q.left) a1
    simp only [Over.comp_left, hT, Category.id_comp] at a2
    rw [Category.id_comp]
    exact a2
  obtain ⟨B1, B2, B3, B4⟩ := pull_birig (Sp ℂ) o.A o'.A f hf o'.P o'.isLB o'.rig₁ o'.rig₂ o'.symm
  have ew : ∀ (k : ℕ) a, e' ((k : ℂ)⁻¹ • Q' (w a)) = e ((k : ℂ)⁻¹ • Q a) ≫ f := by
    intro k a
    rw [hu, ← u.map_smul]
    exact hfe2 _
  have pol := GlobalTheory.T.birigidified_bundle_iso_of_weil_pairing_eq o.A D.g o.ab h o.P (o'.P.pull (lift (fst o.A o.A ≫ f) (snd o.A o.A ≫ f)).left)
    o.isLB o.rig₁ o.rig₂ o.symm B1 B2 B3 B4 e D'.La Q D'.EF he hP.2.1 hk hw (fun k a a₂ c hk0 hc => by
      have W' := hw' k (w a) (w a₂) c hk0 (by rw [hiso]; exact hc)
      rw [ew, ew] at W'
      exact weil_pull_iso (Sp ℂ) o.A o'.A F inferInstance o'.P o'.isLB _ k _ _ _ W')
  exact ⟨{ φ := f.left
           φ₂ := (lift (fst o.A o.A ≫ f) (snd o.A o.A ≫ f)).left
           cart := isGrpPullback_of_iso F
           sq := ⟨by rw [← Over.comp_left, lift_fst, Over.comp_left], by rw [← Over.comp_left, lift_snd, Over.comp_left]⟩
           act := fun c => by rw [← Over.comp_left, hact c, Over.comp_left]
           pol := pol
           eta := heta }⟩

end GlobalTheory.HTIso
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_moduliMap_of_marked_period_isometry : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (σ : R →+* ℂ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (o o' : Obj b N (spMap σ)) h hL h' hL' (D' D'' : PLat D.O D.inv) t t' Q Q' e e' (w : D'.La ≃ₗ[D.O] D''.La) (u : (Fin D.g → ℂ) ≃ₗ[ℂ] (Fin D.g → ℂ)), 0 < N → UnifAt (o.fam h hL) σ ρ N D' t Q (𝟙 _) e → UnifAt (o'.fam h' hL') σ ρ N D'' t' Q' (𝟙 _) e' → IsMarkedIsom N D' D'' t t' w → (∀ x, Q' (w x) = u (Q x)) → Nonempty (ObjMap o o' (𝟙 _)) := by
  atlas_forward_decl GlobalTheory.HTIso.nonempty_objMap_of_markedIsom
end

section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT

theorem Model.fineAt_univ : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ)
    (σ : R →+* ℂ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (M : Model b N) h hL, 0 < N → N.Coprime p →
    b.IsType σ ρ → FineAt (M.univ.fam h hL) σ ρ N (D.Cls N) := by
  intro p _ D R _ b N σ ρ M h hL hN hNp hty
  have tr : ∀ (o : Obj b N (spMap σ)) (y : Sp ℂ ⟶ M.X) (m : ObjMap o M.univ y), y ≫ M.s = spMap σ →
      ∀ h' hL' (D' : PLat D.O D.inv) t Q,
        (∀ e', UnifAt (o.fam h' hL') σ ρ N D' t Q (𝟙 _) e' → ∃ e, UnifAt (M.univ.fam h hL) σ ρ N D' t Q y e) ∧
        (∀ e, UnifAt (M.univ.fam h hL) σ ρ N D' t Q y e → ∃ e', UnifAt (o.fam h' hL') σ ρ N D' t Q (𝟙 _) e') := by
    intro o y m hy h' hL' D' t Q
    have key := GlobalTheory.T.uniformisationAt_correspond_of_cartesian D.O D.inv D.g ρ R R σ σ D.La (M.univ.fam h hL) (o.fam h' hL') N y m.φ m.cart m.act
      ((GlobalTheory.T.harrisTaylorObjectPullback_comp_diagonalBundle p D R b N M.X (Sp ℂ) (Sp ℂ) M.s (spMap σ) (spMap σ) M.univ o o y (𝟙 _)).2 m) m.eta D' t Q (𝟙 _)
      (Category.id_comp _) (by erw [Category.id_comp]; exact hy)
    erw [Category.id_comp] at key
    exact ⟨fun e' he' => (key.1 e' he').imp fun e he => he.1, fun e he => (key.2 e he).imp fun e' he' => he'.1⟩
  refine ⟨?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨o, ⟨m⟩⟩ := GlobalTheory.T.exists_harrisTaylorModuliObject_pullback p D R b N M.X (Sp ℂ) M.s (spMap σ) y hy M.univ
    obtain ⟨h', hL'⟩ := GlobalTheory.T.harrisTaylor_relDim_and_diagonal_isLineBundle p D R b N (Sp ℂ) (spMap σ) o
    obtain ⟨D', t, Q, e, hC, hU⟩ := GlobalTheory.T.exists_complexUniformisation_harrisTaylor p D R b N σ ρ o h' hL' hN hNp hty
    obtain ⟨e2, he2⟩ := (tr o y m hy h' hL' D' t Q).1 e hU
    exact ⟨D', t, Q, e2, hC, he2⟩
  · intro D' t Q hC hQ
    obtain ⟨o, h', hL', e, hU⟩ := GlobalTheory.T.exists_harrisTaylor_object_of_period p D R b N σ ρ D' t Q hN hNp hty hC hQ
    obtain ⟨f, ⟨hf, ⟨m⟩⟩, -⟩ := M.rep (Sp ℂ) (spMap σ) o
    obtain ⟨e2, he2⟩ := (tr o f m hf h' hL' D' t Q).1 e hU
    exact ⟨f, e2, he2⟩
  · intro D' D'' t t' Q Q' y y' e e' hU hU' w u hw hQ
    have hy : y ≫ M.s = spMap σ := hU.1
    have hy' : y' ≫ M.s = spMap σ := hU'.1
    obtain ⟨o1, ⟨m1⟩⟩ := GlobalTheory.T.exists_harrisTaylorModuliObject_pullback p D R b N M.X (Sp ℂ) M.s (spMap σ) y hy M.univ
    obtain ⟨o2, ⟨m2⟩⟩ := GlobalTheory.T.exists_harrisTaylorModuliObject_pullback p D R b N M.X (Sp ℂ) M.s (spMap σ) y' hy' M.univ
    obtain ⟨h1, hL1⟩ := GlobalTheory.T.harrisTaylor_relDim_and_diagonal_isLineBundle p D R b N (Sp ℂ) (spMap σ) o1
    obtain ⟨h2, hL2⟩ := GlobalTheory.T.harrisTaylor_relDim_and_diagonal_isLineBundle p D R b N (Sp ℂ) (spMap σ) o2
    obtain ⟨e1, he1⟩ := (tr o1 y m1 hy h1 hL1 D' t Q).2 e hU
    obtain ⟨e2, he2⟩ := (tr o2 y' m2 hy' h2 hL2 D'' t' Q').2 e' hU'
    obtain ⟨m12⟩ := GlobalTheory.T.nonempty_moduliMap_of_marked_period_isometry p D R b N σ ρ o1 o2 h1 hL1 h2 hL2 D' D'' t t' Q Q' e1 e2 w u hN he1 he2 hw hQ
    have hc := (GlobalTheory.T.harrisTaylorObjectPullback_comp_diagonalBundle p D R b N M.X (Sp ℂ) (Sp ℂ) M.s (spMap σ) (spMap σ) M.univ o2 o1 y' (𝟙 _)).1
      ⟨m12⟩ ⟨m2⟩
    obtain ⟨f, -, huniq⟩ := M.rep (Sp ℂ) (spMap σ) o1
    have e1' := huniq y ⟨hy, ⟨m1⟩⟩
    have e2' := huniq (𝟙 _ ≫ y') ⟨by erw [Category.id_comp]; exact hy', hc⟩
    erw [Category.id_comp] at e2'
    rw [e1', e2']

end GlobalTheory.UPel.HT
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complexPoints_classify_markedPeriods : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (σ : R →+* ℂ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (M : Model b N) h hL, 0 < N → N.Coprime p → b.IsType σ ρ → FineAt (M.univ.fam h hL) σ ρ N (D.Cls N) := by
  first | (exact @GlobalTheory.UPel.HT.Model.fineAt_univ) | (exact GlobalTheory.UPel.HT.Model.fineAt_univ) | (intros; apply GlobalTheory.UPel.HT.Model.fineAt_univ <;> assumption)
end
