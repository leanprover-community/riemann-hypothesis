import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsHalfIdem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussSumNondegenerateFiniteHermitianModule
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexMapNsmulComapEqAbsNormDet
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteRationalPointsCompletedLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralComplexGaussianPosDefHermitianPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormSqEqToL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaTildeHeckeCharSplitMulSignOfNormFormula
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalIsometryVacuumScalarGaussSumIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteWeilRepEqLatticeIntertwinerMulCharacter
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticFormUnitaryPairAction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedHomLatticeMultipleMemOpenLevel
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MeanSquareAddFundamentalDomainOfCocompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurLemmaThetaFunctionsOrientedPairStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitaryMatrixEqProdQuasiReflections
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero

section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndex_map_nsmul_comap_eq_abs_norm_pow_mul_det : ∀ (E Γ : Type) [Field E] [NumberField E] [AddCommGroup Γ] [Module E Γ] [FiniteDimensional E Γ] (A : AddSubgroup Γ), A.FG → (∀ x : Γ, ∃ N : ℕ, 0 < N ∧ N • x ∈ A) → ∀ (m : Module.End E Γ) (N : ℕ), N ≠ 0 → LinearMap.det m ≠ 0 → (∀ x ∈ A, N • m x ∈ A) → (((A.map (N • AddMonoidHom.id Γ)).relIndex (A.comap m.toAddMonoidHom) : ℕ) : ℚ) = |Algebra.norm ℚ ((N : E) ^ Module.finrank E Γ * LinearMap.det m)| := by
  first | exact @GlobalTheory.relIndex_map_nsmul_comap_eq_abs_norm_det | exact GlobalTheory.relIndex_map_nsmul_comap_eq_abs_norm_det | (intros; apply GlobalTheory.relIndex_map_nsmul_comap_eq_abs_norm_det <;> assumption)
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts GlobalTheory.FinWeil GlobalTheory.FinWeilO GlobalTheory.FockCompare GlobalTheory.VacUnique GlobalTheory.RatAut
open scoped TensorProduct Kronecker ComplexOrder nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RatLattice

open GlobalTheory.SplitScalar GlobalTheory.CompletedLatticeFinite

theorem relIndex_comap_comap {G H : Type} [AddCommGroup G] [AddCommGroup H] (f : G →+ H) (A B : AddSubgroup H)
    (h : ∀ b ∈ B, ∃ x, f x ∈ B ∧ b - f x ∈ A) : (A.comap f).relIndex (B.comap f) = A.relIndex B := by
  rw [AddSubgroup.relIndex_comap, ← AddSubgroup.relIndex_sup_right B A,
    ← AddSubgroup.relIndex_sup_right ((B.comap f).map f) A]
  congr 1
  refine le_antisymm (sup_le_sup_right (AddSubgroup.map_comap_le _ _) _) (sup_le (fun b hb => ?_) le_sup_right)
  obtain ⟨x, hx, hb⟩ := h b hb
  rw [← add_sub_cancel (f x) b]
  exact AddSubgroup.add_mem_sup ⟨x, hx, rfl⟩ hb

theorem fg_of_denom {E : Type} [Field E] [NumberField E] {m n : ℕ} (L : AddSubgroup (Matrix (Fin m) (Fin n) E))
    (d : E) (hd : d ≠ 0) (h : ∀ x ∈ L, ∀ i j, IsIntegral ℤ (d * x i j)) : L.FG := by
  let f : Matrix (Fin m) (Fin n) (𝓞 E) →+ Matrix (Fin m) (Fin n) E :=
    AddMonoidHom.mk' (fun x => Matrix.of fun i j => d⁻¹ * (x i j : E)) fun x y => by
      ext i j
      simp [mul_add]
  have e : L = (L.comap f).map f := by
    refine (AddSubgroup.map_comap_eq_self fun x hx => ⟨Matrix.of fun i j => ⟨d * x i j, h x hx i j⟩, ?_⟩).symm
    ext i j
    show d⁻¹ * (d * x i j) = x i j
    rw [inv_mul_cancel_left₀ hd]
  have h1 : (AddSubgroup.toIntSubmodule (L.comap f)).FG := IsNoetherian.noetherian _
  have h2 := h1.map f.toIntLinearMap
  rw [e]
  exact (Submodule.fg_iff_addSubgroup_fg _).1 h2

variable {D : D7} {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
  {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}

theorem exists_denom_latQ (hS : ΛS.FG) (hT : ΛT.FG) :
    ∃ d : D.host.E, d ≠ 0 ∧ ∀ x ∈ latQ S T ΛS ΛT, ∀ i j, IsIntegral ℤ (d * x i j) := by
  classical
  obtain ⟨dS, hdS, hS'⟩ := exists_denom ΛS hS
  obtain ⟨dT, hdT, hT'⟩ := exists_denom ΛT hT
  obtain ⟨dA, hdA, hA'⟩ := D.host.AA.2
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ
    ((Finset.univ : Finset (Fin S.rank × Fin S.rank)).image fun p => S.gram p.1 p.2)
  have hdA0 : (dA : D.host.E) ≠ 0 := by
    have := nonZeroDivisors.ne_zero hdA
    exact_mod_cast this
  have hd : (dA : D.host.E) * dT * (star dS * (y : D.host.E)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hdA0 hdT) (mul_ne_zero (star_ne_zero.2 hdS) (by exact_mod_cast hy0))
  set d : D.host.E := (dA : D.host.E) * dT * (star dS * (y : D.host.E)) with hdd
  have hgen : ∀ a ∈ D.host.AA, ∀ s ∈ ΛS, ∀ t ∈ ΛT, ∀ i j,
      IsIntegral ℤ (d * (a * t i * ∑ k, star (s k) * S.gram k j)) := by
    intro a ha s hs t ht i j
    have e : d * (a * t i * ∑ k, star (s k) * S.gram k j) =
        ((dA : D.host.E) * a) * (dT * t i) * ∑ k, star (dS * s k) * ((y : D.host.E) * S.gram k j) := by
      simp only [hdd, Finset.mul_sum, star_mul]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [e]
    refine IsIntegral.mul (IsIntegral.mul ?_ (hT' t ht i)) (IsIntegral.sum _ fun k _ =>
      (isIntegral_star D (hS' s hs k)).mul ?_)
    · obtain ⟨b, hb⟩ := hA' a ha
      have : (dA : D.host.E) * a = (b : D.host.E) := hb.symm
      rw [this]
      exact b.isIntegral_coe
    · have := hy (S.gram k j) (Finset.mem_image.2 ⟨(k, j), Finset.mem_univ _, rfl⟩)
      simpa [zsmul_eq_mul] using this
  have hlat : ∀ l ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True),
      ∀ i j, finPart D (l i j) ∈ GlobalTheory.AdLat.hat1 D.host.F
        ((FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ d⁻¹ : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : Set D.host.E) := by
    intro l hl i j
    induction hl using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩ := hw
      exact AddSubgroup.subset_closure ⟨α, hα, _, (mem_spanSingleton_inv d hd _).2 (hgen a ha s hs t ht i j), rfl⟩
    | zero => rw [Matrix.zero_apply, RingHom.map_zero]; exact zero_mem _
    | add x z _ _ hx hz => rw [Matrix.add_apply, RingHom.map_add]; exact add_mem hx hz
    | neg x _ hx => rw [Matrix.neg_apply, RingHom.map_neg]; exact neg_mem hx
  exact ⟨d, hd, fun x hx i j =>
    (mem_spanSingleton_inv d hd _).1 (((GlobalTheory.AdLat.adelicCompletion_fractionalIdeal_properties D.host.F D.host.E).2.1 _ (x i j)).1 (hlat _ hx i j))⟩

theorem exists_rat_add_nsmul (Λ : AddSubgroup (WO S T)) (hinf : ∀ u ∈ Λ, u.map (infPart D) = 0)
    (happ : ∀ γ : WO S T, γ.map (infPart D) = 0 → ∃ ρ ∈ ratL T S, ∃ u ∈ Λ, (γ - ρ - u).map (finPart D) = 0)
    {z : WO S T} (hz : z.map (infPart D) = 0) {N : ℕ} (hN : 0 < N) :
    ∃ y, ∃ u ∈ Λ, z = finRat S T y + N • u := by
  obtain ⟨γ, hγ, hNγ⟩ := GlobalTheory.RatSelfDual.exists_div hz hN
  obtain ⟨ρ, ⟨y₀, hy₀⟩, u, hu, hz⟩ := happ γ hγ
  have hγe : γ = finRat S T y₀ + u := by
    refine Matrix.ext fun i j => adele_ext ?_ ?_
    · have e0 : infPart D (γ i j) = 0 := congrFun (congrFun hγ i) j
      have e1 : infPart D (finRat S T y₀ i j) = 0 := congrFun (congrFun (finRat_inf S T y₀) i) j
      have e2 : infPart D (u i j) = 0 := congrFun (congrFun (hinf u hu) i) j
      rw [Matrix.add_apply, RingHom.map_add, e0, e1, e2, add_zero]
    · have e0 : finPart D (γ i j - ρ i j - u i j) = 0 := congrFun (congrFun hz i) j
      have e1 : finPart D (finRat S T y₀ i j) = finPart D (ρ i j) := by rw [← hy₀]; rfl
      rw [RingHom.map_sub, RingHom.map_sub, sub_sub, sub_eq_zero] at e0
      rw [Matrix.add_apply, RingHom.map_add, e1, e0]
  exact ⟨N • y₀, u, hu, by rw [← hNγ, hγe, nsmul_add, (finRat S T).map_nsmul]⟩

theorem actO_inv_actO (g : GA D S) (h : GA D T) (x : XF S T) :
    rhoF S T (g, h) (rhoF S T (g⁻¹, h⁻¹) x) = x ∧ rhoF S T (g⁻¹, h⁻¹) (rhoF S T (g, h) x) = x := by
  constructor
  · rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_inv_cancel, mul_inv_cancel, Prod.mk_one_one, map_one,
      Module.End.one_apply]
  · rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, inv_mul_cancel, inv_mul_cancel, Prod.mk_one_one, map_one,
      Module.End.one_apply]

theorem mem_map_rhoF (A : Submodule (𝓞 D.host.E) (XF S T)) (g : GA D S) (h : GA D T) (x : XF S T) :
    x ∈ A.map (rhoF S T (g, h)) ↔ rhoF S T (g⁻¹, h⁻¹) x ∈ A :=
  ⟨fun ⟨y, hy, e⟩ => by rwa [← e, (actO_inv_actO g h y).2], fun hx => ⟨_, hx, (actO_inv_actO g h x).1⟩⟩

def finX (S T : HSp D) : Matrix (Fin T.rank) (Fin S.rank) D.host.E →+ XF S T :=
  AddMonoidHom.mk' (fun x => XF.mk (finRat S T x) (finRat_inf S T x)) fun x y => XF.ext ((finRat S T).map_add x y)

theorem rhoF_finX {g : GA D S} {h : GA D T} {a : Matrix (Fin S.rank) (Fin S.rank) D.host.E}
    {b : Matrix (Fin T.rank) (Fin T.rank) D.host.E} (ha : Formalism.L2.Theta.mt S g = a.map (incA D))
    (hb : Formalism.L2.Theta.mt T h⁻¹ = b.map (incA D)) (x : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    rhoF S T (g⁻¹, h⁻¹) (finX S T x) = finX S T (b * x * a) := by
  apply XF.ext
  show actO S T g⁻¹ h⁻¹ (finRat S T x) = finRat S T (b * x * a)
  rw [finRat_eq, finRat_eq, actO_smul, actO, inv_inv, ha, hb]
  congr 1
  exact ((Matrix.map_mul (f := incA D)).trans (congrArg (· * a.map (incA D)) (Matrix.map_mul (f := incA D)))).symm

theorem latQ_selfDual_fg_full_index : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → SelfDual (gamQ ψ S T) (latQ S T ΛS ΛT) ∧ (latQ S T ΛS ΛT).toAddSubgroup.FG ∧ (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ N : ℕ, 0 < N ∧ N • x ∈ latQ S T ΛS ΛT) ∧ ∀ (g : GA D S) (h : GA D T) (a : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (b : Matrix (Fin T.rank) (Fin T.rank) D.host.E), Formalism.L2.Theta.mt S g = a.map (incA D) → Formalism.L2.Theta.mt T h⁻¹ = b.map (incA D) → idx (latF S T ΛS ΛT) ((latF S T ΛS ΛT).map (rhoF S T (g, h))) = (latQ S T ΛS ΛT).toAddSubgroup.relIndex ((latQ S T ΛS ΛT).toAddSubgroup.comap (sandw b a).toAddMonoidHom) := by
  intro D ψ hψ S T ΛS ΛT hS hT
  obtain ⟨hdual, happ, -⟩ := GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T ΛS ΛT hψ hS hT
  have hden := GlobalTheory.VacUnique.Den.exists_nsmul_finRat_mem D S T ΛS ΛT hS.1 hT.1
  refine ⟨fun x => ?_, ?_, fun x => ?_, fun g h a b ha hb => ?_⟩
  · refine (GlobalTheory.RatSelfDual.finRat_mem_iff D S T ψ _ hψ (fun u hu => latO_fin hu) hdual happ hden x).trans ?_
    exact forall₂_congr fun y _ => (GlobalTheory.RatSelfDual.psi_fin_iff hψ S T x y).symm
  · obtain ⟨d, hd, h⟩ := exists_denom_latQ (S := S) (T := T) hS.1.fg hT.1.fg
    exact fg_of_denom _ d hd h
  · obtain ⟨N, hN, h⟩ := hden x
    exact ⟨N, hN, by rwa [mem_latQ, map_nsmul]⟩
  · obtain ⟨N, hN, hmov⟩ := (GlobalTheory.LatLevel.level_of_generators D S T ΛS ΛT hS hT
      (GlobalTheory.LatFinGen.latO_finitely_generated D S T ΛS ΛT hS hT)).2 g⁻¹ h⁻¹
    rw [GlobalTheory.FinWeil.idx, ← relIndex_comap_comap (finX S T)]
    · congr 1
      refine AddSubgroup.ext fun x => (mem_map_rhoF _ g h (finX S T x)).trans ?_
      rw [rhoF_finX ha hb]
      rfl
    · intro z hz
      obtain ⟨y, u, hu, e⟩ := exists_rat_add_nsmul _ (fun u hu => latO_fin hu) happ z.fin hN
      have e' : z = finX S T y + N • XF.mk u (latO_fin hu) := XF.ext e
      have h1 : N • XF.mk u (latO_fin hu) ∈ (latF S T ΛS ΛT).map (rhoF S T (g, h)) := by
        rw [mem_map_rhoF, map_nsmul]
        exact hmov u hu
      refine ⟨y, ?_, ?_⟩
      · rw [← sub_eq_iff_eq_add.2 e']
        exact sub_mem hz h1
      · rw [sub_eq_iff_eq_add'.2 e']
        exact nsmul_mem (show XF.mk u (latO_fin hu) ∈ latF S T ΛS ΛT from hu) N

end GlobalTheory.RatLattice

end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts GlobalTheory.FinWeil GlobalTheory.FinWeilO GlobalTheory.FockCompare GlobalTheory.VacUnique GlobalTheory.RatAut
open scoped TensorProduct Kronecker ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_lattice_selfDual_fg_full_index : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → SelfDual (gamQ ψ S T) (latQ S T ΛS ΛT) ∧ (latQ S T ΛS ΛT).toAddSubgroup.FG ∧ (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ N : ℕ, 0 < N ∧ N • x ∈ latQ S T ΛS ΛT) ∧ ∀ (g : GA D S) (h : GA D T) (a : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (b : Matrix (Fin T.rank) (Fin T.rank) D.host.E), Formalism.L2.Theta.mt S g = a.map (incA D) → Formalism.L2.Theta.mt T h⁻¹ = b.map (incA D) → idx (latF S T ΛS ΛT) ((latF S T ΛS ΛT).map (rhoF S T (g, h))) = (latQ S T ΛS ΛT).toAddSubgroup.relIndex ((latQ S T ΛS ΛT).toAddSubgroup.comap (sandw b a).toAddMonoidHom) := by
  first | exact @GlobalTheory.RatLattice.latQ_selfDual_fg_full_index | exact GlobalTheory.RatLattice.latQ_selfDual_fg_full_index | (intros; apply GlobalTheory.RatLattice.latQ_selfDual_fg_full_index <;> assumption)
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts GlobalTheory.FinWeil GlobalTheory.FinWeilO GlobalTheory.FockCompare GlobalTheory.VacUnique GlobalTheory.RatAut
open scoped TensorProduct Kronecker ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RatAut.RealInt

open GlobalTheory.RealWeil

section Mat

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def expM (H s g : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (1 / 2 : ℂ) • ((g - 1)ᴴ * (H * s) * (g - 1) - H * g + (H * g)ᴴ)

theorem expM_herm {H s g : Matrix ι ι ℂ} (hQ : (H * s).PosDef) (hd : (g - 1).det ≠ 0) :
    (expM H s g + (expM H s g)ᴴ).PosDef := by
  have e : expM H s g + (expM H s g)ᴴ = (g - 1)ᴴ * (H * s) * (g - 1) := by
    have h1 : ((g - 1)ᴴ * (H * s) * (g - 1))ᴴ = (g - 1)ᴴ * (H * s) * (g - 1) := by
      rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hQ.1.eq]
      simp only [Matrix.mul_assoc]
    unfold expM
    rw [conjTranspose_smul, conjTranspose_add, conjTranspose_sub _ (H * g), h1, conjTranspose_conjTranspose]
    have : star (1 / 2 : ℂ) = 1 / 2 := by simp
    rw [this]
    module
  rw [e]
  exact hQ.conjTranspose_mul_mul_same
    (mulVec_injective_iff_isUnit.2 ((isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hd)))

theorem expM_mul {H s g g' : Matrix ι ι ℂ} (hH : Hᴴ = H) (hs : s * s = 1) (hg : gᴴ * H * g = H)
    (hc : s * g = g * s) (hi : g * g' = 1) :
    expM H s g * (g * ((1 / 2 : ℂ) • ((1 + s) * g') + (1 / 2 : ℂ) • (1 - s))) = -H * (g - 1) := by
  have hi' : g' * g = 1 := mul_eq_one_comm.1 hi
  have h1 : gᴴ * H = H * g' := by
    calc gᴴ * H = gᴴ * H * g * g' := by rw [Matrix.mul_assoc _ g, hi, Matrix.mul_one]
      _ = _ := by rw [hg]
  have hc' : g' * s = s * g' := by
    calc g' * s = g' * (s * g) * g' := by rw [Matrix.mul_assoc, Matrix.mul_assoc, hi, Matrix.mul_one]
      _ = _ := by rw [hc, ← Matrix.mul_assoc, hi', Matrix.one_mul]
  have a1 : ∀ x : Matrix ι ι ℂ, gᴴ * (H * x) = H * (g' * x) := fun x => by rw [← Matrix.mul_assoc, h1, Matrix.mul_assoc]
  have a2 : ∀ x : Matrix ι ι ℂ, g * (s * x) = s * (g * x) := fun x => by rw [← Matrix.mul_assoc, ← hc, Matrix.mul_assoc]
  have a3 : ∀ x : Matrix ι ι ℂ, g' * (s * x) = s * (g' * x) := fun x => by rw [← Matrix.mul_assoc, hc', Matrix.mul_assoc]
  have a4 : ∀ x : Matrix ι ι ℂ, s * (s * x) = x := fun x => by rw [← Matrix.mul_assoc, hs, Matrix.one_mul]
  have a5 : ∀ x : Matrix ι ι ℂ, g' * (g * x) = x := fun x => by rw [← Matrix.mul_assoc, hi', Matrix.one_mul]
  unfold expM
  simp only [conjTranspose_mul, conjTranspose_sub, conjTranspose_one, hH, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc,
    a1, h1, a2, a3, a4, a5, hi, hi', ← hc, hc', hs, Matrix.neg_mul]
  module

theorem dot_expM {H s g : Matrix ι ι ℂ} (hH : Hᴴ = H) (hQ : (H * s).PosDef) (z : ι → ℂ) :
    star z ⬝ᵥ expM H s g *ᵥ z = Complex.I * ((-(star z ⬝ᵥ H *ᵥ (g *ᵥ z)).im : ℝ) : ℂ) +
      (1 / 2 : ℂ) * ((-(star (Complex.I • s *ᵥ (g *ᵥ z - z)) ⬝ᵥ H *ᵥ (g *ᵥ z - z)).im : ℝ) : ℂ) := by
  have e1 : (g - 1) *ᵥ z = g *ᵥ z - z := by rw [sub_mulVec, one_mulVec]
  have e2 : star z ⬝ᵥ ((g - 1)ᴴ * (H * s) * (g - 1)) *ᵥ z = star (g *ᵥ z - z) ⬝ᵥ (H * s) *ᵥ (g *ᵥ z - z) := by
    rw [← e1, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]
  have e3 : star z ⬝ᵥ (H * g)ᴴ *ᵥ z = star (star z ⬝ᵥ H *ᵥ (g *ᵥ z)) := by
    rw [mulVec_mulVec, ← star_dotProduct_star, star_star, star_mulVec, ← dotProduct_mulVec]
  have e4 : ∀ w : ι → ℂ, star (Complex.I • s *ᵥ w) ⬝ᵥ H *ᵥ w = -Complex.I * (star w ⬝ᵥ (H * s) *ᵥ w) := fun w => by
    rw [star_smul, smul_dotProduct, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, ← hQ.1.eq, conjTranspose_mul, hH]
    simp
  have e5 : (star (g *ᵥ z - z) ⬝ᵥ (H * s) *ᵥ (g *ᵥ z - z)).im = 0 :=
    (Complex.nonneg_iff.1 (hQ.posSemidef.dotProduct_mulVec_nonneg _)).2.symm
  unfold expM
  rw [smul_mulVec, add_mulVec, sub_mulVec, dotProduct_smul, dotProduct_add, dotProduct_sub, e2, e3, e4, ← mulVec_mulVec z H g]
  generalize star (g *ᵥ z - z) ⬝ᵥ (H * s) *ᵥ (g *ᵥ z - z) = u at e5
  generalize star z ⬝ᵥ H *ᵥ (g *ᵥ z) = w
  apply Complex.ext <;> simp [e5] <;> ring

theorem gauss_det {H s g g' : Matrix ι ι ℂ} (hH : Hᴴ = H) (hs : s * s = 1) (hQ : (H * s).PosDef) (hg : gᴴ * H * g = H)
    (hc : s * g = g * s) (hi : g * g' = 1) (hd : (g - 1).det ≠ 0) :
    (expM H s g).det⁻¹ * (g - 1).det = ((H * s).det.re⁻¹ : ℝ) * (-s).det * (g.det * dP s g') := by
  have h0 := (GlobalTheory.MatrixGaussian.integral_gaussian ι _ (expM_herm hQ hd)).1
  have h1 := congrArg det (expM_mul hH hs hg hc hi)
  rw [det_mul, det_mul, det_mul] at h1
  have h2 : (-H).det * (-s).det = (H * s).det := by rw [← det_mul, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
  have h3 := hQ.det_pos
  have h4 : ((H * s).det.re : ℂ) = (H * s).det := Complex.ext rfl (Complex.pos_iff.1 h3).2
  rw [Complex.ofReal_inv, h4]
  have h5 := h3.ne'
  unfold dP
  field_simp
  rw [← h2]
  linear_combination (-(-s).det) * h1

end Mat

section Coord

variable {O : Type} [Fintype O] [DecidableEq O] {m n : ℕ}

def unvE (O : Type) (m n : ℕ) : ((Fin m × Fin n) × O → ℂ) ≃L[ℝ] (O → Fin m → Fin n → ℂ) :=
  ContinuousLinearEquiv.equivOfInverse unvecL vecL vecL_unv unv_vecL

omit [DecidableEq O] in

theorem integral_unv (f : (O → Fin m → Fin n → ℂ) → ℂ) (hf : Integrable fun z : (Fin m × Fin n) × O → ℂ => f (unvecL z)) :
    Integrable f ∧ ∃ c : ℝ, 0 < c ∧ ∫ v, f v = c * ∫ z : (Fin m × Fin n) × O → ℂ, f (unvecL z) := by
  haveI i1 : (volume : Measure (Fin n → ℂ)).IsAddHaarMeasure := inferInstance
  haveI i2 : (volume : Measure (Fin m → Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI i3 : (volume : Measure (O → Fin m → Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  let e := unvE O m n
  have he : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  have hm := Measure.isAddLeftInvariant_eq_smul (volume : Measure (O → Fin m → Fin n → ℂ)) (Measure.map e volume)
  have hp := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure (volume : Measure (O → Fin m → Fin n → ℂ))
    (Measure.map e volume)
  generalize Measure.addHaarScalarFactor (volume : Measure (O → Fin m → Fin n → ℂ)) (Measure.map e volume) = c at hm hp
  refine ⟨?_, c, hp, ?_⟩
  · rw [hm]
    exact (he.integrable_map_iff.2 hf).smul_measure_nnreal
  · conv_lhs => rw [hm]
    rw [integral_smul_nnreal_measure, he.integral_map]
    rfl

theorem det_blk (b : O → Matrix (Fin m) (Fin m) ℂ) (a : O → Matrix (Fin n) (Fin n) ℂ) :
    (blk b a).det = ∏ τ, (b τ ⊗ₖ (a τ)ᵀ).det := det_blockDiagonal _

theorem det_blk_sub_one (b : O → Matrix (Fin m) (Fin m) ℂ) (a : O → Matrix (Fin n) (Fin n) ℂ) :
    (blk b a - 1).det = ∏ τ, (b τ ⊗ₖ (a τ)ᵀ - 1).det := by
  unfold RealWeil.blk
  rw [← blockDiagonal_one, ← blockDiagonal_sub, det_blockDiagonal]
  rfl

theorem inv_unitary {G a a' : Matrix (Fin n) (Fin n) ℂ} (hG : IsUnit G.det) (hi : a * a' = 1) (ha : aᴴ * G * a = G) :
    a * (G⁻¹ * aᴴ) = G⁻¹ := by
  have h1 : a'ᴴ * aᴴ = 1 := by rw [← conjTranspose_mul, hi, conjTranspose_one]
  have h2 : G * a = a'ᴴ * G := by
    conv_rhs => rw [← ha, Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  refine (inv_eq_right_inv ?_).symm
  rw [← Matrix.mul_assoc, h2, Matrix.mul_assoc, ← Matrix.mul_assoc G, mul_nonsing_inv _ hG, Matrix.one_mul, h1]

end Coord

open Classical in
theorem gaussR_unv {D : D7} {S T : HSp D} {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ}
    {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ} (hQ : (HM S T * blk sT sS).PosDef)
    (a : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (b : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (z : Ix S T → ℂ) : gaussR S T sS sT a b (unvecL z) =
      Complex.exp (-(Real.pi : ℂ) * (star z ⬝ᵥ expM (HM S T) (blk sT sS) (blk b a) *ᵥ z)) := by
  have e1 : actR S T a b (unvecL z) = unvecL (blk b a *ᵥ z) := funext fun τ => (cpt_blk b a z τ).symm
  have e2 : ∀ w : Ix S T → ℂ, jO S T sS sT (unvecL w) = unvecL (Complex.I • blk sT sS *ᵥ w) := fun w => funext fun τ => by
    show Complex.I • (sT τ * cpt w τ * sS τ) = _
    rw [← cpt_blk]
    rfl
  unfold gaussR
  rw [dot_expM HM_herm hQ, im_HM, im_HM, e1, ← map_sub, e2, ← Complex.exp_add, neg_neg, neg_neg]
  congr 1
  ring

open Classical in

theorem integral_gaussR : ∀ (D : D7) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → ∃ ε : ℂ, ∀ (a a' : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (b b' : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ τ, a τ * a' τ = 1 ∧ b τ * b' τ = 1 ∧ (a τ)ᴴ * gramAt D S τ * a τ = gramAt D S τ ∧ (b τ)ᴴ * gramAt D T τ * b τ = gramAt D T τ ∧ sS τ * a τ = a τ * sS τ ∧ sT τ * b τ = b τ * sT τ ∧ (b τ ⊗ₖ (a τ)ᵀ - 1).det ≠ 0) → Integrable (gaussR S T sS sT a b) volume ∧ ∃ r : ℝ, 0 < r ∧ (∫ v, gaussR S T sS sT a b v) * ∏ τ, (b τ ⊗ₖ (a τ)ᵀ - 1).det = r * ε * ∏ τ, ((b τ ⊗ₖ (a τ)ᵀ).det * detPlus (sS τ) (sT τ) (a' τ) (b' τ)) := by
  intro D S T sS sT hS hT
  refine ⟨(-blk sT sS).det, fun a a' b b' h => ?_⟩
  obtain ⟨hs, hQ⟩ := HM_cartan hS hT
  have hd : (blk b a - 1).det ≠ 0 := by
    rw [det_blk_sub_one]
    exact Finset.prod_ne_zero_iff.2 fun τ _ => (h τ).2.2.2.2.2.2
  have hi : blk b a * blk b' a' = 1 := by
    rw [blk_mul, ← blk_one]
    congr 1 <;> funext τ
    · exact (h τ).2.1
    · exact mul_eq_one_comm.1 (h τ).1
  have hc : blk sT sS * blk b a = blk b a * blk sT sS := by
    rw [blk_mul, blk_mul]
    congr 1 <;> funext τ
    · exact (h τ).2.2.2.2.2.1
    · exact (h τ).2.2.2.2.1.symm
  have hg : (blk b a)ᴴ * HM S T * blk b a = HM S T := by
    unfold HM
    rw [blk_conjTranspose, blk_mul, blk_mul]
    congr 1 <;> funext τ
    · rw [Matrix.mul_smul, Matrix.smul_mul, (h τ).2.2.2.1]
    · exact inv_unitary (GlobalTheory.SmoothForms.RealPts.gramAt_unit S τ) (h τ).1 (h τ).2.2.1
  obtain ⟨-, h1, h2⟩ := GlobalTheory.MatrixGaussian.integral_gaussian _ _ (expM_herm hQ hd)
  simp only [← gaussR_unv hQ] at h1 h2
  obtain ⟨h3, c, hc0, h4⟩ := integral_unv _ h1
  refine ⟨h3, c * (HM S T * blk sT sS).det.re⁻¹, mul_pos hc0 (inv_pos.2 (Complex.pos_iff.1 hQ.det_pos).1), ?_⟩
  rw [h4, h2, ← det_blk_sub_one, mul_assoc, gauss_det HM_herm hs hQ hg hc hi hd, Finset.prod_mul_distrib, ← det_blk,
    ← detPlus_blockDiagonal, Complex.ofReal_mul]
  ring

end GlobalTheory.RatAut.RealInt

end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts GlobalTheory.FinWeil GlobalTheory.FinWeilO GlobalTheory.FockCompare GlobalTheory.VacUnique GlobalTheory.RatAut
open scoped TensorProduct Kronecker ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_gaussian_real_isometry_no_fixed : ∀ (D : D7) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → ∃ ε : ℂ, ∀ (a a' : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (b b' : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ τ, a τ * a' τ = 1 ∧ b τ * b' τ = 1 ∧ (a τ)ᴴ * gramAt D S τ * a τ = gramAt D S τ ∧ (b τ)ᴴ * gramAt D T τ * b τ = gramAt D T τ ∧ sS τ * a τ = a τ * sS τ ∧ sT τ * b τ = b τ * sT τ ∧ (b τ ⊗ₖ (a τ)ᵀ - 1).det ≠ 0) → Integrable (gaussR S T sS sT a b) volume ∧ ∃ r : ℝ, 0 < r ∧ (∫ v, gaussR S T sS sT a b v) * ∏ τ, (b τ ⊗ₖ (a τ)ᵀ - 1).det = r * ε * ∏ τ, ((b τ ⊗ₖ (a τ)ᵀ).det * detPlus (sS τ) (sT τ) (a' τ) (b' τ)) := by
  first | exact @GlobalTheory.RatAut.RealInt.integral_gaussR | exact GlobalTheory.RatAut.RealInt.integral_gaussR | (intros; apply GlobalTheory.RatAut.RealInt.integral_gaussR <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts GlobalTheory.FinWeil GlobalTheory.FinWeilO GlobalTheory.FockCompare GlobalTheory.VacUnique GlobalTheory.RatAut
open scoped TensorProduct Kronecker ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaTildeHeckeChar_split_mul_sign_of_norm_formula : ∀ (D : D7) (η : (AE D)ˣ →* Circle), IsEtaTilde D η → ∀ (lam : ℕ →* ℂ), GoodNorm (GlobalTheory.FinWeil.sgO D) lam → (∀ n : ℕ, n ≠ 0 → (∀ q : ℕ, q.Prime → Formalism.MainNotions.StandardLatticesGL3.InertQ D q → ¬ q ∣ n) → lam n = (Real.sqrt n : ℂ)) → ∀ ε, IsHalfIdem D ε → ∀ (x : D.host.E) (k : ℕ), x ≠ 0 → (k : ℚ) = |Algebra.norm ℚ x| → ∀ y : (AE D)ˣ, (y : AE D) = (ε + cA D ε) * incA D x + (1 - (ε + cA D ε)) → ∃ r : ℝ, 0 < r ∧ (η y : ℂ) * lam k * ∏ τ, tauE D τ x = r := by
  first | exact @GlobalTheory.EtaProduct.eta_split_mul_lam_pos | exact GlobalTheory.EtaProduct.eta_split_mul_lam_pos | (intros; apply GlobalTheory.EtaProduct.eta_split_mul_lam_pos <;> assumption)
end

section
section
open Matrix Formalism.IndefR.Datum
open scoped ComplexOrder MatrixOrder

namespace GlobalTheory.CartanRefl

theorem exists_sign {k : ℕ} {G : Matrix (Fin k) (Fin k) ℂ} (hG : G.IsHermitian) (hd : G.det ≠ 0) :
    ∃ s, IsCartanInv G s ∧ ∀ u, u * G = G * u → u * s = s * u := by
  classical
  let U : Matrix (Fin k) (Fin k) ℂ := hG.eigenvectorUnitary.1
  have h1 : U * star U = 1 := hG.eigenvectorUnitary.2.2
  have h2 : star U * U = 1 := hG.eigenvectorUnitary.2.1
  have hs : G = U * diagonal (fun i => (hG.eigenvalues i : ℂ)) * star U := by
    have := hG.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  have hne : ∀ i, hG.eigenvalues i ≠ 0 := fun i hi => by
    rw [hG.det_eq_prod_eigenvalues] at hd
    exact hd (Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi]))
  have mul : ∀ a b : Fin k → ℂ, (U * diagonal a * star U) * (U * diagonal b * star U) =
      U * diagonal (fun i => a i * b i) * star U := fun a b => by
    calc _ = U * (diagonal a * (star U * U) * diagonal b) * star U := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h2, Matrix.mul_one, diagonal_mul_diagonal]
  let e : Fin k → ℝ := fun i => if 0 < hG.eigenvalues i then 1 else -1
  have he : ∀ i, (e i : ℂ) * e i = 1 := fun i => by
    simp only [e]; split_ifs <;> simp
  have hh : (U * diagonal (fun i => (e i : ℂ)) * star U)ᴴ = U * diagonal (fun i => (e i : ℂ)) * star U := by
    simp [Matrix.conjTranspose_mul, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.mul_assoc,
      Pi.star_def]
  refine ⟨U * diagonal (fun i => (e i : ℂ)) * star U, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [mul]
    simp only [he, diagonal_one, Matrix.mul_one, h1]
  · rw [hh]
    conv_lhs => rw [hs]
    conv_rhs => rw [hs]
    rw [mul, mul]
    congr 3
    funext i
    rw [mul_right_comm, he, one_mul]
  · conv => arg 1; arg 1; rw [hs]
    rw [mul]
    have hp : (diagonal fun i => (hG.eigenvalues i : ℂ) * e i).PosDef := by
      rw [Matrix.posDef_diagonal_iff]
      intro i
      rw [← Complex.ofReal_mul, Complex.zero_lt_real]
      simp only [e]
      split_ifs with h
      · simpa using h
      · have := lt_of_le_of_ne (not_lt.1 h) (hne i)
        linarith
    have hu : IsUnit (star U) := ⟨⟨star U, U, h2, h1⟩, rfl⟩
    have := hp.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hu)
    rwa [Matrix.star_eq_conjTranspose, conjTranspose_conjTranspose, ← Matrix.star_eq_conjTranspose] at this
  · intro u hu
    obtain ⟨v, rfl⟩ : ∃ v, u = U * v * star U := ⟨star U * u * U, by
      calc u = (U * star U) * u * (U * star U) := by rw [h1, Matrix.one_mul, Matrix.mul_one]
        _ = _ := by simp only [Matrix.mul_assoc]⟩
    have cm : ∀ a b : Matrix (Fin k) (Fin k) ℂ, (U * a * star U) * (U * b * star U) = U * (a * b) * star U := fun a b => by
      calc _ = U * (a * (star U * U) * b) * star U := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [h2, Matrix.mul_one]
    have inj : ∀ a b : Matrix (Fin k) (Fin k) ℂ, U * a * star U = U * b * star U → a = b := fun a b h => by
      have key : ∀ a : Matrix (Fin k) (Fin k) ℂ, star U * (U * a * star U) * U = a := fun a => by
        calc _ = (star U * U) * a * (star U * U) := by simp only [Matrix.mul_assoc]
          _ = a := by rw [h2, Matrix.one_mul, Matrix.mul_one]
      rw [← key a, h, key]
    have hv : v * diagonal (fun i => (hG.eigenvalues i : ℂ)) = diagonal (fun i => (hG.eigenvalues i : ℂ)) * v := by
      apply inj
      rw [← cm, ← cm, ← hs, hu]
    rw [cm, cm]
    congr 2
    ext i j
    have hij := congrFun (congrFun hv i) j
    rw [mul_diagonal, diagonal_mul] at hij ⊢
    by_cases h0 : v i j = 0
    · simp [h0]
    · have : hG.eigenvalues j = hG.eigenvalues i := by
        rw [mul_comm] at hij
        exact_mod_cast mul_right_cancel₀ h0 hij
      simp only [e, this, mul_comm]

theorem exists_comm {k : ℕ} {G r : Matrix (Fin k) (Fin k) ℂ} (hG : Gᴴ = G) (hd : G.det ≠ 0)
    (hr : r * r = 1) (hrG : rᴴ * G * r = G) : ∃ s, IsCartanInv G s ∧ s * r = r * s := by
  classical
  have hH : (1 + rᴴ * r).PosDef := PosDef.one.add_posSemidef (posSemidef_conjTranspose_mul_self r)
  obtain ⟨C, hC, hCH⟩ := CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp hH.isStrictlyPositive
  obtain ⟨⟨C, B, hCB, hBC⟩, rfl⟩ := hC
  simp only [star_eq_conjTranspose] at hCH
  have hCB' : Bᴴ * Cᴴ = 1 := by rw [← conjTranspose_mul, hCB, conjTranspose_one]
  have hBC' : Cᴴ * Bᴴ = 1 := by rw [← conjTranspose_mul, hBC, conjTranspose_one]
  have hr' : rᴴ * rᴴ = 1 := by rw [← conjTranspose_mul, hr, conjTranspose_one]
  have e1 : ∀ X : Matrix (Fin k) (Fin k) ℂ, C * (B * X) = X := fun X => by rw [← Matrix.mul_assoc, hCB, Matrix.one_mul]
  have e2 : ∀ X : Matrix (Fin k) (Fin k) ℂ, B * (C * X) = X := fun X => by rw [← Matrix.mul_assoc, hBC, Matrix.one_mul]
  have e3 : ∀ X : Matrix (Fin k) (Fin k) ℂ, Bᴴ * (Cᴴ * X) = X := fun X => by rw [← Matrix.mul_assoc, hCB', Matrix.one_mul]
  have e4 : ∀ X : Matrix (Fin k) (Fin k) ℂ, Cᴴ * (Bᴴ * X) = X := fun X => by rw [← Matrix.mul_assoc, hBC', Matrix.one_mul]
  have e5 : ∀ X : Matrix (Fin k) (Fin k) ℂ, r * (r * X) = X := fun X => by rw [← Matrix.mul_assoc, hr, Matrix.one_mul]
  have e6 : ∀ X : Matrix (Fin k) (Fin k) ℂ, rᴴ * (G * (r * X)) = G * X := fun X => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hrG]
  have hinv : rᴴ * (Cᴴ * C) * r = Cᴴ * C := by
    rw [← hCH, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, ← Matrix.mul_assoc, hr', Matrix.one_mul, hr, add_comm]
  have huu : (C * r * B) * (C * r * B) = 1 := by
    simp only [Matrix.mul_assoc, e2, e5, hCB]
  have hsu : (C * r * B)ᴴ * (C * r * B) = 1 := by
    calc _ = Bᴴ * (rᴴ * (Cᴴ * C) * r) * B := by simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hinv]; simp only [Matrix.mul_assoc, e3, hCB]
  have hu : (C * r * B)ᴴ = C * r * B := by
    calc _ = (C * r * B)ᴴ * ((C * r * B) * (C * r * B)) := by rw [huu, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, hsu, Matrix.one_mul]
  have hG' : (Bᴴ * G * B).IsHermitian := isHermitian_conjTranspose_mul_mul B hG
  have hd' : (Bᴴ * G * B).det ≠ 0 := by
    intro h
    apply hd
    have : G = Cᴴ * (Bᴴ * G * B) * C := by simp only [Matrix.mul_assoc, e4, hBC, Matrix.mul_one]
    rw [this, det_mul, det_mul, h, mul_zero, zero_mul]
  have hc : (C * r * B) * (Bᴴ * G * B) = (Bᴴ * G * B) * (C * r * B) := by
    have : (C * r * B)ᴴ * (Bᴴ * G * B) * (C * r * B) = Bᴴ * G * B := by
      simp only [conjTranspose_mul, Matrix.mul_assoc, e4, e2, e6]
    rw [hu] at this
    conv_lhs => rw [← this]
    rw [← Matrix.mul_assoc (C * r * B), ← Matrix.mul_assoc (C * r * B), huu, Matrix.one_mul]
  obtain ⟨s, ⟨hs1, hs2, hs3⟩, hs4⟩ := exists_sign hG' hd'
  have hs5 := hs4 _ hc
  refine ⟨B * s * C, ⟨?_, ?_, ?_⟩, ?_⟩
  · calc _ = B * (s * s) * C := by simp only [Matrix.mul_assoc, e1]
      _ = 1 := by rw [hs1, Matrix.mul_one, hBC]
  · calc _ = Cᴴ * (sᴴ * (Bᴴ * G * B) * s) * C := by simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = G := by rw [hs2]; simp only [Matrix.mul_assoc, e4, hBC, Matrix.mul_one]
  · have hu : IsUnit C := ⟨⟨C, B, hCB, hBC⟩, rfl⟩
    have := hs3.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hu)
    simpa only [Matrix.mul_assoc, e4] using this
  · calc _ = B * (s * (C * r * B)) * C := by simp only [Matrix.mul_assoc, hBC, Matrix.mul_one]
      _ = _ := by rw [← hs5]; simp only [Matrix.mul_assoc, e2]

theorem exists_cartan_comm_quasiReflection : ∀ (n : ℕ) (G : Matrix (Fin n) (Fin n) ℂ), Gᴴ = G → G.det ≠ 0 → ∀ x : Fin n → ℂ, star x ⬝ᵥ G *ᵥ x ≠ 0 → ∃ s, IsCartanInv G s ∧ ∀ c : ℂ, s * (1 + c • Matrix.vecMulVec x (star x ᵥ* G)) = (1 + c • Matrix.vecMulVec x (star x ᵥ* G)) * s := by
  intro n G hG hd x hx
  set q := star x ⬝ᵥ G *ᵥ x with hq
  have hM : Matrix.vecMulVec x (star x ᵥ* G) = Matrix.vecMulVec x (star x) * G := by
    rw [vecMulVec_mul]
  have hN : (Matrix.vecMulVec x (star x))ᴴ = Matrix.vecMulVec x (star x) := by
    rw [conjTranspose_vecMulVec, star_star]
  have hMM : Matrix.vecMulVec x (star x ᵥ* G) * Matrix.vecMulVec x (star x ᵥ* G) = q • Matrix.vecMulVec x (star x ᵥ* G) := by
    rw [vecMulVec_mul_vecMulVec, hq, dotProduct_mulVec, vecMulVec_smul]
  have hMG : (Matrix.vecMulVec x (star x ᵥ* G))ᴴ * G = G * Matrix.vecMulVec x (star x ᵥ* G) := by
    rw [hM, conjTranspose_mul, hN, hG, Matrix.mul_assoc]
  have hqs : star q = q := by
    rw [hq, ← star_dotProduct_star, star_star, star_mulVec, hG, dotProduct_mulVec]
  generalize Matrix.vecMulVec x (star x ᵥ* G) = M at hMM hMG ⊢
  have hr : (1 + (-2 / q) • M) * (1 + (-2 / q) • M) = 1 := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, hMM,
      smul_smul, add_assoc, ← add_smul, smul_add]
    have : -2 / q + (-2 / q + -2 / q * (-2 / q * q)) = 0 := by field_simp; ring
    rw [this, zero_smul, add_zero]
  have hrG : (1 + (-2 / q) • M)ᴴ * G = G * (1 + (-2 / q) • M) := by
    have : star (-2 / q) = -2 / q := by rw [star_div₀, hqs]; simp
    rw [conjTranspose_add, conjTranspose_one, conjTranspose_smul, this, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul,
      Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, hMG]
  obtain ⟨s, hs, hc⟩ := exists_comm hG hd hr (by rw [hrG, Matrix.mul_assoc, hr, Matrix.mul_one])
  refine ⟨s, hs, fun c => ?_⟩
  have hsM : s * M = M * s := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul,
      add_right_inj] at hc
    exact smul_right_injective _ (div_ne_zero (by norm_num) hx) hc
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, hsM]

end GlobalTheory.CartanRefl
end

open Matrix Formalism.IndefR.Datum
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cartanInvolution_comm_quasiReflection : ∀ (n : ℕ) (G : Matrix (Fin n) (Fin n) ℂ), Gᴴ = G → G.det ≠ 0 → ∀ x : Fin n → ℂ, star x ⬝ᵥ G *ᵥ x ≠ 0 → ∃ s, IsCartanInv G s ∧ ∀ c : ℂ, s * (1 + c • Matrix.vecMulVec x (star x ᵥ* G)) = (1 + c • Matrix.vecMulVec x (star x ᵥ* G)) * s := by
  atlas_forward_decl GlobalTheory.CartanRefl.exists_cartan_comm_quasiReflection
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts GlobalTheory.FinWeil GlobalTheory.FinWeilO GlobalTheory.FockCompare GlobalTheory.VacUnique GlobalTheory.RatAut
open scoped TensorProduct Kronecker ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteWeilRep_eq_latticeIntertwiner_mul_character : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (χS χT : (AE D)ˣ →* Circle) (nS nT : ℕ), IsHeckeChar D χS → IsHeckeChar D χT → ResEta D χS nS → ResEta D χT nT → ∀ of : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ), IsFinWeil ψ S T ΛS ΛT χS χT of → ∀ (lam : ℕ →* ℂ), GoodNorm (GlobalTheory.FinWeil.sgO D) lam → (∀ n : ℕ, n ≠ 0 → (∀ q : ℕ, q.Prime → Formalism.MainNotions.StandardLatticesGL3.InertQ D q → ¬ q ∣ n) → lam n = (Real.sqrt n : ℂ)) → ∀ (w : 𝓞 D.host.E) (Om : GA D S × GA D T →* Module.End ℂ (thetaSub ψ S T)), IsLatRep hψ.1 ΛS ΛT w lam Om → ∀ ε, IsHalfIdem D ε → ∀ (g : GA D S) (h : GA D T) (x y : (AE D)ˣ), (x : AE D) = ε * (Formalism.L2.Theta.mt S g).det + (1 - ε) → (y : AE D) = ε * (Formalism.L2.Theta.mt T h).det + (1 - ε) → ∀ f : thetaSub ψ S T, of (g, h) f = ((((χT x)⁻¹ * χS y : Circle) : ℂ)) • (Om (g, h) f : WO S T → ℂ) := by
  first | exact @GlobalTheory.FinWeilForm.finWeil_eq | exact GlobalTheory.FinWeilForm.finWeil_eq | (intros; apply GlobalTheory.FinWeilForm.finWeil_eq <;> assumption)
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RatSubst

theorem setLIntegral_comp_addEquiv {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (Γ : AddSubgroup G) [Countable Γ] (e : G ≃+ G) (he : Continuous e) (hes : Continuous e.symm)
    (hΓ : ∀ x, e x ∈ Γ ↔ x ∈ Γ) (μ : Measure G) [μ.IsAddHaarMeasure] {F : Set G}
    (hF : IsAddFundamentalDomain Γ F μ) (hfin : μ F ≠ ⊤) (φ : G → ENNReal)
    (hφ : ∀ γ ∈ Γ, ∀ x, φ (γ + x) = φ x) : ∫⁻ w in F, φ (e w) ∂μ = ∫⁻ w in F, φ w ∂μ := by
  let m : G ≃ᵐ G :=
    { toEquiv := e.toEquiv
      measurable_toFun := he.measurable
      measurable_invFun := hes.measurable }
  have hmp : MeasurePreserving m (μ.map e.symm) μ :=
    (MeasurePreserving.symm m.symm ⟨m.symm.measurable, rfl⟩)
  have hmp' : MeasurePreserving e (μ.map e.symm) μ := hmp
  have hν : (μ.map e.symm).IsAddHaarMeasure := AddEquiv.isAddHaarMeasure_map μ e.symm hes (by simpa using he)
  have hF' : IsAddFundamentalDomain Γ (e ⁻¹' F) (μ.map e.symm) := by
    let f : Γ → Γ := fun y => ⟨e.symm y, (hΓ _).1 (by simp)⟩
    have hf : Function.Bijective f := by
      constructor
      · intro a b hab
        exact Subtype.ext (e.symm.injective (congrArg Subtype.val hab))
      · intro x
        exact ⟨⟨e x, (hΓ _).2 x.2⟩, Subtype.ext (by simp [f])⟩
    refine hF.preimage_of_equiv hmp'.quasiMeasurePreserving hf ?_
    intro y x
    simp [f, AddSubgroup.vadd_def]
  obtain ⟨c, hc⟩ : ∃ c : NNReal, μ.map e.symm = c • μ := ⟨_, Measure.isAddLeftInvariant_eq_smul _ μ⟩
  have hac : μ.map e.symm ≪ μ := hc ▸ Measure.smul_absolutelyContinuous
  have hF'' : IsAddFundamentalDomain Γ F (μ.map e.symm) := hF.mono hac
  have h1 : (μ.map e.symm) (e ⁻¹' F) = μ F := hmp.measure_preimage_equiv F
  have h2 : (μ.map e.symm) F = μ F := (hF''.measure_eq hF').trans h1
  have h0 : μ F ≠ 0 := hF.measure_ne_zero (NeZero.ne μ)
  have hc1 : (c : ENNReal) = 1 := by
    rw [hc, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h2
    exact (ENNReal.mul_left_inj h0 hfin).1 (by rw [h2, one_mul])
  have hc2 : c = 1 := by exact_mod_cast hc1
  rw [hc2, one_smul] at hc
  have h3 : ∫⁻ w in e ⁻¹' F, φ (e w) ∂(μ.map e.symm) = ∫⁻ w in F, φ w ∂μ :=
    hmp.setLIntegral_comp_preimage_emb m.measurableEmbedding φ F
  rw [hc] at h3 hF'
  rw [← h3]
  refine hF.setLIntegral_eq hF' (fun w => φ (e w)) fun g x => ?_
  show φ (e ((g : G) + x)) = φ (e x)
  rw [map_add, hφ _ ((hΓ _).2 g.2)]

variable {D : D7} {S T : HSp D}

theorem actO_add (g : GA D S) (h : GA D T) (x y : WO S T) :
    actO S T g h (x + y) = actO S T g h x + actO S T g h y := by
  unfold actO
  rw [Matrix.mul_add, Matrix.add_mul]

theorem mt_mul (V : HSp D) (g g' : GA D V) : Formalism.L2.Theta.mt V (g * g') = Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V g' := rfl

theorem mt_one (V : HSp D) : Formalism.L2.Theta.mt V 1 = 1 := rfl

theorem actO_inv_actO (g : GA D S) (h : GA D T) (x : WO S T) : actO S T g⁻¹ h⁻¹ (actO S T g h x) = x := by
  unfold actO
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← mt_mul, inv_mul_cancel, mt_one, Matrix.one_mul, Matrix.mul_assoc,
    ← mt_mul, mul_inv_cancel, mt_one, Matrix.mul_one]

theorem symplOH_actO (g : GA D S) (h : GA D T) (x y : WO S T) :
    symplOH S T (actO S T g h x) (actO S T g h y) = symplOH S T x y := by
  unfold symplOH
  rw [GlobalTheory.SymplOInv.symplO_actO]

theorem exists_mt_eq (V : HSp D) {γ : GA D V} (h : γ ∈ GQ V) :
    ∃ m : Matrix (Fin V.rank) (Fin V.rank) D.host.E, Formalism.L2.Theta.mt V γ = m.map (incA D) := by
  obtain ⟨γ', -, e⟩ := h
  exact ⟨γ'.1, (congrArg Units.val e).symm⟩

theorem exists_actO_ratW {γ : GA D S} (hγ : γ ∈ GQ S) {γ' : GA D T} (hγ' : γ' ∈ GQ T)
    (x : Matrix (Fin T.rank) (Fin S.rank) D.host.E) : ∃ y, actO S T γ γ' (ratW T S x) = ratW T S y := by
  obtain ⟨m, hm⟩ := exists_mt_eq S ((GQ S).inv_mem hγ)
  obtain ⟨m', hm'⟩ := exists_mt_eq T hγ'
  refine ⟨m' * x * m, ?_⟩
  unfold actO ratW
  rw [hm, hm', Matrix.map_mul, Matrix.map_mul]

theorem actO_mem_ratL {γ : GA D S} (hγ : γ ∈ GQ S) {γ' : GA D T} (hγ' : γ' ∈ GQ T) {x : WO S T}
    (hx : x ∈ ratL T S) : actO S T γ γ' x ∈ ratL T S := by
  obtain ⟨y, rfl⟩ := hx
  obtain ⟨z, hz⟩ := exists_actO_ratW hγ hγ' y
  exact ⟨z, hz.symm⟩

theorem isThetaFunO_comp {ψ : AddChar (AF D.host.F) ℂ} {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    {γ : GA D S} (hγ : γ ∈ GQ S) {γ' : GA D T} (hγ' : γ' ∈ GQ T) :
    IsThetaFunO ψ S T fun w => f (actO S T γ γ' w) := by
  let A : WO S T →+ WO S T := AddMonoidHom.mk' (actO S T γ γ') (actO_add γ γ')
  have hA : Continuous (actO S T γ γ') := GlobalTheory.LatLevel.continuous_actO S T γ γ'
  refine ⟨fun x w => ?_, ?_, hf.cont.comp hA, fun k L h1 h2 w => ?_⟩
  · obtain ⟨y, e⟩ := exists_actO_ratW hγ hγ' x
    rw [actO_add, ← symplOH_actO γ γ', e, hf.quasi]
  · obtain ⟨U, hU, h⟩ := hf.level
    refine ⟨U.comap A, hU.preimage hA, fun u hu h0 => ?_⟩
    funext w
    have e := congrFun (h _ hu (GlobalTheory.LatLevel.actO_map_inf S T γ γ' h0)) (actO S T γ γ' w)
    unfold heisO at e ⊢
    rw [← e, ← symplOH_actO γ γ' w u]
    exact congrArg (fun x => _ * f x) (actO_add γ γ' w u)
  · have h3 : ∀ t, (actO S T γ γ' (L t)).map (finPart D) = 0 := fun t => by
      unfold actO
      rw [Matrix.map_mul, Matrix.map_mul, h2, Matrix.mul_zero, Matrix.zero_mul]
    have := hf.smooth k (A.comp L) (hA.comp h1) h3 (actO S T γ γ' w)
    simp only [actO_add]
    exact this

theorem rational_substitution : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D), ∀ γ ∈ GQ S, ∀ γ' ∈ GQ T, ∀ f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (fun w => f (actO S T γ⁻¹ γ'⁻¹ w)) ∧ (∀ w₀, (fun w => heisO ψ S T w₀ f (actO S T γ⁻¹ γ'⁻¹ w)) = heisO ψ S T (actO S T γ γ' w₀) (fun w => f (actO S T γ⁻¹ γ'⁻¹ w))) ∧ ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ → ∫⁻ w in 𝓕, ‖f (actO S T γ⁻¹ γ'⁻¹ w)‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ := by
  intro D ψ hψ S T γ hγ γ' hγ' f hf
  have hi := (GQ S).inv_mem hγ
  have hi' := (GQ T).inv_mem hγ'
  refine ⟨isThetaFunO_comp hf hi hi', fun w₀ => ?_, fun μ 𝓕 hμ h𝓕 => ?_⟩
  · funext w
    unfold heisO
    beta_reduce
    rw [actO_add, actO_inv_actO, ← symplOH_actO γ⁻¹ γ'⁻¹ w, actO_inv_actO]
  · obtain ⟨h1, h2, h3, h4, h5, K, hK, hcov⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
    have : BorelSpace (WO S T) := ⟨rfl⟩
    have : Countable (ratL T S) := countable_of_discrete_addSubgroup _
    have hinv : ∀ x, actO S T γ γ' (actO S T γ⁻¹ γ'⁻¹ x) = x := fun x => by
      have := actO_inv_actO γ⁻¹ γ'⁻¹ x
      rwa [inv_inv, inv_inv] at this
    let e : WO S T ≃+ WO S T :=
      { toFun := actO S T γ⁻¹ γ'⁻¹
        invFun := actO S T γ γ'
        left_inv := hinv
        right_inv := actO_inv_actO γ γ'
        map_add' := actO_add _ _ }
    refine setLIntegral_comp_addEquiv (G := WO S T) (ratL T S) e (GlobalTheory.LatLevel.continuous_actO S T _ _)
      (GlobalTheory.LatLevel.continuous_actO S T _ _) (fun x => ⟨fun hx => ?_, actO_mem_ratL hi hi'⟩) μ h𝓕
      (measure_addFundamentalDomain_lt_top_of_cocompact (G := WO S T) (ratL T S) hK hcov μ h𝓕).ne
      (fun w => ‖f w‖ₑ ^ 2) ?_
    · rw [← hinv x]
      exact actO_mem_ratL hγ hγ' hx
    · rintro _ ⟨y, rfl⟩ x
      have h6 : f (ratW T S y + x) = _ := hf.quasi y x
      have h7 : ‖f (ratW T S y + x)‖ = ‖f x‖ := by
        rw [h6, norm_mul, hψ.1.2.1, one_mul]
      show ‖f (ratW T S y + x)‖ₑ ^ 2 = ‖f x‖ₑ ^ 2
      rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, h7]

end GlobalTheory.RatSubst

end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_substitution_theta_heisenberg_unitary : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D), ∀ γ ∈ GQ S, ∀ γ' ∈ GQ T, ∀ f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (fun w => f (actO S T γ⁻¹ γ'⁻¹ w)) ∧ (∀ w₀, (fun w => heisO ψ S T w₀ f (actO S T γ⁻¹ γ'⁻¹ w)) = heisO ψ S T (actO S T γ γ' w₀) (fun w => f (actO S T γ⁻¹ γ'⁻¹ w))) ∧ ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ → ∫⁻ w in 𝓕, ‖f (actO S T γ⁻¹ γ'⁻¹ w)‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ := by
  first | exact @GlobalTheory.RatSubst.rational_substitution | exact GlobalTheory.RatSubst.rational_substitution | (intros; apply GlobalTheory.RatSubst.rational_substitution <;> assumption)
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct Kronecker ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RatAut

open GlobalTheory.WeilParts GlobalTheory.FinWeil GlobalTheory.FinWeilO GlobalTheory.FockCompare GlobalTheory.VacUnique GlobalTheory.SplitScalar

section Abstract

theorem gauss_isometry {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M]
    {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M} (h : IsHeis σ w γ W) {lam : ℕ →* ℂ} (hlam : GoodNorm σ lam)
    {A : Submodule R X} (hA : SelfDual γ A) (u : X →ₗ[R] X) (hu : ∀ x y, γ (u x) (u y) = γ x y)
    (hs : ∀ a, ∃ y, u y - y = a) (n : ℕ) (t : Fin n → X) (ht : ∀ k, u (t k) - t k ∈ A)
    (ht' : ∀ y, u y - y ∈ A → ∃! k, y - t k ∈ A) :
    ∑ k, γ (σ w • (u (t k) - t k)) (t k) = lam n ∧ lam n ^ 2 = n := by
  let β : X → X → ℂ := fun y x => γ (σ w • (u y - y)) x * γ (w • (u y - y)) (u x)
  have hsub : ∀ x y z, γ (x - y) z = γ x z * (γ y z)⁻¹ := fun x y z => by
    rw [sub_eq_add_neg, h.add_left, h.neg_left]
  have hβ : ∀ y x, β y x = γ (σ w • u y) x * (γ (σ w • y) x)⁻¹ * (γ (w • y) x * (γ (w • y) (u x))⁻¹) := fun y x => by
    simp only [β, smul_sub, hsub]
    rw [← map_smul u w y, hu]
  have e1 : ∀ x y, γ (σ w • x) y = (γ (w • y) x)⁻¹ := fun x y => by rw [h.adj, h.sg_sg, h.swap]
  have hsym : ∀ x y, β x y = β y x := fun x y => by
    rw [hβ, hβ, e1, e1, e1, e1]
    simp only [inv_inv]
    ring
  have hβ' : ∀ y x, β y x = γ (u y - y) (w • x + σ w • u x) := fun y x => by
    simp only [β]
    rw [h.add_right, h.adj, h.adj, h.sg_sg]
  have hm : ∀ x, x ∈ A.comap (u - LinearMap.id) ↔ u x - x ∈ A := fun x => Iff.rfl
  have key := GlobalTheory.T.gaussSum_nondegenerate_finite_hermitian_module σ w h.sg_sg h.w_add lam hlam β
    (fun x y z => by
      rw [hβ', hβ', hβ', ← h.add_left, map_add]
      congr 1
      abel)
    hsym
    (fun r x y => by
      rw [hβ', hβ', map_smul, ← smul_sub, h.adj, map_smul, smul_add, smul_comm (σ r) w, smul_comm (σ r) (σ w)])
    (A.comap (u - LinearMap.id)) (A.comap (u - LinearMap.id) ⊓ A) inf_le_left
    (fun x hx => by
      rw [hm] at hx
      have hz : w • x + σ w • u x = x + σ w • (u x - x) := by
        have e : w • x + σ w • x = x := by rw [← add_smul, h.w_add, one_smul]
        rw [smul_sub, ← sub_eq_zero]
        rw [← sub_eq_zero] at e
        rw [← e]
        abel
      constructor
      · rintro ⟨-, hxA⟩ y hy
        rw [hsym, hβ', hz]
        exact h.iso hA hy (A.add_mem hxA (A.smul_mem _ hx))
      · intro hy
        refine ⟨hx, ?_⟩
        have : x + σ w • (u x - x) ∈ A := (hA _).2 fun a ha => by
          obtain ⟨y, rfl⟩ := hs a
          have := hy y ha
          rw [hsym, hβ', hz] at this
          exact h.swap_eq_one this
        exact (A.add_mem_iff_left (A.smul_mem _ hx)).1 this)
    n t (fun k => (hm _).2 (ht k)) (fun y hy => by
      obtain ⟨k, hk, hk'⟩ := ht' y hy
      exact ⟨k, ⟨Submodule.sub_mem _ hy ((hm _).2 (ht k)), hk⟩, fun k' h' => hk' k' h'.2⟩)
  refine ⟨Eq.trans (Finset.sum_congr rfl fun k _ => ?_) key.1, key.2⟩
  have e4 : ∀ (r : R) y, γ (r • (u y - y)) (u y) = γ (σ r • (u y - y)) y := fun r y => by
    rw [smul_sub, smul_sub, hsub, hsub, ← map_smul u r y, hu, h.adj (σ r), h.adj (σ r), h.sg_sg, h.swap (r • y) (u y),
      h.swap (r • y) y, inv_inv, mul_comm]
  simp only [β]
  rw [map_smul, ← smul_sub, smul_smul, smul_smul, e4, ← h.add_left, ← add_smul, map_mul, ← mul_add, h.w_add, mul_one]

theorem exists_transversal {X : Type} [AddCommGroup X] (A B : AddSubgroup X) (h : A.relIndex B ≠ 0) :
    ∃ t : Fin (A.relIndex B) → X, (∀ k, t k ∈ B) ∧ ∀ y ∈ B, ∃! k, y - t k ∈ A := by
  have : Finite (B ⧸ A.addSubgroupOf B) := AddSubgroup.index_ne_zero_iff_finite.1 h
  let e : (B ⧸ A.addSubgroupOf B) ≃ Fin (A.relIndex B) := Finite.equivFinOfCardEq rfl
  refine ⟨fun k => ((e.symm k).out : B), fun k => (e.symm k).out.2, fun y hy => ?_⟩
  have key : ∀ k, y - ((e.symm k).out : B) ∈ A ↔ k = e (QuotientAddGroup.mk ⟨y, hy⟩) := fun k => by
    rw [← Equiv.symm_apply_eq, eq_comm, ← QuotientAddGroup.out_eq' (e.symm k), QuotientAddGroup.eq_iff_sub_mem,
      QuotientAddGroup.out_eq']
    rfl
  exact ⟨_, (key _).2 rfl, fun k hk => (key k).1 hk⟩

theorem finite_det_smul_sub_one {K ι : Type} [Field K] [Fintype ι] [DecidableEq ι] (M : Matrix ι ι K) :
    {t : K | (t • M - 1).det = 0}.Finite := by
  have h0 : M.charpolyRev ≠ 0 := fun h => by
    have := Matrix.eval_charpolyRev (M := M)
    rw [h, Polynomial.eval_zero] at this
    exact zero_ne_one this
  refine (Polynomial.finite_setOfPred_isRoot h0).subset fun t ht => ?_
  have e : M.charpolyRev.eval t = (1 - t • M).det := by
    rw [Matrix.charpolyRev, ← Polynomial.coe_evalRingHom, RingHom.map_det]
    rw [map_sub, map_one]
    congr 2
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Polynomial.eval_mul,
      Polynomial.coe_evalRingHom, Polynomial.eval_X, Polynomial.eval_C]
  show M.charpolyRev.eval t = 0
  rw [e, ← neg_sub, Matrix.det_neg, show (t • M - 1).det = 0 from ht, mul_zero]

theorem det_unitary_sub_one {K ι : Type} [Field K] [StarRing K] [Fintype ι] [DecidableEq ι] {M P : Matrix ι ι K}
    (hP : P.det ≠ 0) (h : Mᴴ * P * M = P) :
    M.det * star M.det = 1 ∧ M.det * star (M - 1).det = (-1) ^ Fintype.card ι * (M - 1).det := by
  constructor
  · have := congrArg Matrix.det h
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose] at this
    refine mul_right_cancel₀ hP ?_
    linear_combination this
  · have e : (M - 1)ᴴ * P * M = P * -(M - 1) := by
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.sub_mul, Matrix.sub_mul, h, Matrix.one_mul,
        neg_sub, Matrix.mul_sub, Matrix.mul_one]
    have := congrArg Matrix.det e
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_neg] at this
    refine mul_right_cancel₀ hP ?_
    linear_combination this

theorem kronecker_unitary {K : Type} [Field K] [StarRing K] {m n : ℕ} {a G : Matrix (Fin n) (Fin n) K}
    {b H : Matrix (Fin m) (Fin m) K} (hG : IsUnit G.det) (ha : aᴴ * G * a = G) (hb : bᴴ * H * b = H) :
    (b ⊗ₖ aᵀ)ᴴ * (H ⊗ₖ G⁻¹ᵀ) * (b ⊗ₖ aᵀ) = H ⊗ₖ G⁻¹ᵀ := by
  have h1 : (G⁻¹ * aᴴ * G) * a = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc aᴴ, ha, Matrix.nonsing_inv_mul _ hG]
  have h2 : a * G⁻¹ * aᴴ = G⁻¹ := by
    have h3 := mul_eq_one_comm.1 h1
    calc a * G⁻¹ * aᴴ = a * (G⁻¹ * aᴴ * G) * G⁻¹ := by
          simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hG, Matrix.mul_one]
      _ = G⁻¹ := by rw [h3, Matrix.one_mul]
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, hb]
  congr 1
  conv_rhs => rw [← h2]
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.mul_assoc]
  rfl

end Abstract

variable {D : D7}

def IsRat (V : HSp D) (g : GA D V) (a : Matrix (Fin V.rank) (Fin V.rank) D.host.E) : Prop :=
  Formalism.L2.Theta.mt V g = a.map (incA D)

theorem incA_inj : Function.Injective (incA D) := by
  obtain ⟨θ, hθ⟩ := GlobalTheory.Member.exists_isInfFam_family D
  intro x y h
  refine (tauE D (D.eTau.symm 1)).injective ?_
  rw [← comp_incA hθ, ← comp_incA hθ, h]

theorem exists_isRat {V : HSp D} {g : GA D V} (hg : g ∈ GQ V) : ∃ a, IsRat V g a := by
  obtain ⟨a, -, ha⟩ := hg
  exact ⟨a.1, (congrArg Units.val ha).symm⟩

theorem mt_unitary (V : HSp D) (g : GA D V) :
    ((Formalism.L2.Theta.mt V g).map (cA D))ᵀ * V.gram.map (incA D) * Formalism.L2.Theta.mt V g = V.gram.map (incA D) := g.2

theorem IsRat.unitary {V : HSp D} {g : GA D V} {a} (h : IsRat V g a) : aᴴ * V.gram * a = V.gram := by
  have e := mt_unitary V g
  rw [show Formalism.L2.Theta.mt V g = _ from h] at e
  refine Matrix.map_injective (incA_inj (D := D)) ?_
  show (aᴴ * V.gram * a).map (incA D) = V.gram.map (incA D)
  rw [Matrix.map_mul, Matrix.map_mul]
  exact e

theorem exists_of_unitary (V : HSp D) {a : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (h : aᴴ * V.gram * a = V.gram) :
    ∃ g ∈ GQ V, IsRat V g a := by
  have hd := (det_unitary_sub_one (GlobalTheory.LatVac.gram_det_isUnit V).ne_zero h).1
  let a' : GL (Fin V.rank) D.host.E := Matrix.GeneralLinearGroup.mkOfDetNeZero a (left_ne_zero_of_mul_eq_one hd)
  refine ⟨⟨Formalism.UG.bc (incA D) a', ?_⟩, ⟨a', h, rfl⟩, rfl⟩
  show ((a.map (incA D)).map (cA D))ᵀ * V.gram.map (incA D) * a.map (incA D) = V.gram.map (incA D)
  conv_rhs => rw [← h, Matrix.map_mul, Matrix.map_mul]
  rfl

theorem IsRat.mul {V : HSp D} {g g' : GA D V} {a a'} (h : IsRat V g a) (h' : IsRat V g' a') : IsRat V (g * g') (a * a') := by
  rw [IsRat, mt_mul, show Formalism.L2.Theta.mt V g = _ from h, show Formalism.L2.Theta.mt V g' = _ from h', Matrix.map_mul]

theorem isRat_one (V : HSp D) : IsRat V 1 1 := by
  rw [IsRat, mt_one, Matrix.map_one _ (incA D).map_zero (incA D).map_one]

theorem IsRat.ext {V : HSp D} {g g' : GA D V} {a} (h : IsRat V g a) (h' : IsRat V g' a) : g = g' :=
  Subtype.ext (Units.ext (h.trans h'.symm))

theorem IsRat.mem {V : HSp D} {g : GA D V} {a} (h : IsRat V g a) : g ∈ GQ V := by
  obtain ⟨g', h1, h2⟩ := exists_of_unitary V h.unitary
  rwa [h.ext h2]

theorem IsRat.compAt {V : HSp D} {g : GA D V} {a} (h : IsRat V g a) {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) :
    compAt θ τ (Formalism.L2.Theta.mt V g) = a.map (tauE D τ) := by
  rw [show Formalism.L2.Theta.mt V g = _ from h]
  funext i j
  exact comp_incA hθ τ _

theorem compAt_mul (θ : InfFam D) (τ : D.what₂.Tau) (V : HSp D) (g g' : GA D V) :
    compAt θ τ (Formalism.L2.Theta.mt V (g * g')) = compAt θ τ (Formalism.L2.Theta.mt V g) * compAt θ τ (Formalism.L2.Theta.mt V g') :=
  Matrix.map_mul (f := (θ τ).comp (infPart D))

theorem compAt_fin (θ : InfFam D) (τ : D.what₂.Tau) {V : HSp D} {k : GA D V} (hk : k ∈ GfC V) :
    compAt θ τ (Formalism.L2.Theta.mt V k) = 1 := by
  have h : (Formalism.L2.Theta.mt V k).map (infPart D) = 1 := congrArg Units.val (MonoidHom.mem_ker.1 hk)
  have : compAt θ τ (Formalism.L2.Theta.mt V k) = ((Formalism.L2.Theta.mt V k).map (infPart D)).map (θ τ) := rfl
  rw [this, h, Matrix.map_one _ (θ τ).map_zero (θ τ).map_one]

theorem map_tau_unitary {V : HSp D} {a : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (h : aᴴ * V.gram * a = V.gram)
    (τ : D.what₂.Tau) : (a.map (tauE D τ))ᴴ * gramAt D V τ * a.map (tauE D τ) = gramAt D V τ := by
  have e : (aᴴ).map (tauE D τ) = (a.map (tauE D τ))ᴴ := by
    funext i j
    exact tauE_star τ _
  have := congrArg (fun m : Matrix (Fin V.rank) (Fin V.rank) D.host.E => m.map (tauE D τ)) h
  simp only [Matrix.map_mul, e] at this
  exact this

theorem infinite_norm_one (D : D7) : {t : D.host.E | t * star t = 1}.Infinite := by
  have h0 : D.host.xi0 ≠ 0 := GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero
  have hs := GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg D
  have hne : ∀ n : ℕ, (n : D.host.E) - D.host.xi0 ≠ 0 := fun n h => by
    have e := congrArg star h
    rw [star_sub, star_natCast, hs, star_zero] at e
    apply h0
    linear_combination (e - h) / 2
  have hne' : ∀ n : ℕ, (n : D.host.E) + D.host.xi0 ≠ 0 := fun n h => by
    have e := congrArg star h
    rw [star_add, star_natCast, hs, star_zero] at e
    exact hne n (by rw [← e]; ring)
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ => ((n : D.host.E) + D.host.xi0) / (n - D.host.xi0))
    (fun n m h => ?_) fun n => ?_
  · have := (div_eq_div_iff (hne n) (hne m)).1 h
    have e : D.host.xi0 * ((n : D.host.E) - m) = 0 := by linear_combination (-1 / 2) * this
    exact_mod_cast sub_eq_zero.1 ((mul_eq_zero.1 e).resolve_left h0)
  · show _ * star _ = 1
    rw [star_div₀, star_add, star_sub, star_natCast, hs, sub_neg_eq_add, ← sub_eq_add_neg]
    have := hne n
    have := hne' n
    field_simp

theorem rat_induction (V : HSp D) (P : GA D V → Prop) (h1 : P 1) (hm : ∀ g ∈ GQ V, ∀ g' ∈ GQ V, P g → P g' → P (g * g'))
    (hr : ∀ g (x : Fin V.rank → D.host.E) (c : D.host.E), star x ⬝ᵥ V.gram *ᵥ x ≠ 0 →
      IsRat V g (1 + c • Matrix.vecMulVec x (star x ᵥ* V.gram)) → P g) : ∀ g ∈ GQ V, P g := by
  intro g hg
  obtain ⟨a, ha⟩ := exists_isRat hg
  have hc : ∀ x : D.host.E, D.host.conj x = star x := fun x => (GlobalTheory.SplitIdem.star_eq_conj D x).symm
  have hh : ∀ x y, GlobalTheory.UnRep.hermE D.host.conj V.gramᵀ x y = star y ⬝ᵥ V.gram *ᵥ x := fun x y => by
    simp only [GlobalTheory.UnRep.hermE, hc, dotProduct, Matrix.mulVec, Matrix.transpose_apply, Finset.mul_sum, Pi.star_apply]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hun : ∀ m, GlobalTheory.UnRep.IsUnE D.host.conj V.gramᵀ m ↔ mᴴ * V.gram * m = V.gram := fun m => by
    have e : ∀ x y, star (m *ᵥ y) ⬝ᵥ V.gram *ᵥ m *ᵥ x = star y ⬝ᵥ (mᴴ * V.gram * m) *ᵥ x := fun x y => by
      rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    simp only [GlobalTheory.UnRep.IsUnE, hh, e]
    refine ⟨fun h => ?_, fun h x y => by rw [h]⟩
    ext i j
    simpa using h (Pi.single j 1) (Pi.single i 1)
  have hG : GlobalTheory.UnRep.IsHermForm D.host.conj V.gramᵀ := by
    refine ⟨fun x => by rw [hc, hc, star_star], fun h => ?_, fun i j => by rw [hc]; exact GlobalTheory.LatVac.gram_star V _ _,
      by rw [Matrix.det_transpose]; exact (GlobalTheory.LatVac.gram_det_isUnit V).ne_zero⟩
    have e := GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg D
    rw [← hc, h, AlgEquiv.one_apply] at e
    exact GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero (D := D) (by linear_combination e / 2)
  obtain ⟨l, hl, rfl⟩ := GlobalTheory.UnRep.isUnE_eq_prod_refl ℚ _ D.host.conj _ _ hG a ((hun a).2 ha.unitary)
  clear hg
  induction l generalizing g with
  | nil => exact ha.ext (isRat_one V) ▸ h1
  | cons p l ih =>
    obtain ⟨p1, p2⟩ := hl p List.mem_cons_self
    obtain ⟨g₁, m1, r1⟩ := exists_of_unitary V
      ((hun _).1 ((GlobalTheory.UnRep.ReflLaws.refl_laws ℚ _ D.host.conj _ _ hG p.1 p1).2.2.2 p.2 p2))
    obtain ⟨g₂, m2, r2⟩ := exists_of_unitary V
      ((hun _).1 (GlobalTheory.UnRep.ReflGen.isUnE_prod hG l fun q hq => hl q (List.mem_cons_of_mem _ hq)))
    rw [List.map_cons, List.prod_cons] at ha
    rw [ha.ext (r1.mul r2)]
    refine hm _ m1 _ m2 (hr g₁ p.1 ((p.2 - 1) / GlobalTheory.UnRep.hermE D.host.conj V.gramᵀ p.1 p.1) (hh _ _ ▸ p1) ?_)
      (ih g₂ (fun q hq => hl q (List.mem_cons_of_mem _ hq)) r2)
    rw [← Matrix.mulVec_transpose]
    have e : (fun b => D.host.conj (p.1 b)) = star p.1 := funext fun b => hc _
    rw [← e]
    exact r1

section Operators

variable {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
  {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
  {χS χT : (AE D)ˣ →* Circle} {of oi : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}

theorem act_mul (g g' : GA D S) (h h' : GA D T) (u : WO S T) :
    actO S T (g * g') (h * h') u = actO S T g h (actO S T g' h' u) := by
  simp only [actO, _root_.mul_inv_rev, mt_mul, Matrix.mul_assoc]

theorem act_one (u : WO S T) : actO S T 1 1 u = u := by
  rw [actO, inv_one, mt_one, mt_one, Matrix.one_mul, Matrix.mul_one]

def subst (p : GA D S × GA D T) : Module.End ℂ (WO S T → ℂ) := LinearMap.funLeft ℂ ℂ (actO S T p.1⁻¹ p.2⁻¹)

theorem subst_apply (p : GA D S × GA D T) (f : WO S T → ℂ) : subst p f = fun w => f (actO S T p.1⁻¹ p.2⁻¹ w) := rfl

theorem subst_mul (p q : GA D S × GA D T) (f : WO S T → ℂ) : subst (p * q) f = subst p (subst q f) := by
  funext w
  show f (actO S T (p.1 * q.1)⁻¹ (p.2 * q.2)⁻¹ w) = f (actO S T q.1⁻¹ q.2⁻¹ (actO S T p.1⁻¹ p.2⁻¹ w))
  rw [_root_.mul_inv_rev, _root_.mul_inv_rev, act_mul]

theorem subst_one (f : WO S T → ℂ) : subst (1 : GA D S × GA D T) f = f := by
  funext w
  show f (actO S T 1⁻¹ 1⁻¹ w) = f w
  rw [inv_one, inv_one, act_one]

theorem exists_parts (p : GA D S × GA D T) : ∃ a k : GA D S × GA D T, a.1 ∈ GinfC S ∧ a.2 ∈ GinfC T ∧ k.1 ∈ GfC S ∧
    k.2 ∈ GfC T ∧ p = a * k ∧ p = k * a := by
  obtain ⟨s1, s2, -⟩ := GlobalTheory.UnitarySplit.real_finite_split D S
  obtain ⟨t1, t2, -⟩ := GlobalTheory.UnitarySplit.real_finite_split D T
  obtain ⟨a, ha, k, hk, e⟩ := s1 p.1
  obtain ⟨a', ha', k', hk', e'⟩ := t1 p.2
  exact ⟨(a, a'), (k, k'), ha, ha', hk, hk', Prod.ext e e',
    Prod.ext (e.trans (s2 a ha k hk)) (e'.trans (t2 a' ha' k' hk'))⟩

def IsScalar (ψ : AddChar (AF D.host.F) ℂ) (of oi : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (p : GA D S × GA D T)
    (c : ℂ) : Prop :=
  ∀ f, IsThetaFunO ψ S T f → of p (oi p f) = c • subst p f

theorem exists_isScalar (hψ : IsStdChar D ψ (-1)) (hf : IsFinWeil ψ S T ΛS ΛT χS χT of) (hi : IsInfWeil ψ θ S T oi)
    {p : GA D S × GA D T} (h1 : p.1 ∈ GQ S) (h2 : p.2 ∈ GQ T) : ∃ c : ℂ, ‖c‖ = 1 ∧ IsScalar ψ of oi p c := by
  have R := GlobalTheory.T.rational_substitution_theta_heisenberg_unitary D ψ hψ S T _ (inv_mem h1) _ (inv_mem h2)
  have R' := GlobalTheory.T.rational_substitution_theta_heisenberg_unitary D ψ hψ S T _ h1 _ h2
  obtain ⟨a, k, a1, a2, k1, k2, e1, e2⟩ := exists_parts p
  have hoi : ∀ f, IsThetaFunO ψ S T f → oi p f = oi a f := fun f h => by
    rw [e1, map_mul, Module.End.mul_apply, hi.triv k.1 k1 k.2 k2 f h]
  have hof : ∀ f, IsThetaFunO ψ S T f → of p f = of k f := fun f h => by
    rw [e2, map_mul, Module.End.mul_apply, hf.triv a.1 a1 a.2 a2 f h]
  have hth : ∀ u f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (heisO ψ S T u f) :=
    fun u f h => by
      have e : u = realIdem D • u + (1 - realIdem D) • u := by rw [← add_smul, add_sub_cancel, one_smul]
      rw [e, heisO_add_of_orth ψ S T (symplO_real_fin S T (real_smul_real u) (fin_smul_fin u))]
      exact GlobalTheory.WeilVacMove.isTheta_heisO_real hψ (real_smul_real u)
        (GlobalTheory.FinTranslate.isTheta_heisO_fin hψ.1 (fin_smul_fin u) h)
  obtain ⟨c, hc, h⟩ := GlobalTheory.T.schurLemma_thetaFunctions_orientedPair D ψ hψ S T (of p * oi p * subst p⁻¹)
    (fun f h => hf.pres _ _ (hi.pres _ _ (R f h).1))
    (fun w f h => by
      have t1 : IsThetaFunO ψ S T (subst p⁻¹ f) := (R f h).1
      have t2 : subst p⁻¹ (heisO ψ S T w f) = heisO ψ S T (actO S T p.1⁻¹ p.2⁻¹ w) (subst p⁻¹ f) := (R f h).2.1 w
      simp only [Module.End.mul_apply]
      rw [t2, hoi _ (hth _ _ t1), hi.Heisenberg₂ a.1 a1 a.2 a2 _ _ t1, hof _ (hth _ _ (hi.pres _ _ t1)),
        hf.Heisenberg₂ k.1 k1 k.2 k2 _ _ (hi.pres _ _ t1), ← act_mul, ← act_mul, ← hof _ (hi.pres _ _ t1), ← hoi _ t1,
        show k.1 * a.1 = p.1 from congrArg Prod.fst e2.symm, show k.2 * a.2 = p.2 from congrArg Prod.snd e2.symm,
        mul_inv_cancel, mul_inv_cancel, act_one])
    (fun μ 𝓕 hμ h𝓕 f h => by
      have t1 : IsThetaFunO ψ S T (subst p⁻¹ f) := (R f h).1
      simp only [Module.End.mul_apply]
      rw [hf.unit μ 𝓕 hμ h𝓕 _ _ (hi.pres _ _ t1), hi.unit μ 𝓕 hμ h𝓕 _ _ t1]
      exact (R f h).2.2 μ 𝓕 hμ h𝓕)
  refine ⟨c, hc, fun f hf' => ?_⟩
  have := h (subst p f) (R' f hf').1
  simp only [Module.End.mul_apply] at this
  rwa [← subst_mul, inv_mul_cancel, subst_one] at this

theorem IsScalar.unique (hψ : IsStdChar D ψ (-1)) {p : GA D S × GA D T} {c c' : ℂ} (h : IsScalar ψ of oi p c)
    (h' : IsScalar ψ of oi p c') : c = c' := by
  obtain ⟨f, hf, f0⟩ := GlobalTheory.Mem.ThetaNonzero.exists_thetaO_ne_zero hψ S T
  refine smul_left_injective ℂ (m := subst p f) (fun e => f0 ?_) ((h f hf).symm.trans (h' f hf))
  rw [← subst_one (S := S) (T := T) f, ← inv_mul_cancel p, subst_mul, e, map_zero]

theorem IsScalar.mul (hψ : IsStdChar D ψ (-1)) (hi : IsInfWeil ψ θ S T oi)
    (hcomm : ∀ p q f, IsThetaFunO ψ S T f → of p (oi q f) = oi q (of p f)) {p q : GA D S × GA D T} {c c' : ℂ}
    (h : IsScalar ψ of oi p c) (h' : IsScalar ψ of oi q c') (h1 : q.1 ∈ GQ S) (h2 : q.2 ∈ GQ T) :
    IsScalar ψ of oi (p * q) (c * c') := fun f hf => by
  have t : IsThetaFunO ψ S T (subst q f) := (GlobalTheory.T.rational_substitution_theta_heisenberg_unitary D ψ hψ S T _ h1 _ h2 f hf).1
  rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hcomm q p _ (hi.pres _ _ hf), h' f hf, map_smul,
    map_smul, h _ t, smul_smul, mul_comm c', subst_mul]

theorem oi_comm (hψ : IsStdChar D ψ (-1)) (hi : IsInfWeil ψ θ S T oi) {w : 𝓞 D.host.E} {lam : ℕ →* ℂ}
    {Om : GA D S × GA D T →* Module.End ℂ (thetaSub ψ S T)} (h : IsLatRep hψ.1 ΛS ΛT w lam Om)
    (hof : ∀ p, ∃ z : ℂ, ∀ f : thetaSub ψ S T, of p f = z • (Om p f : WO S T → ℂ)) (p q : GA D S × GA D T)
    (f : WO S T → ℂ) (hf : IsThetaFunO ψ S T f) : of p (oi q f) = oi q (of p f) := by
  obtain ⟨z, hz⟩ := hof p
  obtain ⟨a, k, a1, a2, k1, k2, e1, -⟩ := exists_parts q
  have hoi : ∀ f, IsThetaFunO ψ S T f → oi q f = oi a f := fun f h => by
    rw [e1, map_mul, Module.End.mul_apply, hi.triv k.1 k1 k.2 k2 f h]
  let L : thetaSub ψ S T →ₗ[ℂ] thetaSub ψ S T := (oi q).restrict fun f hf => hi.pres q f hf
  have hL : ∀ m, (L m : WO S T → ℂ) = oi q m := fun _ => rfl
  have := congrArg Subtype.val (h.comm L (fun x v => Subtype.ext (by
    have e : actO S T a.1 a.2 x = x := congrArg XF.val (rhoF_real a1 a2 x)
    rw [hL, coe_opF, coe_opF, hL, map_smul, hoi _ (GlobalTheory.FinTranslate.isTheta_heisO_fin hψ.1 x.fin v.2),
      hi.Heisenberg₂ a.1 a1 a.2 a2 _ _ v.2, e, ← hoi _ v.2])) p ⟨f, hf⟩)
  rw [hz ⟨f, hf⟩, map_smul, ← hL, ← this]
  exact hz (L ⟨f, hf⟩)

end Operators

section Finite

variable {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ}
  {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}

def finL (S T : HSp D) : Matrix (Fin T.rank) (Fin S.rank) D.host.E →ₗ[𝓞 D.host.E] XF S T where
  toFun x := XF.mk (finRat S T x) (finRat_inf S T x)
  map_add' x y := XF.ext (map_add (finRat S T) x y)
  map_smul' r x := XF.ext (finRat_smul S T (r : D.host.E) x)

theorem isHeis_gamQ (hψ : IsCharAF D.host.F ψ) (S T : HSp D) {w : 𝓞 D.host.E} (hw : w + sgO D w = 1) :
    IsHeis (sgO D) w (gamQ ψ S T) fun x => opF hψ S T w (finL S T x) := by
  have H := isHeis_opF hψ S T hw
  have e : ∀ x y, gamQ ψ S T x y = gamF ψ S T (finL S T x) (finL S T y) := fun _ _ => rfl
  exact ⟨H.sg_sg, H.w_add, fun x y z => by rw [e, e, e, map_add, H.add_left],
    fun x y z => by rw [e, e, e, map_add, H.add_right], fun x => by rw [e, H.alt],
    fun r x y => by rw [e, e, map_smul, map_smul, H.adj], fun v => by rw [map_zero, H.zero],
    fun x y v => by rw [H.comp, e, map_smul, map_add]⟩

theorem finRat_sandw {g : GA D S} {h : GA D T} {a b} (ha : IsRat S g a) (hb : IsRat T h⁻¹ b)
    (x : Matrix (Fin T.rank) (Fin S.rank) D.host.E) : finRat S T (b * x * a) = actO S T g⁻¹ h⁻¹ (finRat S T x) := by
  rw [finRat_eq, finRat_eq, actO_smul, actO, inv_inv, show Formalism.L2.Theta.mt S g = _ from ha,
    show Formalism.L2.Theta.mt T h⁻¹ = _ from hb, ratW, ratW, Matrix.map_mul, Matrix.map_mul]

theorem finite_data (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) {lam : ℕ →* ℂ}
    (hlam : GoodNorm (sgO D) lam) {w : 𝓞 D.host.E} (hw : w + sgO D w = 1) {g : GA D S} {h : GA D T} {a b}
    (ha : IsRat S g a) (hb : IsRat T h⁻¹ b) (hΔ : (b ⊗ₖ aᵀ).det ≠ 0) (hd : (b ⊗ₖ aᵀ - 1).det ≠ 0) :
    Function.Bijective (fun x : Matrix (Fin T.rank) (Fin S.rank) D.host.E => b * x * a - x) ∧
    ∃ (n : ℕ) (t : Fin n → Matrix (Fin T.rank) (Fin S.rank) D.host.E) (c N M : ℕ), n ≠ 0 ∧ c ≠ 0 ∧ N ≠ 0 ∧
      (∀ k, b * t k * a - t k ∈ latQ S T ΛS ΛT) ∧
      (∀ y, b * y * a - y ∈ latQ S T ΛS ΛT → ∃! k, y - t k ∈ latQ S T ΛS ΛT) ∧
      ∑ k, gamQ ψ S T (sgO D w • (b * t k * a - t k)) (t k) = lam n ∧ lam n ^ 2 = n ∧
      ((c * n : ℕ) : ℚ) = |Algebra.norm ℚ ((N : D.host.E) ^ M * (b ⊗ₖ aᵀ - 1).det)| ∧
      ((c * idx (latF S T ΛS ΛT) ((latF S T ΛS ΛT).map (rhoF S T (g, h))) : ℕ) : ℚ) =
        |Algebra.norm ℚ ((N : D.host.E) ^ M * (b ⊗ₖ aᵀ).det)| := by
  obtain ⟨sd, fg, full, hidx⟩ := GlobalTheory.T.rational_lattice_selfDual_fg_full_index D ψ hψ S T ΛS ΛT hS hT
  rw [hidx g h a b ha hb]
  rw [← det_sandw] at hΔ ⊢
  rw [← det_sandw_sub_one] at hd ⊢
  have hbij : Function.Bijective ⇑(sandw b a - 1) :=
    (Module.End.isUnit_iff _).1 ((LinearMap.isUnit_iff_isUnit_det _).2 hd.isUnit)
  refine ⟨hbij, ?_⟩
  set A := (latQ S T ΛS ΛT).toAddSubgroup with hA
  obtain ⟨N, hN, hNA⟩ : ∃ N : ℕ, N ≠ 0 ∧ ∀ x ∈ A, N • sandw b a x ∈ A := by
    obtain ⟨s, hs⟩ := fg
    choose k hk hk' using full
    refine ⟨∏ y ∈ s, k (sandw b a y), Finset.prod_ne_zero_iff.2 fun y _ => (hk _).ne', fun x hx => ?_⟩
    rw [← hs] at hx
    induction hx using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem (fun y => k (sandw b a y)) hx
      rw [hm, mul_comm, mul_smul]
      exact nsmul_mem (hk' _) m
    | zero => rw [map_zero, smul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add, smul_add]; exact add_mem hx hy
    | neg x _ hx => rw [map_neg, smul_neg]; exact neg_mem hx
  have i1 := GlobalTheory.T.relIndex_map_nsmul_comap_eq_abs_norm_pow_mul_det _ _ A fg full (sandw b a - 1) N hN hd fun x hx => by
    rw [LinearMap.sub_apply, smul_sub]
    exact sub_mem (hNA x hx) (nsmul_mem hx N)
  have i2 := GlobalTheory.T.relIndex_map_nsmul_comap_eq_abs_norm_pow_mul_det _ _ A fg full (sandw b a) N hN hΔ hNA
  set B₁ := A.comap (sandw b a - 1).toAddMonoidHom with hB₁
  set B₂ := A.comap (sandw b a).toAddMonoidHom with hB₂
  set NA := A.map (N • AddMonoidHom.id _) with hNA'
  have e12 : A ⊓ B₁ = A ⊓ B₂ := by
    ext x
    refine and_congr_right fun hx => ?_
    show sandw b a x - x ∈ A ↔ sandw b a x ∈ A
    exact ⟨fun h => by simpa using add_mem h hx, fun h => sub_mem h hx⟩
  have hle : NA ≤ A ⊓ B₂ := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨nsmul_mem hx N, ?_⟩
    show sandw b a (N • x) ∈ A
    rw [map_nsmul]
    exact hNA x hx
  have m1 := AddSubgroup.relIndex_mul_relIndex NA (A ⊓ B₁) B₁ (e12 ▸ hle) inf_le_right
  have m2 := AddSubgroup.relIndex_mul_relIndex NA (A ⊓ B₂) B₂ hle inf_le_right
  rw [AddSubgroup.inf_relIndex_right] at m1 m2
  rw [e12] at m1
  have h0 : NA.relIndex (A ⊓ B₂) * A.relIndex B₁ ≠ 0 := by
    rw [m1, ← Nat.cast_ne_zero (R := ℚ), i1, abs_ne_zero, Algebra.norm_ne_zero_iff]
    exact mul_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.2 hN)) hd
  obtain ⟨t, t1, t2⟩ := exists_transversal A B₁ (right_ne_zero_of_mul h0)
  obtain ⟨g1, g2⟩ := gauss_isometry (isHeis_gamQ hψ.1 S T hw) hlam sd ((sandw b a).restrictScalars (𝓞 D.host.E))
    (fun x y => by
      show ψ (symplO S T (finRat S T (b * x * a)) (finRat S T (b * y * a))) = _
      rw [finRat_sandw ha hb, finRat_sandw ha hb, GlobalTheory.T.symplecticForm_unitaryPairAction]
      rfl) hbij.2 _ t t1 t2
  exact ⟨_, t, _, N, _, right_ne_zero_of_mul h0, left_ne_zero_of_mul h0, hN, t1, t2, g1, g2, m1 ▸ i1, m2 ▸ i2⟩

end Finite

end GlobalTheory.RatAut

end
end
