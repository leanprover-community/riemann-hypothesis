import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.IntegralTransvectionMemSlIntegersConjugateZero
import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.IwasawaDecompositionFiniteAdeles
import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.ATrans
import Mathlib.NumberTheory.NumberField.ProductFormula
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.LatticeIdealNonzero
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.KLevTop
import GroundTheory.AutomorphicForms.StrongApproximationSLDense
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.CompactBoxLattices.MemParahoricTimesPrincipalCongruenceIff
import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.AMinkP
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ScalarStabilizers.FinSupp
import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.DMinkP
import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.DNormalP
import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.DScaleP
import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.DEntryP
import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.DetR
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.CompactBoxLattices.LocTwo
import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.DRepsP
import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.DGoodP

section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk.MonomialSupportLemmas

variable {F : Type} [Field F] [NumberField F]

theorem nrm_unit {w : Pl F} {x : w.adicCompletion F} (h : Valued.v x = 1) : ‖x‖ = 1 :=
  le_antisymm ((Valued.toNormedField.norm_le_one_iff (x := x)).2 h.le)
    ((Valued.toNormedField.one_le_norm_iff (x := x)).2 h.ge)

theorem fin_supp (y : (Af F)ˣ) : (Function.mulSupport fun w : Pl F => ‖pLoc F w (y : Af F)‖).Finite := by
  have h1 := Filter.eventually_cofinite.1 (y : Af F).2
  have h2 := Filter.eventually_cofinite.1 ((y⁻¹ : (Af F)ˣ) : Af F).2
  refine (h1.union h2).subset fun w hw => ?_
  by_contra hc
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hc
  have a1 : Valued.v (pLoc F w (y : Af F)) ≤ 1 := hc.1
  have a2 : Valued.v (pLoc F w ((y⁻¹ : (Af F)ˣ) : Af F)) ≤ 1 := hc.2
  have a3 : Valued.v (pLoc F w (y : Af F)) * Valued.v (pLoc F w ((y⁻¹ : (Af F)ˣ) : Af F)) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  refine hw (nrm_unit (le_antisymm a1 ?_))
  calc 1 = _ := a3.symm
    _ ≤ Valued.v (pLoc F w (y : Af F)) * 1 := mul_le_mul_right a2 _
    _ = _ := mul_one _

end UpperTheory.Esk.MonomialSupportLemmas

open UpperTheory.Esk.MonomialSupportLemmas in
theorem UpperTheory.Esk.aMono : UpperTheory.Esk.AMono := by
  intro F _ _ t t' h
  classical
  unfold absF
  set s := ((fin_supp t).union (fin_supp t')).toFinset
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := s) (by intro w hw; simp [s, hw]),
    finprod_eq_prod_of_mulSupport_subset _ (s := s) (by intro w hw; simp [s, hw])]
  exact Finset.prod_le_prod (fun _ _ => norm_nonneg _)
    fun w _ => (Valued.toNormedField.norm_le_iff).2 (h w)
end
end

section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk.PrimitiveVectorLemmas

variable {F : Type} [Field F] [NumberField F]

omit [NumberField F] in
theorem exists_row (s : Fin 2 → F) (hs : s ≠ 0) : ∃ γ : GL (Fin 2) F, ∀ j, γ.val 1 j = s j := by
  by_cases h0 : s 0 = 0
  · have h1 : s 1 ≠ 0 := by
      intro h1; apply hs; funext i; fin_cases i <;> simp [h0, h1]
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 0; s 0, s 1] (by simp [Matrix.det_fin_two, h1]), ?_⟩
    intro j; fin_cases j <;> rfl
  · refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; s 0, s 1] (by simp [Matrix.det_fin_two, h0]), ?_⟩
    intro j; fin_cases j <;> rfl

theorem row_mul (s : Fin 2 → F) (γ : GL (Fin 2) F) (hγ : ∀ j, γ.val 1 j = s j) (x : GF F) (i : Fin 2) :
    rowF s x i = (jF F γ * x).val 1 i := by
  simp [rowF, jF, Matrix.mul_apply, Matrix.vecMul, dotProduct, hγ]

theorem row_zak (d a : (Af F)ˣ) (u : Af F) (k : GF F) (i : Fin 2) :
    (zc F d * aff a u * k).val 1 i = (d : Af F) * k.val 1 i := by
  simp [zc, aff, Matrix.mul_apply, Fin.sum_univ_two, Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply,
    Matrix.diagonal_apply]

end UpperTheory.Esk.PrimitiveVectorLemmas

theorem UpperTheory.Esk.aRow : UpperTheory.Esk.AMem → UpperTheory.Esk.AIw → UpperTheory.Esk.ARow := by
  intro hM hI F _ _ s x
  refine ⟨fun hs => ?_, fun t k hk hrow => ?_⟩
  · obtain ⟨γ, hγ⟩ := UpperTheory.Esk.PrimitiveVectorLemmas.exists_row s hs
    obtain ⟨d, a, u, k, hk, he⟩ := hI F (UpperTheory.Esk.jF F γ * x)
    refine ⟨d, k, hk, fun i => ?_⟩
    rw [UpperTheory.Esk.PrimitiveVectorLemmas.row_mul s γ hγ x i, he, UpperTheory.Esk.PrimitiveVectorLemmas.row_zak]
  · obtain ⟨-, -, -, -, h5, -⟩ := hM F
    have key : ∀ w : Pl F, max ‖pLoc F w (k.val 1 0)‖ ‖pLoc F w (k.val 1 1)‖ = 1 := by
      intro w
      have h := (h5 k hk w).2
      refine le_antisymm (max_le (Valued.toNormedField.norm_le_one_iff.2 ((le_max_left _ _).trans h.le))
        (Valued.toNormedField.norm_le_one_iff.2 ((le_max_right _ _).trans h.le))) ?_
      rcases max_choice (Valued.v (pLoc F w (k.val 1 0))) (Valued.v (pLoc F w (k.val 1 1))) with hh | hh <;> rw [hh] at h
      · exact le_max_of_le_left (Valued.toNormedField.one_le_norm_iff.2 h.ge)
      · exact le_max_of_le_right (Valued.toNormedField.one_le_norm_iff.2 h.ge)
    have hw : ∀ w : Pl F, max ‖pLoc F w (UpperTheory.Esk.rowF s x 0)‖ ‖pLoc F w (UpperTheory.Esk.rowF s x 1)‖ =
        ‖pLoc F w (t : Af F)‖ := by
      intro w
      rw [hrow 0, hrow 1, map_mul, map_mul, norm_mul, norm_mul, ← mul_max_of_nonneg _ _ (norm_nonneg _), key w, mul_one]
    show ∏ᶠ w : Pl F, max ‖pLoc F w (UpperTheory.Esk.rowF s x 0)‖ ‖pLoc F w (UpperTheory.Esk.rowF s x 1)‖ = ∏ᶠ w : Pl F, ‖pLoc F w (t : Af F)‖
    exact finprod_congr hw
end
end

section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk.ClassNumberLemmas

theorem v_one {F : Type} [Field F] [NumberField F] (e : (Af F)ˣ) (h1 : (e : Af F) ∈ PIW.ClassFinD.Ohat F)
    (h2 : ((e⁻¹ : (Af F)ˣ) : Af F) ∈ PIW.ClassFinD.Ohat F) (w : Pl F) : Valued.v (pLoc F w (e : Af F)) = 1 := by
  have a1 : Valued.v (pLoc F w (e : Af F)) ≤ 1 := by
    have h := h1 w
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h
    exact h
  have a2 : Valued.v (pLoc F w ((e⁻¹ : (Af F)ˣ) : Af F)) ≤ 1 := by
    have h := h2 w
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h
    exact h
  have hm : Valued.v (pLoc F w (e : Af F)) * Valued.v (pLoc F w ((e⁻¹ : (Af F)ˣ) : Af F)) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  refine le_antisymm a1 ?_
  calc (1 : _) = Valued.v (pLoc F w (e : Af F)) * Valued.v (pLoc F w ((e⁻¹ : (Af F)ˣ) : Af F)) := hm.symm
    _ ≤ Valued.v (pLoc F w (e : Af F)) * 1 := by gcongr
    _ = Valued.v (pLoc F w (e : Af F)) := mul_one _

end UpperTheory.Esk.ClassNumberLemmas

namespace UpperTheory.Esk

theorem aCls : ACls := by
  intro F _ _
  obtain ⟨C, hC⟩ := PIW.ClassFinD.idele_class_finite F
  refine ⟨C, fun z => ?_⟩
  obtain ⟨f, c, hc, e, he1, he2, hz⟩ := hC z
  exact ⟨f, e, c, hc, ClassNumberLemmas.v_one e he1 he2, hz⟩

end UpperTheory.Esk
end
end

section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk

theorem aAdd : AMem → AAdd := by
  intro _ F _ _ t u
  have hU : IsOpen {z : Af F | ((t⁻¹ : (Af F)ˣ) : Af F) * (u - z) ∈ Ohat F} :=
    isOpen_Ohat.preimage (by fun_prop)
  obtain ⟨y, hy⟩ := (GroundTheory.Automorphic.AdelicGLn.denseRange_algebraMap_finiteAdeleRing F).exists_mem_open hU
    ⟨u, by simp⟩
  exact ⟨y, hy⟩

end UpperTheory.Esk
end
end

section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk.AdelicNormalFormLemmas

theorem key {R : Type} [CommRing R] (c α r e r' e' : Rˣ) (u y0 : R) (k : GL (Fin 2) R) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) c⁻¹ * aff α⁻¹ (-y0) *
      (Matrix.GeneralLinearGroup.scalar (Fin 2) (c * r * e) * aff (α * r' * e') u * k) =
    Matrix.GeneralLinearGroup.scalar (Fin 2) r * aff r' 0 *
      (aff 1 (((r'⁻¹ : Rˣ) : R) * (((α⁻¹ : Rˣ) : R) * u - y0)) *
        (Matrix.GeneralLinearGroup.scalar (Fin 2) e * aff e' 0 * k)) := by
  have h1 : Matrix.GeneralLinearGroup.scalar (Fin 2) c⁻¹ * aff α⁻¹ (-y0) *
      (Matrix.GeneralLinearGroup.scalar (Fin 2) (c * r * e) * aff (α * r' * e') u) =
    Matrix.GeneralLinearGroup.scalar (Fin 2) r * aff r' 0 *
      (aff 1 (((r'⁻¹ : Rˣ) : R) * (((α⁻¹ : Rˣ) : R) * u - y0)) *
        (Matrix.GeneralLinearGroup.scalar (Fin 2) e * aff e' 0)) := by
    have hc := Units.inv_mul c
    have ha := Units.inv_mul α
    have hr := Units.mul_inv r'
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [aff, Matrix.mul_apply, Fin.sum_univ_two, Matrix.GeneralLinearGroup.scalar, Matrix.vecMul, dotProduct,
        Matrix.diagonal_apply] <;>
      first
      | linear_combination (((α⁻¹ : Rˣ) : R) * α * r * e * r' * e') * hc + ((r : R) * e * r' * e') * ha
      | linear_combination ((r : R) * e * (((α⁻¹ : Rˣ) : R) * u - y0)) * hc - ((r : R) * e * (((α⁻¹ : Rˣ) : R) * u - y0)) * hr
      | linear_combination ((r : R) * e) * hc
  calc _ = (Matrix.GeneralLinearGroup.scalar (Fin 2) c⁻¹ * aff α⁻¹ (-y0) *
      (Matrix.GeneralLinearGroup.scalar (Fin 2) (c * r * e) * aff (α * r' * e') u)) * k := by group
    _ = _ := by rw [h1]; group

theorem jF_sa {F : Type} [Field F] [NumberField F] (c α : Fˣ) (β : F) :
    UpperTheory.Esk.jF F (Matrix.GeneralLinearGroup.scalar (Fin 2) c * aff α β) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (ratU F c) * aff (ratU F α) (algebraMap F (Af F) β) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [UpperTheory.Esk.jF, ratU, aff, Matrix.mul_apply, Matrix.GeneralLinearGroup.scalar, Matrix.diagonal_apply]

end UpperTheory.Esk.AdelicNormalFormLemmas

open UpperTheory.Esk.AdelicNormalFormLemmas in
theorem UpperTheory.Esk.aBnf : UpperTheory.Esk.AMem → UpperTheory.Esk.AIw → UpperTheory.Esk.ACls → UpperTheory.Esk.AAdd → UpperTheory.Esk.ABnf := by
  intro hM hI hC hA F _ _
  classical
  obtain ⟨T, hT⟩ := hC F
  refine ⟨(T ×ˢ T).image (fun p => zc F p.1 * aff p.2 0), fun x => ?_⟩
  obtain ⟨d, a, u, k, hk, rfl⟩ := hI F x
  obtain ⟨y, e, r, hr, he, hd⟩ := hT d
  obtain ⟨y', e', r', hr', he', ha⟩ := hT a
  obtain ⟨y0, hy0⟩ := hA F r' ((((ratU F y')⁻¹ : (Af F)ˣ) : Af F) * u)
  have hK := (hM F).2.2.2.2.2.2.2
  refine ⟨Matrix.GeneralLinearGroup.scalar (Fin 2) y⁻¹ * aff y'⁻¹ (-y0), ?_, zc F r * aff r' 0,
    Finset.mem_image.2 ⟨(r, r'), Finset.mem_product.2 ⟨hr, hr'⟩, rfl⟩,
    aff 1 (((r'⁻¹ : (Af F)ˣ) : Af F) * ((((ratU F y')⁻¹ : (Af F)ˣ) : Af F) * u - algebraMap F (Af F) y0)) *
      (zc F e * aff e' 0 * k), ?_, ?_⟩
  · simp [aff, Matrix.GeneralLinearGroup.scalar, Matrix.mul_apply, Fin.sum_univ_two]
  · exact Subgroup.mul_mem _ ((hK 1 (by simp)).2 _ hy0)
      (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hK e he).1 ((hK e' he').2 0 (zero_mem _))) hk)
  · rw [jF_sa, map_inv, map_inv, map_neg, hd, ha]
    exact key (ratU F y) (ratU F y') r e r' e' u (algebraMap F (Af F) y0) k
end
end

section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk

theorem aOrb : AMem → AOrb := by
  intro _ F _ _ c hc x
  have hT := UpperTheory.V.Sd.Wc.kcTop F
  have hK0 : IsCompact (K0 F : Set (GF F)) := ((hT.1 (fun _ => 0) (by simp)).2)
  have hKo : IsOpen (Kc c : Set (GF F)) := (hT.1 c hc).1
  have hs : IsCompact ((fun k : GF F => k * x) '' (K0 F : Set (GF F))) :=
    hK0.image (continuous_id.mul continuous_const)
  obtain ⟨t, -, ht⟩ := hs.elim_nhds_subcover (fun g => (fun y : GF F => g⁻¹ * y) ⁻¹' (Kc c : Set (GF F)))
    (fun g _ => (hKo.preimage (continuous_const.mul continuous_id)).mem_nhds (by simp [(Kc c).one_mem]))
  refine ⟨t, fun k hk => ?_⟩
  have hm := ht ⟨k, hk, rfl⟩
  simp only [Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe] at hm
  obtain ⟨g, hg, hgk⟩ := hm
  exact ⟨g, hg, g⁻¹ * (k * x), hgk, by rw [mul_inv_cancel_left]⟩

end UpperTheory.Esk
end
end

section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk

theorem aBnfH : UpperTheory.Esk.ABnf → UpperTheory.Esk.AOrb → UpperTheory.Esk.ABnfH := by
  classical
  intro hB hO F _ _ c hc
  obtain ⟨S, hS⟩ := hB F
  obtain ⟨T, hT⟩ := hO F c hc 1
  refine ⟨Finset.image₂ (· * ·) S T, fun x => ?_⟩
  obtain ⟨b, hb, x', hx', k, hk, hx⟩ := hS x
  obtain ⟨y, hy, h, hh, hkh⟩ := hT k hk
  refine ⟨b, hb, x' * y, Finset.mem_image₂_of_mem hx' hy, h, hh, ?_⟩
  rw [hx, mul_assoc, ← hkh, mul_one]

end UpperTheory.Esk
end
end

section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk.NearUnitLemmas

open scoped Classical

abbrev bU (F : Type) [Field F] [NumberField F] :=
  (NumberField.Units.basisUnitLattice F).ofZLatticeBasis ℝ (NumberField.Units.unitLattice F)

theorem abs_sg {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (v : InfinitePlace F) (x : F) :
    |sg v x| = v x := by
  simpa [Real.norm_eq_abs] using InfinitePlace.norm_embedding_of_isReal (IsTotallyReal.isReal v) x

theorem near_unit (F : Type) [Field F] [NumberField F] (a : NumberField.Units.dirichletUnitTheorem.logSpace F) :
    ∃ x : (𝓞 F)ˣ, ∀ w : {w : InfinitePlace F // w ≠ NumberField.Units.dirichletUnitTheorem.w₀},
      |a w - InfinitePlace.mult w.1 * Real.log (w.1 (x : F))| ≤ ∑ i, ‖bU F i‖ := by
  have hmem : (ZSpan.floor (bU F) a : NumberField.Units.dirichletUnitTheorem.logSpace F) ∈
      NumberField.Units.unitLattice F := by
    rw [← Module.Basis.ofZLatticeBasis_span ℝ (NumberField.Units.unitLattice F)
      (NumberField.Units.basisUnitLattice F)]
    exact (ZSpan.floor (bU F) a).2
  obtain ⟨x, -, hx⟩ := Submodule.mem_map.1 hmem
  refine ⟨x.toMul, fun w => ?_⟩
  have h1 : InfinitePlace.mult w.1 * Real.log (w.1 ((x.toMul : (𝓞 F)ˣ) : F)) =
      (ZSpan.floor (bU F) a : NumberField.Units.dirichletUnitTheorem.logSpace F) w := by
    rw [← hx]; rfl
  rw [h1]
  have h2 : a w - (ZSpan.floor (bU F) a : NumberField.Units.dirichletUnitTheorem.logSpace F) w =
      ZSpan.fract (bU F) a w := by rw [ZSpan.fract_apply]; rfl
  rw [h2, ← Real.norm_eq_abs]
  exact (norm_le_pi_norm _ w).trans (ZSpan.norm_fract_le _ _)

end UpperTheory.Esk.NearUnitLemmas

namespace UpperTheory.Esk

open UpperTheory.Esk.NearUnitLemmas in
theorem aUnit : UpperTheory.Esk.AUnit := by
  classical
  intro F _ _ _
  set M : ℝ := ∑ i, ‖bU F i‖ with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun i _ => norm_nonneg _
  refine ⟨Real.exp (2 * (Fintype.card (InfinitePlace F) * M)), Real.exp_pos _, fun y hy => ?_⟩
  set L : InfinitePlace F → ℝ := fun w => Real.log |y w|
  set m : ℝ := (∑ w, L w) / Fintype.card (InfinitePlace F)
  obtain ⟨x, hx⟩ := near_unit F (fun w => m - L w.1)
  set u : F := (x : F)
  have hmult : ∀ w : InfinitePlace F, InfinitePlace.mult w = 1 :=
    fun w => (IsTotallyReal.isReal w).mult_eq_one
  set d : InfinitePlace F → ℝ := fun w => Real.log (w u) + L w - m
  have hn : (Fintype.card (InfinitePlace F) : ℝ) ≠ 0 := by
    have : 0 < Fintype.card (InfinitePlace F) := Fintype.card_pos
    exact_mod_cast this.ne'
  have hsum : ∑ w, d w = 0 := by
    have h0 : ∑ w : InfinitePlace F, Real.log (w u) = 0 := by
      simpa [hmult] using NumberField.Units.sum_mult_mul_log x
    simp only [d, Finset.sum_sub_distrib, Finset.sum_add_distrib, h0, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, m]
    field_simp
    ring
  have hne : ∀ w : {w : InfinitePlace F // w ≠ NumberField.Units.dirichletUnitTheorem.w₀}, |d w| ≤ M := by
    intro w
    have := hx w
    rw [hmult, Nat.cast_one, one_mul] at this
    calc |d w| = |(m - L w.1) - Real.log (w.1 u)| := by
          rw [← abs_neg]; congr 1; simp only [d]; ring
      _ ≤ M := this
  have hall : ∀ w, |d w| ≤ Fintype.card (InfinitePlace F) * M := by
    intro w
    by_cases hw : w = NumberField.Units.dirichletUnitTheorem.w₀
    · subst hw
      have h := Fintype.sum_eq_add_sum_subtype_ne d NumberField.Units.dirichletUnitTheorem.w₀
      rw [hsum] at h
      have h' : d NumberField.Units.dirichletUnitTheorem.w₀ =
          -∑ w : {w : InfinitePlace F // w ≠ NumberField.Units.dirichletUnitTheorem.w₀}, d w := by
        linarith
      rw [h', abs_neg]
      calc |∑ w : {w : InfinitePlace F // w ≠ NumberField.Units.dirichletUnitTheorem.w₀}, d w|
          ≤ ∑ w : {w : InfinitePlace F // w ≠ NumberField.Units.dirichletUnitTheorem.w₀}, |d w| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _w : {w : InfinitePlace F // w ≠ NumberField.Units.dirichletUnitTheorem.w₀}, M :=
            Finset.sum_le_sum fun w _ => hne w
        _ = (Fintype.card {w : InfinitePlace F // w ≠ NumberField.Units.dirichletUnitTheorem.w₀} : ℝ) * M := by
            simp
        _ ≤ Fintype.card (InfinitePlace F) * M := by
            gcongr
            exact_mod_cast Fintype.card_subtype_le _
    · calc |d w| ≤ M := hne ⟨w, hw⟩
        _ ≤ Fintype.card (InfinitePlace F) * M := by
          have : (1 : ℝ) ≤ Fintype.card (InfinitePlace F) := by exact_mod_cast Fintype.card_pos
          nlinarith
  have hu0 : ∀ w : InfinitePlace F, 0 < w u := fun w => NumberField.Units.pos_at_place x w
  have hval : ∀ w, |sg w u * y w| = Real.exp (d w + m) := by
    intro w
    simp only [d, L]
    rw [abs_mul, abs_sg, sub_add_cancel, Real.exp_add, Real.exp_log (hu0 w),
      Real.exp_log (abs_pos.2 (hy w))]
  refine ⟨u, ?_, ?_, ?_, fun v v' => ?_⟩
  · intro h
    have := hu0 NumberField.Units.dirichletUnitTheorem.w₀
    rw [h, map_zero] at this
    exact lt_irrefl _ this
  · exact NumberField.RingOfIntegers.isIntegral_coe (x : 𝓞 F)
  · have : u⁻¹ = ((x⁻¹ : (𝓞 F)ˣ) : F) := by simp [u]
    rw [this]
    exact NumberField.RingOfIntegers.isIntegral_coe ((x⁻¹ : (𝓞 F)ˣ) : 𝓞 F)
  · rw [hval, hval, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have h1 := (abs_le.1 (hall v)).2
    have h2 := (abs_le.1 (hall v')).1
    linarith

end UpperTheory.Esk
end
end

section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk

theorem aTrans : ATrans := by
  intro F _ _ _
  classical
  let b := mixedEmbedding.latticeBasis F
  refine ⟨(∑ i, ‖b i‖) + 1, by positivity, fun x => ?_⟩
  let p : mixedEmbedding.mixedSpace F := (fun w => x w.1, 0)
  have hm : (ZSpan.floor b p : mixedEmbedding.mixedSpace F) ∈
      Submodule.span ℤ (Set.range b) := (ZSpan.floor b p).2
  rw [mixedEmbedding.mem_span_latticeBasis] at hm
  obtain ⟨s, hs⟩ := hm
  refine ⟨-(s : F), (RingOfIntegers.isIntegral_coe s).neg, fun v => ?_⟩
  have h1 := ZSpan.norm_fract_le b p
  have h2 : (ZSpan.fract b p).1 ⟨v, IsTotallyReal.isReal v⟩ = x v + sg v (-(s : F)) := by
    rw [ZSpan.fract_apply, ← hs]
    simp [p, sg, sub_eq_add_neg]
  have h3 : ‖(ZSpan.fract b p).1 ⟨v, IsTotallyReal.isReal v⟩‖ ≤ ‖ZSpan.fract b p‖ :=
    (norm_le_pi_norm _ _).trans (norm_fst_le _)
  rw [h2, Real.norm_eq_abs] at h3
  linarith

end UpperTheory.Esk
end
end

section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk

theorem dCount : AMem → ABnfH → AOrb → DCount := by
  intro hM hB hO F _ _ _ c hc χ
  have : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  have hKH : Kc c ≤ Hc c := le_sup_left
  have hzH : ∀ z, zc F z ∈ Hc c := fun z => Subgroup.mem_sup_right ⟨z, rfl⟩
  obtain ⟨-, -, hKK, hHd, -⟩ := hM F
  show Countable (GF F ⧸ Hc c) ∧ ∀ a : GF F,
    {ω : GF F ⧸ Hc c | ∃ h ∈ Hc c, ω = ((h * a : GF F) : GF F ⧸ Hc c)}.Finite
  refine ⟨?_, fun a => ?_⟩
  · obtain ⟨S, hS⟩ := hB F c hc
    have : Countable (Matrix (Fin 2) (Fin 2) F) := inferInstanceAs (Countable (Fin 2 → Fin 2 → F))
    have : Countable (GL (Fin 2) F) :=
      (show Function.Injective (Units.val : GL (Fin 2) F → Matrix (Fin 2) (Fin 2) F) from
        fun _ _ h => Units.ext h).countable
    refine Function.Surjective.countable
      (f := fun p : GL (Fin 2) F × S => ((jF F p.1 * p.2.1 : GF F) : GF F ⧸ Hc c)) ?_
    intro ω
    induction ω using QuotientGroup.induction_on with
    | H x =>
      obtain ⟨b, -, x', hx', h, hh, e⟩ := hS x
      refine ⟨(b⁻¹, ⟨x', hx'⟩), QuotientGroup.eq.2 ?_⟩
      have hx : x = jF F b⁻¹ * x' * h := by rw [map_inv, mul_assoc, ← e, inv_mul_cancel_left]
      show (jF F b⁻¹ * x')⁻¹ * x ∈ Hc c
      rw [hx, inv_mul_cancel_left]
      exact hKH hh
  · obtain ⟨S, hS⟩ := hO F c hc a
    refine (S.finite_toSet.image (fun x : GF F => (x : GF F ⧸ Hc c))).subset ?_
    rintro ω ⟨h, hh, rfl⟩
    obtain ⟨k, hk, z, rfl⟩ := (hHd c h).1 hh
    obtain ⟨x', hx', h', hh', e⟩ := hS k (hKK c hk)
    refine ⟨x', hx', QuotientGroup.eq.2 ?_⟩
    have he : k * zc F z * a = x' * (h' * zc F z) := by
      rw [mul_assoc, ← Subgroup.mem_center_iff.1 (zc_center z) a, ← mul_assoc, e, mul_assoc]
    rw [he, inv_mul_cancel_left]
    exact mul_mem (hKH hh') (hzH z)

end UpperTheory.Esk
end
end

section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk.HeightFunctionLemmas

variable {F : Type} [Field F] [NumberField F]

theorem nF_eq (s : Fin 2 → F) (x : GF F) :
    nF s x = ∏ᶠ w : Pl F, max ‖pLoc F w (rowF s x 0)‖ ‖pLoc F w (rowF s x 1)‖ := rfl

theorem rowF_jF (s : Fin 2 → F) (γ : GL (Fin 2) F) (x : GF F) :
    rowF s (jF F γ * x) = rowF (s ᵥ* γ.val) x := by
  unfold rowF
  have h : (fun i => algebraMap F (Af F) ((s ᵥ* γ.val) i)) =
      (fun i => algebraMap F (Af F) (s i)) ᵥ* (jF F γ).val := by
    funext i
    exact RingHom.map_vecMul (algebraMap F (Af F)) γ.val s i
  rw [h, Units.val_mul, Matrix.vecMul_vecMul]

theorem rowF_smul (s : Fin 2 → F) (a : F) (x : GF F) (i : Fin 2) :
    rowF (a • s) x i = algebraMap F (Af F) a * rowF s x i := by
  unfold rowF
  have h : (fun i => algebraMap F (Af F) ((a • s) i)) = algebraMap F (Af F) a • (fun i => algebraMap F (Af F) (s i)) := by
    funext i
    simp [map_mul]
  rw [h, Matrix.smul_vecMul, Pi.smul_apply, smul_eq_mul]

theorem det_jF (γ : GL (Fin 2) F) :
    Matrix.GeneralLinearGroup.det (jF F γ) = ratU F (Matrix.GeneralLinearGroup.det γ) := by
  apply Units.ext
  change (γ.val.map (algebraMap F (Af F))).det = algebraMap F (Af F) γ.val.det
  exact (RingHom.map_det (algebraMap F (Af F)) γ.val).symm

variable [IsTotallyReal F]

theorem nF_pos (hR : ARow) {s : Fin 2 → F} (hs : s ≠ 0) (x : GF F) : 0 < nF s x := by
  obtain ⟨t, k, hk, h⟩ := (hR F s x).1 hs
  rw [(hR F s x).2 t k hk h]
  exact (Hm.absf F).1 t

theorem reAt_eq (v : InfinitePlace F) (x : F) : reAt v x = sg v x := by
  unfold reAt
  rw [← InfinitePlace.embedding_of_isReal_apply (IsTotallyReal.isReal v) x, Complex.ofReal_re]

theorem prod_rat (a : Fˣ) : (∏ v, |sg v (a : F)|) * absF (ratU F a) = 1 := by
  have := (Hm.absf F).2.2.2 a
  simp only [reAt_eq] at this
  exact this

end UpperTheory.Esk.HeightFunctionLemmas

open UpperTheory.Esk.HeightFunctionLemmas in
theorem UpperTheory.Esk.dHt : UpperTheory.Esk.ARow → UpperTheory.Esk.DHt := by
  intro hR F _ _ _ c _ χ
  refine ⟨fun s hs x => ?_, fun s hs γ x => ?_, fun s hs a ha x => ?_⟩
  · change 0 < absF (Matrix.GeneralLinearGroup.det x) / nF s x ^ 2
    exact div_pos ((Hm.absf F).1 _) (pow_pos (nF_pos hR hs x) 2)
  · change absF (Matrix.GeneralLinearGroup.det (jF F γ * x)) / nF s (jF F γ * x) ^ 2 * ∏ v, |sg v γ.val.det| =
      absF (Matrix.GeneralLinearGroup.det x) / nF (s ᵥ* γ.val) x ^ 2
    have hP := prod_rat (Matrix.GeneralLinearGroup.det γ)
    rw [Matrix.GeneralLinearGroup.val_det_apply] at hP
    rw [map_mul, det_jF, (Hm.absf F).2.1, nF_eq s, rowF_jF, ← nF_eq]
    calc absF (ratU F (Matrix.GeneralLinearGroup.det γ)) * absF (Matrix.GeneralLinearGroup.det x) / nF (s ᵥ* γ.val) x ^ 2 *
          ∏ v, |sg v γ.val.det|
        = ((∏ v, |sg v γ.val.det|) * absF (ratU F (Matrix.GeneralLinearGroup.det γ))) *
          (absF (Matrix.GeneralLinearGroup.det x) / nF (s ᵥ* γ.val) x ^ 2) := by ring
      _ = _ := by rw [hP, one_mul]
  · change absF (Matrix.GeneralLinearGroup.det x) / nF (a • s) x ^ 2 =
      absF (Matrix.GeneralLinearGroup.det x) / nF s x ^ 2 * ∏ v, sg v a ^ 2
    obtain ⟨t, k, hk, h⟩ := (hR F s x).1 hs
    have h1 := (hR F s x).2 t k hk h
    have h2 : nF (a • s) x = absF (ratU F (Units.mk0 a ha)) * nF s x := by
      rw [(hR F (a • s) x).2 (ratU F (Units.mk0 a ha) * t) k hk (fun i => by
        rw [rowF_smul, h i, Units.val_mul, mul_assoc]; rfl), (Hm.absf F).2.1, h1]
    have hP := prod_rat (Units.mk0 a ha)
    simp only [Units.val_mk0] at hP
    have hA := (Hm.absf F).1 (ratU F (Units.mk0 a ha))
    have hN := nF_pos hR hs x
    have hsq : ∏ v, sg v a ^ 2 = (∏ v, |sg v a|) ^ 2 := by
      rw [← Finset.prod_pow]; simp [sq_abs]
    rw [h2, hsq, eq_inv_of_mul_eq_one_left hP]
    field_simp
end
end

section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk.HeightMultiplicativityAlt

theorem rowF_mul {F : Type} [Field F] [NumberField F] (s : Fin 2 → F) (x y : GF F) :
    rowF s (x * y) = rowF s x ᵥ* y.val := by
  simp only [rowF, Units.val_mul, Matrix.vecMul_vecMul]

theorem row_mul {F : Type} [Field F] [NumberField F] (t : Af F) (k : GF F) (M : Matrix (Fin 2) (Fin 2) (Af F)) :
    (fun i => t * k.val 1 i) ᵥ* M = fun i => t * (k.val * M) 1 i := by
  ext i
  simp [Matrix.vecMul, dotProduct, Matrix.mul_apply, Fin.sum_univ_two, mul_add, mul_assoc]

theorem zc_val {F : Type} [Field F] [NumberField F] (z : (Af F)ˣ) :
    (zc F z).val = Matrix.scalar (Fin 2) (z : Af F) := rfl

theorem det_zc {F : Type} [Field F] [NumberField F] (z : (Af F)ˣ) :
    Matrix.GeneralLinearGroup.det (zc F z) = z * z := by
  apply Units.ext
  simp [Matrix.GeneralLinearGroup.val_det_apply, zc_val, pow_two]

theorem part1 (hM : AMem) (hR : ARow) (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (c : Pl F → ℕ)
    (s : Fin 2 → F) (hs : s ≠ 0) (x h : GF F) (hh : h ∈ Hc c) :
    absF (Matrix.GeneralLinearGroup.det (x * h)) / nF s (x * h) ^ 2 =
      absF (Matrix.GeneralLinearGroup.det x) / nF s x ^ 2 := by
  obtain ⟨-, -, hKc, hH, hdet, -⟩ := hM F
  obtain ⟨hA1, hA2, hA3, -⟩ := UpperTheory.V.Sd.Hm.absf F
  obtain ⟨k', hk', z, rfl⟩ := (hH c h).1 hh
  obtain ⟨t, k, hk, ht⟩ := (hR F s x).1 hs
  have hk'0 : k' ∈ K0 F := hKc c hk'
  have e1 : nF s x = absF t := (hR F s x).2 t k hk ht
  have hx : rowF s x = fun i => (t : Af F) * k.val 1 i := funext ht
  have e2 : nF s (x * (k' * zc F z)) = absF (t * z) := by
    refine (hR F s _).2 (t * z) (k * k') (mul_mem hk hk'0) fun i => ?_
    rw [rowF_mul, hx, row_mul]
    simp only [Units.val_mul, zc_val, ← Matrix.mul_assoc, Matrix.scalar_apply, Matrix.mul_diagonal]
    ring
  have e3 : absF (Matrix.GeneralLinearGroup.det k') = 1 := hA3 _ fun w => (hdet k' hk'0 w).1
  rw [e1, e2, map_mul, map_mul, det_zc]
  simp only [hA2, e3]
  have := (hA1 t).ne'
  have := (hA1 z).ne'
  field_simp

theorem part2 (hM : AMem) (hR : ARow) (hMo : AMono) (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
    (a : GF F) : ∃ C : ℝ, ∀ s : Fin 2 → F, s ≠ 0 → ∀ x : GF F,
      absF (Matrix.GeneralLinearGroup.det (x * a)) / nF s (x * a) ^ 2 ≤
        C * (absF (Matrix.GeneralLinearGroup.det x) / nF s x ^ 2) := by
  obtain ⟨hK, hO, -, -, hdet, -, hN, -⟩ := hM F
  obtain ⟨hA1, hA2, -, -⟩ := UpperTheory.V.Sd.Hm.absf F
  obtain ⟨N, hN0, hNa⟩ := hN a⁻¹
  have hNF : (N : F) ≠ 0 := Nat.cast_ne_zero.2 hN0
  obtain ⟨n, hn⟩ : ∃ n : (Af F)ˣ, (n : Af F) = (N : Af F) :=
    ⟨ratU F (Units.mk0 (N : F) hNF), by simp [ratU]⟩
  refine ⟨absF (Matrix.GeneralLinearGroup.det a) / absF n ^ 2, fun s hs x => ?_⟩
  obtain ⟨t, k, hk, ht⟩ := (hR F s x).1 hs
  obtain ⟨t', k', hk', ht'⟩ := (hR F s (x * a)).1 hs
  rw [(hR F s x).2 t k hk ht, (hR F s (x * a)).2 t' k' hk' ht']
  have key : absF (n * t) ≤ absF t' := by
    refine hMo F _ _ fun w => ?_
    have hrow : rowF s x = rowF s (x * a) ᵥ* (a⁻¹ : GF F).val := by
      rw [← rowF_mul, mul_inv_cancel_right]
    have hint : ∀ i j, Valued.v (pLoc F w (k'.val i j)) ≤ 1 := fun i j =>
      (hO _).1 (((hK k').1 hk').1 i j) w
    have hint2 : ∀ i j, Valued.v (pLoc F w ((N : Af F) * (a⁻¹ : GF F).val i j)) ≤ 1 := fun i j =>
      (hO _).1 (hNa i j) w
    have heq : ∀ i, (n : Af F) * ((t : Af F) * k.val 1 i) = (t' : Af F) * (k'.val 1 0 * ((N : Af F) * (a⁻¹ : GF F).val 0 i) +
        k'.val 1 1 * ((N : Af F) * (a⁻¹ : GF F).val 1 i)) := by
      intro i
      have h1 := congrFun hrow i
      rw [← ht i, hn, h1]
      simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_two, ht']
      ring
    have hS : ∀ i, Valued.v (pLoc F w (k'.val 1 0 * ((N : Af F) * (a⁻¹ : GF F).val 0 i) +
        k'.val 1 1 * ((N : Af F) * (a⁻¹ : GF F).val 1 i))) ≤ 1 := by
      intro i
      rw [map_add]
      refine Valuation.map_add_le _ ?_ ?_ <;> rw [map_mul, map_mul] <;> exact mul_le_one' (hint _ _) (hint2 _ _)
    have hmax := (hdet k hk w).2
    obtain ⟨i, hi⟩ : ∃ i, Valued.v (pLoc F w (k.val 1 i)) = 1 := by
      rcases max_choice (Valued.v (pLoc F w (k.val 1 0))) (Valued.v (pLoc F w (k.val 1 1))) with h | h
      · exact ⟨0, h.symm.trans hmax⟩
      · exact ⟨1, h.symm.trans hmax⟩
    calc Valued.v (pLoc F w ((n * t : (Af F)ˣ) : Af F))
        = Valued.v (pLoc F w ((n : Af F) * ((t : Af F) * k.val 1 i))) := by
          simp only [Units.val_mul, map_mul, hi, mul_one]
      _ = Valued.v (pLoc F w (t' : Af F)) * Valued.v (pLoc F w (k'.val 1 0 * ((N : Af F) * (a⁻¹ : GF F).val 0 i) +
          k'.val 1 1 * ((N : Af F) * (a⁻¹ : GF F).val 1 i))) := by
          rw [heq i, map_mul (pLoc F w), map_mul Valued.v]
      _ ≤ Valued.v (pLoc F w (t' : Af F)) * 1 := mul_le_mul' le_rfl (hS i)
      _ = _ := mul_one _
  rw [map_mul, hA2]
  have key2 : absF n * absF t ≤ absF t' := by rw [← hA2]; exact key
  have p1 := hA1 n
  have p2 := hA1 t
  have p3 := hA1 t'
  have p4 := hA1 (Matrix.GeneralLinearGroup.det x)
  have p5 := hA1 (Matrix.GeneralLinearGroup.det a)
  calc absF (Matrix.GeneralLinearGroup.det x) * absF (Matrix.GeneralLinearGroup.det a) / absF t' ^ 2
      ≤ absF (Matrix.GeneralLinearGroup.det x) * absF (Matrix.GeneralLinearGroup.det a) / (absF n * absF t) ^ 2 :=
        div_le_div_of_nonneg_left (mul_pos p4 p5).le (pow_pos (mul_pos p1 p2) 2)
          (pow_le_pow_left₀ (mul_pos p1 p2).le key2 2)
    _ = _ := by
      field_simp

end UpperTheory.Esk.HeightMultiplicativityAlt

theorem UpperTheory.Esk.dMul : UpperTheory.Esk.AMem → UpperTheory.Esk.AIw → UpperTheory.Esk.AMono → UpperTheory.Esk.ARow → UpperTheory.Esk.DMul := by
  intro hM _ hMo hR F _ _ _ c _ χ
  exact ⟨fun s hs x h hh => UpperTheory.Esk.HeightMultiplicativityAlt.part1 hM hR F c s hs x h hh,
    fun a => UpperTheory.Esk.HeightMultiplicativityAlt.part2 hM hR hMo F a⟩
end
end

section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk.HeightProductFormula

theorem reAt_eq {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (v : InfinitePlace F) (x : F) :
    reAt v x = sg v x := by
  rw [reAt, ← InfinitePlace.embedding_of_isReal_apply (IsTotallyReal.isReal v), Complex.ofReal_re]

theorem rowF_apply {F : Type} [Field F] [NumberField F] (s : Fin 2 → F) (x : GF F) (i : Fin 2) :
    rowF s x i = algebraMap F (Af F) (s 0) * x.val 0 i + algebraMap F (Af F) (s 1) * x.val 1 i := by
  simp [rowF, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

theorem det_id {F : Type} [Field F] [NumberField F] (s s' : Fin 2 → F) (x : GF F) :
    algebraMap F (Af F) (s 0 * s' 1 - s 1 * s' 0) * (Matrix.GeneralLinearGroup.det x : Af F) =
      rowF s x 0 * rowF s' x 1 - rowF s x 1 * rowF s' x 0 := by
  rw [rowF_apply, rowF_apply, rowF_apply, rowF_apply, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
  simp only [map_sub, map_mul]
  ring

end UpperTheory.Esk.HeightProductFormula

namespace UpperTheory.Esk

open HeightProductFormula in
theorem dProd : AMem → AMono → ARow → DProd := by
  intro hM hMo hR F _ _ _ c _ χ s s' hΔ x
  obtain ⟨hpos, hmul, -, hprod⟩ := UpperTheory.V.Sd.Hm.absf F
  have hs : s ≠ 0 := fun h => hΔ (by simp [h])
  have hs' : s' ≠ 0 := fun h => hΔ (by simp [h])
  obtain ⟨t, k, hk, ht⟩ := (hR F s x).1 hs
  obtain ⟨t', k', hk', ht'⟩ := (hR F s' x).1 hs'
  have hn : nF s x = absF t := (hR F s x).2 t k hk ht
  have hn' : nF s' x = absF t' := (hR F s' x).2 t' k' hk' ht'
  obtain ⟨hK, hO, -⟩ := hM F
  have hle : ∀ (g : GF F), g ∈ K0 F → ∀ i j (w : Pl F), Valued.v (pLoc F w (g.val i j)) ≤ 1 :=
    fun g hg i j w => (hO _).1 (((hK g).1 hg).1 i j) w
  set Δ := s 0 * s' 1 - s 1 * s' 0 with hΔd
  set U1 : (Af F)ˣ := ratU F (Units.mk0 Δ hΔ) * Matrix.GeneralLinearGroup.det x
  have key : absF U1 ≤ absF (t * t') := by
    refine hMo F _ _ fun w => ?_
    have e : (U1 : Af F) = (t * t' : (Af F)ˣ) * (k.val 1 0 * k'.val 1 1 - k.val 1 1 * k'.val 1 0) := by
      change algebraMap F (Af F) Δ * (Matrix.GeneralLinearGroup.det x : Af F) = _
      rw [det_id, ht, ht, ht', ht', Units.val_mul]
      ring
    rw [e, map_mul, map_mul]
    have h1 : Valued.v (pLoc F w (k.val 1 0 * k'.val 1 1 - k.val 1 1 * k'.val 1 0)) ≤ 1 := by
      rw [map_sub, map_mul, map_mul]
      refine (Valuation.map_sub _ _ _).trans (max_le ?_ ?_)
      · rw [map_mul]; exact mul_le_one' (hle k hk 1 0 w) (hle k' hk' 1 1 w)
      · rw [map_mul]; exact mul_le_one' (hle k hk 1 1 w) (hle k' hk' 1 0 w)
    calc _ ≤ Valued.v (pLoc F w ((t * t' : (Af F)ˣ) : Af F)) * 1 := mul_le_mul_right h1 _
      _ = _ := mul_one _
  have hU1 : absF U1 = absF (ratU F (Units.mk0 Δ hΔ)) * absF (Matrix.GeneralLinearGroup.det x) := hmul _ _
  have hP := hprod (Units.mk0 Δ hΔ)
  change (∏ v, |reAt v Δ|) * absF (ratU F (Units.mk0 Δ hΔ)) = 1 at hP
  simp only [reAt_eq] at hP
  change absF (Matrix.GeneralLinearGroup.det x) / nF s x ^ 2 * (absF (Matrix.GeneralLinearGroup.det x) / nF s' x ^ 2) ≤
    ∏ v, sg v Δ ^ 2
  rw [hn, hn']
  have hsq : ∏ v, sg v Δ ^ 2 = (∏ v, |sg v Δ|) ^ 2 := by
    rw [← Finset.prod_pow]; exact Finset.prod_congr rfl fun v _ => (sq_abs _).symm
  rw [hsq]
  set P := ∏ v, |sg v Δ|
  set R := absF (ratU F (Units.mk0 Δ hΔ))
  set A := absF (Matrix.GeneralLinearGroup.det x)
  have hA := hpos (Matrix.GeneralLinearGroup.det x)
  have hT := hpos t
  have hT' := hpos t'
  have hRp := hpos (ratU F (Units.mk0 Δ hΔ))
  have hPp : 0 ≤ P := Finset.prod_nonneg fun v _ => abs_nonneg _
  rw [hU1, hmul t t'] at key
  have hA2 : A ≤ absF t * absF t' * P := by
    have : A = P * (R * A) := by rw [← mul_assoc, hP, one_mul]
    rw [this, mul_comm (absF t * absF t') P]
    exact mul_le_mul_of_nonneg_left key hPp
  rw [div_mul_div_comm, div_le_iff₀ (by positivity), ← sq, ← mul_pow, ← mul_pow]
  exact pow_le_pow_left₀ hA.le (by linarith) 2

end UpperTheory.Esk
end
end

section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk.BoxMapsToLemmas

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

lemma place_eq (v : InfinitePlace F) (t : F) : v t = |sg v t| := by
  rw [← Real.norm_eq_abs]
  exact (InfinitePlace.norm_embedding_of_isReal _ t).symm

lemma injOn (R : ℝ) : Set.InjOn (fun t : F => fun v : InfinitePlace F => ⌊sg v t⌋)
    {t : F | IsIntegral ℤ t ∧ ∀ v : InfinitePlace F, v t ≤ R} := by
  intro t ht t' ht' h
  by_contra hne
  let a : 𝓞 F := ⟨t - t', ht.1.sub ht'.1⟩
  have ha : a ≠ 0 := by
    intro h0
    apply hne
    have h1 : ((a : 𝓞 F) : F) = 0 := by rw [h0]; rfl
    exact sub_eq_zero.1 h1
  have hlt : ∀ v : InfinitePlace F, v (a : F) < 1 := by
    intro v
    have hv := congrFun h v
    simp only at hv
    rw [place_eq]
    show |sg v (t - t')| < 1
    rw [map_sub]
    exact Int.abs_sub_lt_one_of_floor_eq_floor hv
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  exact absurd (InfinitePlace.one_le_of_lt_one (w := w) ha fun z _ => hlt z) (not_le.2 (hlt w))

open Classical in
lemma mapsTo (R : ℝ) : Set.MapsTo (fun t : F => fun v : InfinitePlace F => ⌊sg v t⌋)
    {t : F | IsIntegral ℤ t ∧ ∀ v : InfinitePlace F, v t ≤ R}
    ((Fintype.piFinset fun _ : InfinitePlace F => Finset.Icc (-(⌈R⌉₊ : ℤ)) ⌈R⌉₊ : Finset _) : Set _) := by
  intro t ht
  simp only [Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_Icc]
  intro v
  have h1 := ht.2 v
  rw [place_eq, abs_le] at h1
  have hc : R ≤ (⌈R⌉₊ : ℝ) := Nat.le_ceil R
  constructor
  · rw [Int.le_floor]
    push_cast
    linarith [h1.1]
  · have h2 : ((⌊sg v t⌋ : ℤ) : ℝ) ≤ ((⌈R⌉₊ : ℤ) : ℝ) := by
      push_cast
      linarith [Int.floor_le (sg v t), h1.2]
    exact_mod_cast h2

end UpperTheory.Esk.BoxMapsToLemmas

open Classical in
theorem UpperTheory.Esk.dBox : UpperTheory.Esk.DBox := by
  intro F _ _ _
  refine ⟨5 ^ Fintype.card (InfinitePlace F), fun R hR => ?_⟩
  set d := Fintype.card (InfinitePlace F)
  set T := (Fintype.piFinset fun _ : InfinitePlace F => Finset.Icc (-(⌈R⌉₊ : ℤ)) ⌈R⌉₊)
  refine ⟨Set.Finite.of_injOn (BoxMapsToLemmas.mapsTo R) (BoxMapsToLemmas.injOn R) T.finite_toSet, ?_⟩
  have h1 := Set.ncard_le_ncard_of_injOn _ (BoxMapsToLemmas.mapsTo R) (BoxMapsToLemmas.injOn R) T.finite_toSet
  rw [Set.ncard_coe_finset] at h1
  have h2 : T.card = (2 * ⌈R⌉₊ + 1) ^ d := by
    simp only [T, Fintype.card_piFinset, Int.card_Icc, Finset.prod_const, Finset.card_univ]
    congr 1
    omega
  have h3 : ((2 * ⌈R⌉₊ + 1 : ℕ) : ℝ) ≤ 5 * max 1 R := by
    have := Nat.ceil_lt_add_one hR
    have hm1 : (1 : ℝ) ≤ max 1 R := le_max_left _ _
    have hmR : R ≤ max 1 R := le_max_right _ _
    push_cast
    linarith
  have h4 : (max 1 R) ^ d ≤ 1 + R ^ d := by
    rcases le_total R 1 with h | h
    · rw [max_eq_left h, one_pow]
      linarith [pow_nonneg hR d]
    · rw [max_eq_right h]
      linarith [zero_le_one' ℝ]
  calc (_ : ℝ) ≤ (T.card : ℝ) := by exact_mod_cast h1
    _ = ((2 * ⌈R⌉₊ + 1 : ℕ) : ℝ) ^ d := by rw [h2]; push_cast; ring
    _ ≤ (5 * max 1 R) ^ d := pow_le_pow_left₀ (by positivity) h3 _
    _ = 5 ^ d * (max 1 R) ^ d := mul_pow _ _ _
    _ ≤ 5 ^ d * (1 + R ^ d) := mul_le_mul_of_nonneg_left h4 (by positivity)
end
end

section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk.CentralScalarMap

theorem central_of_map {K L : Type} [Field K] [Field L] (f : K →+* L) {g : GL (Fin 2) K}
    (h : Matrix.GeneralLinearGroup.map f g ∈ Subgroup.center (GL (Fin 2) L)) :
    g ∈ Subgroup.center (GL (Fin 2) K) := by
  rw [Subgroup.mem_center_iff] at h ⊢
  intro δ
  have e := h (Matrix.GeneralLinearGroup.map f δ)
  rw [← map_mul, ← map_mul] at e
  apply Units.ext
  exact Matrix.map_injective f.injective (congrArg Units.val e)

theorem map_scalar_center {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (z : Rˣ) :
    Matrix.GeneralLinearGroup.map f (Matrix.GeneralLinearGroup.scalar (Fin 2) z) ∈ Subgroup.center (GL (Fin 2) S) := by
  rw [Subgroup.mem_center_iff]
  intro g
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

end UpperTheory.Esk.CentralScalarMap

namespace UpperTheory.Esk

open CentralScalarMap in
theorem dTwo : AMem → DTwo := by
  intro hA F _ _ _ c χ ⟨u, hu, hu2⟩ ω S hS hfin
  obtain ⟨-, -, -, hH, -⟩ := hA F
  have hc0 : Nat.card S ≠ 0 := Nat.card_pos.ne'
  refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd hc0 (p := 2) ?_⟩
  intro p hp hd
  by_contra hne
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨γ, hγ⟩ := exists_prime_orderOf_dvd_card' (G := S) p hd
  set g : GL (Fin 2) F := (γ : PG F).out with hg
  have hmk : ((g : PG F)) = (γ : PG F) := QuotientGroup.out_eq' _
  have hgp : g ^ p ∈ Subgroup.center (GL (Fin 2) F) := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hmk, ← Subgroup.coe_pow, ← hγ, pow_orderOf_eq_one,
      Subgroup.coe_one]
  have hst : (γ : PG F) • ω = ω := hS γ.2
  obtain ⟨x, hx⟩ : ∃ x : GF F, ((x : GF F ⧸ Hc c) : (mkDat c χ).Om) = ω := QuotientGroup.mk_surjective ω
  have h1 : ((jF F g * x : GF F) : GF F ⧸ Hc c) = (x : GF F ⧸ Hc c) := by
    rw [← hmk, ← hx] at hst
    exact hst
  have h2 : x⁻¹ * (jF F g * x) ∈ Hc c := QuotientGroup.eq.1 h1.symm
  obtain ⟨k, hk, z, hkz⟩ := (hH c _).1 h2
  obtain ⟨z0, hz0⟩ := jF_center hgp
  have hzc : ∀ z, zc F z ∈ Subgroup.center (GF F) := zc_center
  have hyp : (x⁻¹ * (jF F g * x)) ^ p = zc F z0 := by
    have := conj_pow (a := x⁻¹) (b := jF F g) (i := p)
    rw [inv_inv] at this
    rw [← mul_assoc, this, ← map_pow, hz0, Subgroup.mem_center_iff.1 (hzc _) x⁻¹, inv_mul_cancel_right]
  have hkp : k ^ p = zc F (z0 * (z ^ p)⁻¹) := by
    have e1 : (k * zc F z) ^ p = k ^ p * zc F z ^ p :=
      Commute.mul_pow (Subgroup.mem_center_iff.1 (hzc z) k) p
    rw [map_mul, map_inv, map_pow, ← hyp, hkz, e1, mul_inv_cancel_right]
  set P := Matrix.GeneralLinearGroup.map (n := Fin 2) (pLoc F u) with hP
  have hPz : ∀ z, P (zc F z) ∈ Subgroup.center _ := fun z => map_scalar_center _ z
  have hku : P k ∈ K1 u (c u) := Subgroup.mem_iInf.1 hk u
  have hkc := locTwo F u (c u) hu hu2 _ hku p (hp.odd_of_ne_two hne) (by rw [← map_pow, hkp]; exact hPz _)
  have hc2 : P (x⁻¹ * (jF F g * x)) ∈ Subgroup.center _ := by
    rw [hkz, map_mul]; exact mul_mem hkc (hPz z)
  have hc3 : P (jF F g) ∈ Subgroup.center _ := by
    have := (Subgroup.normal_of_characteristic _).conj_mem _ hc2 (P x)
    simpa [mul_assoc] using this
  have hcen : g ∈ Subgroup.center (GL (Fin 2) F) :=
    central_of_map ((pLoc F u).comp (algebraMap F (Af F))) hc3
  have h1' : (γ : PG F) = 1 := by
    rw [← hmk]; exact (QuotientGroup.eq_one_iff _).2 hcen
  have : γ = 1 := Subtype.ext h1'
  rw [this, orderOf_one] at hγ
  exact hp.one_lt.ne hγ

end UpperTheory.Esk
end
end

section
namespace UpperTheory.Esk

theorem dAx : DAx :=
  have m := aMem
  have iw := aIw m
  have row := aRow m iw
  have orb := aOrb m
  have bnf := aBnfH (aBnf m iw aCls (aAdd m)) orb
  have ht := dHt row
  have mul := dMul m iw aMono row
  dAx_of (dCount m bnf orb) ht mul (dProd m aMono row) (dMink m aMono row bnf aMink ht mul)
    (dNormal m bnf orb aUnit aTrans ht mul) (dCnt (dScale m aCls aUnit) dBox dEntry)

theorem dTwo' : DTwo := dTwo aMem

theorem dGood' : DGood := dGood aMem

end UpperTheory.Esk
end
