import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.WKTensFockGenSub
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.TotalDegreeBindLeOfLinear
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.AlgebraMapInvFf
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.MemHighestWeightSubIff
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.LinearAlgebra.Trace
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.ProjectionCommutesDerivedAction
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.EquivSigLamOfIsDS

section
noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.TRGap

variable {n : ℕ} {ε : Fin n → Bool}

theorem involute_physFock {x : Fock n} (hx : x ∈ physFock ε) : CliffordAlgebra.involute x ∈ physFock ε := by
  simp only [physFock, Submodule.mem_iInf, LinearMap.mem_ker] at hx ⊢
  intro i a hia
  have h := LinearMap.congr_fun (fock_inv_cm i a) x
  simp only [Module.End.mul_apply, AlgHom.toLinearMap_apply, LinearMap.neg_apply, hx i a hia, map_zero] at h
  exact neg_eq_zero.mp h.symm

theorem involute_ff_mapsTo (k : Matrix (Fin n) (Fin n) ℂ) :
    ∀ x ∈ physFock ε, (CliffordAlgebra.involute.toLinearMap ∘ₗ (ff ε k).toLinearMap) x ∈ physFock ε := by
  intro x hx
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply]
  exact involute_physFock (ff_physFock k hx)

theorem physWedge_mem (S : LfIdx ε) : fockBasis n S.1 ∈ physFock ε := by
  simp only [physFock, Submodule.mem_iInf, LinearMap.mem_ker]
  intro i a hia
  have hm : finProdFinEquiv (i, a) ∉ S.1 := by
    intro h
    have := S.2 h
    rw [lfPhysModes, Finset.mem_filter, Equiv.symm_apply_apply] at this
    exact hia this.2
  exact lf_cm_basis_of_not_mem (x := (i, a)) hm

theorem physWedge_li :
    LinearIndependent ℂ (fun S : LfIdx ε => (⟨fockBasis n S.1, physWedge_mem S⟩ : physFock ε)) := by
  apply LinearIndependent.of_comp (physFock ε).subtype
  exact (fockBasis n).linearIndependent.comp _ Subtype.val_injective

theorem phys_eq_sum (y : physFock ε) :
    (y : Fock n) = ∑ S : LfIdx ε, (fockBasis n).repr y S.1 • fockBasis n S.1 := by
  calc (y : Fock n) = ∑ T, (fockBasis n).repr y T • fockBasis n T := ((fockBasis n).sum_repr _).symm
    _ = ∑ T ∈ univ.filter (fun T => T ⊆ lfPhysModes ε), (fockBasis n).repr y T • fockBasis n T := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun T _ => ?_
        split_ifs with h
        · rfl
        · have h0 : (fockBasis n).repr y T = 0 := by
            by_contra h0
            exact h (gc_support_phys y.2 (by rwa [Module.Basis.coord_apply]))
          rw [h0, zero_smul]
    _ = ∑ S : LfIdx ε, (fockBasis n).repr y S.1 • fockBasis n S.1 :=
        Finset.sum_subtype _ (fun T => by simp) _

theorem physWedge_span :
    ⊤ ≤ Submodule.span ℂ (Set.range (fun S : LfIdx ε => (⟨fockBasis n S.1, physWedge_mem S⟩ : physFock ε))) := by
  intro y _
  have hy : y = ∑ S : LfIdx ε, (fockBasis n).repr y S.1 • (⟨fockBasis n S.1, physWedge_mem S⟩ : physFock ε) := by
    apply Subtype.ext
    conv_lhs => rw [phys_eq_sum y]
    rw [Submodule.coe_sum]
    rfl
  rw [hy]
  exact Submodule.sum_mem _ fun S _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨S, rfl⟩)

def physBasis (ε : Fin n → Bool) : Module.Basis (LfIdx ε) ℂ (physFock ε) :=
  Module.Basis.mk physWedge_li physWedge_span

theorem physBasis_coe (S : LfIdx ε) : (physBasis ε S : Fock n) = fockBasis n S.1 := by
  simp [physBasis]

theorem physBasis_repr (y : physFock ε) (S : LfIdx ε) :
    (physBasis ε).repr y S = (fockBasis n).repr y S.1 := by
  have : Finsupp.lapply S ∘ₗ (physBasis ε).repr.toLinearMap =
      Finsupp.lapply S.1 ∘ₗ (fockBasis n).repr.toLinearMap ∘ₗ (physFock ε).subtype := by
    refine (physBasis ε).ext fun T => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.repr_self, Finsupp.lapply_apply,
      Submodule.subtype_apply, physBasis_coe, Finsupp.single_apply, Subtype.ext_iff]
  exact LinearMap.congr_fun this y

theorem involute_ιMulti (p : ℕ) (v : Fin p → (Fin n × Fin n → ℂ)) :
    CliffordAlgebra.involute (ExteriorAlgebra.ιMulti ℂ p v) = ((-1 : ℂ) ^ p) • ExteriorAlgebra.ιMulti ℂ p v := by
  induction p with
  | zero => simp [ExteriorAlgebra.ιMulti_zero_apply]
  | succ p ih =>
    rw [ExteriorAlgebra.ιMulti_succ_apply, map_mul, ih, CliffordAlgebra.involute_ι, mul_smul_comm, neg_mul,
      pow_succ, mul_neg_one, neg_smul, smul_neg]

theorem involute_basis (S : Finset (Fin (n * n))) :
    CliffordAlgebra.involute (fockBasis n S) = ((-1 : ℂ) ^ S.card) • fockBasis n S := by
  rw [fockBasis_eq, involute_ιMulti]

theorem strPhys_eq_trace (k : Matrix (Fin n) (Fin n) ℂ) :
    strPhys ε k = LinearMap.trace ℂ (physFock ε)
      ((CliffordAlgebra.involute.toLinearMap ∘ₗ (ff ε k).toLinearMap).restrict (involute_ff_mapsTo k)) := by
  have hterm : ∀ S : LfIdx ε, (physBasis ε).repr
      (((CliffordAlgebra.involute.toLinearMap ∘ₗ (ff ε k).toLinearMap).restrict (involute_ff_mapsTo k))
        (physBasis ε S)) S = (-1 : ℂ) ^ S.1.card * ffMat ε k S.1 S.1 := by
    intro S
    rw [physBasis_repr, LinearMap.coe_restrict_apply, physBasis_coe]
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply]
    rw [← ff_involute, involute_basis, map_smul, map_smul, Finsupp.smul_apply, smul_eq_mul, ffMat,
      LinearMap.toMatrix_apply, AlgHom.toLinearMap_apply]
  rw [strPhys, LinearMap.trace_eq_matrix_trace ℂ (physBasis ε), Matrix.trace]
  simp only [Matrix.diag, LinearMap.toMatrix_apply, hterm]
  exact Finset.sum_subtype _ (fun S => by simp [IsPhysSet, Finset.subset_iff, lfPhysModes, IsPhys]) _

end ReciprocityTheory.ChartRestriction.DS.TRGap
end
end

section
noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.TRGap

variable {n : ℕ} {ε : Fin n → Bool}

theorem det_one_sub_eq_sum_minors {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) :
    (1 - A).det =
      ∑ s : Finset ι, (-1 : ℂ) ^ s.card * (A.submatrix (Subtype.val : s → ι) Subtype.val).det := by
  have e : Matrix.det (1 - A) =
      Matrix.detRowAlternating ((fun i => (-A) i) + (fun i => (1 : Matrix ι ι ℂ) i)) := by
    refine congrArg Matrix.detRowAlternating ?_
    funext i j
    simp [sub_eq_neg_add]
  rw [e, AlternatingMap.map_add_univ]
  refine Finset.sum_congr rfl fun s _ => ?_
  refine (Matrix.det_piecewise_one_eq_submatrix_det (-A) s).trans ?_
  have hn : (-A).submatrix (Subtype.val : s → ι) (Subtype.val : s → ι) =
      -(A.submatrix (Subtype.val : s → ι) (Subtype.val : s → ι)) := by
    ext i j
    simp
  rw [hn, Matrix.det_neg, Fintype.card_coe]

theorem fock_repr_ιMulti (S : Finset (Fin (n * n))) (v : Fin S.card → (Fin n × Fin n → ℂ)) :
    (fockBasis n).repr (ExteriorAlgebra.ιMulti ℂ S.card v) S =
      (Matrix.of fun i j => v i (finProdFinEquiv.symm (S.orderEmbOfFin rfl j))).det := by
  have h1 : (fockBasis n).repr (ExteriorAlgebra.ιMulti ℂ S.card v) S =
      (((Pi.basisFun ℂ (Fin n × Fin n)).reindex finProdFinEquiv).exteriorPower S.card).repr
        (exteriorPower.ιMulti ℂ S.card v) (Set.powersetCard.ofCard (rfl : S.card = S.card)) := by
    rw [fockBasis, Module.Basis.ExteriorAlgebra, Module.Basis.repr_reindex_apply,
      Set.powersetCard.prodEquiv_symm_apply]
    exact DirectSum.IsInternal.collectedBasis_repr_of_mem _ _ (exteriorPower.ιMulti ℂ S.card v).2
  rw [h1, exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti]
  congr 1

theorem ffMat_diag_det (k : Matrix (Fin n) (Fin n) ℂ) (S : Finset (Fin (n * n))) :
    ffMat ε k S S = (Matrix.of fun i j : Fin S.card =>
      adMat ε k (finProdFinEquiv.symm (S.orderEmbOfFin rfl i))
        (finProdFinEquiv.symm (S.orderEmbOfFin rfl j))).det := by
  rw [ffMat, LinearMap.toMatrix_apply, AlgHom.toLinearMap_apply, fockBasis_eq, ff,
    ExteriorAlgebra.map_apply_ιMulti, fock_repr_ιMulti, ← Matrix.det_transpose]
  congr 1
  ext i j
  simp [adPhys, Matrix.mulVec, dotProduct, Pi.single_apply]

def physEmb (ε : Fin n → Bool) : {x : Fin n × Fin n // IsPhys ε x} ↪ Fin (n * n) :=
  ⟨fun x => finProdFinEquiv x.1, fun _ _ h => Subtype.ext (finProdFinEquiv.injective h)⟩

theorem ffMat_map_physEmb (k : Matrix (Fin n) (Fin n) ℂ) (s : Finset {x : Fin n × Fin n // IsPhys ε x}) :
    ffMat ε k (s.map (physEmb ε)) (s.map (physEmb ε)) =
      ((Matrix.of fun x y : {x : Fin n × Fin n // IsPhys ε x} => k x.1.1 y.1.1 * star (k x.1.2 y.1.2)).submatrix
        (Subtype.val : s → _) Subtype.val).det := by
  classical
  set S := s.map (physEmb ε) with hS
  rw [ffMat_diag_det]
  have hmem : ∀ i, ∃ x ∈ s, physEmb ε x = S.orderEmbOfFin rfl i :=
    fun i => Finset.mem_map.1 (S.orderEmbOfFin_mem rfl i)
  let e : Fin S.card → s := fun i => ⟨(hmem i).choose, (hmem i).choose_spec.1⟩
  have he : ∀ i, (((e i : {x : Fin n × Fin n // IsPhys ε x}) : Fin n × Fin n)) =
      finProdFinEquiv.symm (S.orderEmbOfFin rfl i) := by
    intro i
    rw [← (hmem i).choose_spec.2]
    exact (finProdFinEquiv.symm_apply_apply _).symm
  have hp : ∀ i, IsPhys ε (finProdFinEquiv.symm (S.orderEmbOfFin rfl i)) :=
    fun i => he i ▸ (e i : {x : Fin n × Fin n // IsPhys ε x}).2
  have hinj : Function.Injective e := by
    intro i j hij
    have h1 := he i
    rw [hij, he j] at h1
    exact (S.orderEmbOfFin rfl).injective (finProdFinEquiv.symm.injective h1.symm)
  have hcard : Fintype.card (Fin S.card) = Fintype.card s := by simp [S]
  rw [← Matrix.det_submatrix_equiv_self
    (Equiv.ofBijective e ((Fintype.bijective_iff_injective_and_card e).2 ⟨hinj, hcard⟩))]
  congr 1
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.of_apply, Equiv.ofBijective_apply]
  rw [he i, he j]
  simp only [adMat, if_pos (hp i), if_pos (hp j)]

theorem strPhys_eq_physDet (k : Matrix (Fin n) (Fin n) ℂ) : strPhys ε k = physDet ε k := by
  classical
  have h1 : physDet ε k = (1 - Matrix.of fun x y : {x : Fin n × Fin n // IsPhys ε x} =>
      k x.1.1 y.1.1 * star (k x.1.2 y.1.2)).det := by
    rw [physDet]
    congr 1
  rw [h1, det_one_sub_eq_sum_minors, strPhys]
  symm
  refine Finset.sum_bij (fun s _ => s.map (physEmb ε)) ?_ ?_ ?_ ?_
  · intro s _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, IsPhysSet]
    intro m hm
    obtain ⟨x, _, rfl⟩ := Finset.mem_map.1 hm
    show IsPhys ε (finProdFinEquiv.symm (finProdFinEquiv x.1))
    rw [Equiv.symm_apply_apply]
    exact x.2
  · intro s _ t _ h
    exact Finset.map_injective _ h
  · intro S hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
    refine ⟨Finset.univ.filter (fun x => physEmb ε x ∈ S), Finset.mem_univ _, ?_⟩
    ext m
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hm
      refine ⟨⟨finProdFinEquiv.symm m, hS m hm⟩, ?_, finProdFinEquiv.apply_symm_apply m⟩
      show finProdFinEquiv (finProdFinEquiv.symm m) ∈ S
      rw [Equiv.apply_symm_apply]
      exact hm
  · intro s _
    rw [ffMat_map_physEmb, Finset.card_map]

end ReciprocityTheory.ChartRestriction.DS.TRGap
end
end

section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.TRGap

section LA

variable {Y : Type*} [AddCommGroup Y] [Module ℂ Y] [FiniteDimensional ℂ Y]

theorem trace_eq_trace_restrict_of_range_le (f : Y →ₗ[ℂ] Y) (Y0 : Submodule ℂ Y)
    (h : LinearMap.range f ≤ Y0) :
    LinearMap.trace ℂ Y f =
      LinearMap.trace ℂ Y0 (f.restrict (fun x _ => h (LinearMap.mem_range_self f x))) := by
  have hm : ∀ x, f x ∈ Y0 := fun x => h (LinearMap.mem_range_self f x)
  calc LinearMap.trace ℂ Y f = LinearMap.trace ℂ Y (Y0.subtype ∘ₗ LinearMap.codRestrict Y0 f hm) := by
        rw [LinearMap.subtype_comp_codRestrict]
    _ = LinearMap.trace ℂ Y0 (LinearMap.codRestrict Y0 f hm ∘ₗ Y0.subtype) :=
        LinearMap.trace_comp_comm' _ _
    _ = _ := by
        congr 1

theorem trace_eq_add_of_isCompl (f : Y →ₗ[ℂ] Y) {K R : Submodule ℂ Y} (hKR : IsCompl K R)
    (hK : ∀ x ∈ K, f x ∈ K) (hR : ∀ x ∈ R, f x ∈ R) :
    LinearMap.trace ℂ Y f = LinearMap.trace ℂ K (f.restrict hK) + LinearMap.trace ℂ R (f.restrict hR) := by
  have hrK : LinearMap.range (f ∘ₗ K.projection R hKR) ≤ K := by
    rintro _ ⟨x, rfl⟩
    exact hK _ (Submodule.projection_apply_mem _ _)
  have hrR : LinearMap.range (f ∘ₗ R.projection K hKR.symm) ≤ R := by
    rintro _ ⟨x, rfl⟩
    exact hR _ (Submodule.projection_apply_mem _ _)
  have h1 : LinearMap.trace ℂ Y f = LinearMap.trace ℂ Y (f ∘ₗ K.projection R hKR) +
      LinearMap.trace ℂ Y (f ∘ₗ R.projection K hKR.symm) := by
    rw [← map_add, ← LinearMap.comp_add, Submodule.projection_add_projection_eq_id, LinearMap.comp_id]
  rw [h1, trace_eq_trace_restrict_of_range_le _ K hrK, trace_eq_trace_restrict_of_range_le _ R hrR]
  congr 2
  · ext x
    simp
  · ext x
    simp

end LA

section S4

variable {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y]

theorem str_eq_str_ker (Dl Γ B : Y →ₗ[ℂ] Y) (hD : ∀ x y, inner ℂ (Dl x) y = inner ℂ x (Dl y))
    (hΓD : ∀ x, Γ (Dl x) = -Dl (Γ x)) (hBD : ∀ x, B (Dl x) = Dl (B x)) :
    ∃ hk : ∀ x ∈ LinearMap.ker Dl, (Γ ∘ₗ B) x ∈ LinearMap.ker Dl,
      LinearMap.trace ℂ Y (Γ ∘ₗ B) = LinearMap.trace ℂ (LinearMap.ker Dl) ((Γ ∘ₗ B).restrict hk) := by
  have hDΓ : ∀ y, Dl (Γ y) = -Γ (Dl y) := fun y => by rw [hΓD, neg_neg]
  have hk : ∀ x ∈ LinearMap.ker Dl, (Γ ∘ₗ B) x ∈ LinearMap.ker Dl := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    rw [LinearMap.comp_apply, hDΓ, ← hBD, hx, map_zero, map_zero, neg_zero]
  refine ⟨hk, ?_⟩
  have hsym : Dl.IsSymmetric := hD
  have hkr : IsCompl (LinearMap.ker Dl) (LinearMap.range Dl) := by
    have := (Submodule.isCompl_orthogonal (LinearMap.range Dl)).symm
    rwa [hsym.orthogonal_range] at this
  have hV : ∀ x ∈ LinearMap.range Dl, (Γ ∘ₗ B) x ∈ LinearMap.range Dl := by
    rintro _ ⟨y, rfl⟩
    refine ⟨-Γ (B y), ?_⟩
    rw [map_neg, hDΓ, neg_neg, LinearMap.comp_apply, hBD]
  rw [trace_eq_add_of_isCompl _ hkr hk hV]
  suffices h0 : LinearMap.trace ℂ (LinearMap.range Dl) ((Γ ∘ₗ B).restrict hV) = 0 by
    rw [h0, add_zero]
  have hDV : ∀ x ∈ LinearMap.range Dl, Dl x ∈ LinearMap.range Dl := fun x _ => LinearMap.mem_range_self Dl x
  have hΓV : ∀ x ∈ LinearMap.range Dl, Γ x ∈ LinearMap.range Dl := by
    rintro _ ⟨y, rfl⟩
    exact ⟨-Γ y, by rw [map_neg, hDΓ, neg_neg]⟩
  have hBV : ∀ x ∈ LinearMap.range Dl, B x ∈ LinearMap.range Dl := by
    rintro _ ⟨y, rfl⟩
    exact ⟨B y, (hBD y).symm⟩
  have hinj : Function.Injective (Dl.restrict hDV) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro v hv
    have hv' : (v : Y) ∈ LinearMap.ker Dl := by
      rw [LinearMap.mem_ker]
      have := congrArg Subtype.val (LinearMap.mem_ker.1 hv)
      simpa using this
    exact Subtype.ext (Submodule.disjoint_def.1 hkr.disjoint _ hv' v.2)
  set e := LinearEquiv.ofInjectiveEndo (Dl.restrict hDV) hinj
  have hsplit : (Γ ∘ₗ B).restrict hV = Γ.restrict hΓV ∘ₗ B.restrict hBV := by
    ext v
    rfl
  have hconj : e.conj ((Γ ∘ₗ B).restrict hV) = -((Γ ∘ₗ B).restrict hV) := by
    ext v
    obtain ⟨w, rfl⟩ : ∃ w, v = e w := ⟨e.symm v, (e.apply_symm_apply v).symm⟩
    simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      LinearMap.neg_apply]
    show ((Dl.restrict hDV) ((Γ ∘ₗ B).restrict hV w) : Y) = -(((Γ ∘ₗ B).restrict hV (Dl.restrict hDV w)) : Y)
    simp only [LinearMap.restrict_apply, LinearMap.comp_apply]
    rw [hDΓ, ← hBD]
  have ht := LinearMap.trace_conj' ((Γ ∘ₗ B).restrict hV) e
  rw [hconj, map_neg] at ht
  linear_combination -ht / 2

end S4

end ReciprocityTheory.ChartRestriction.DS.TRGap
end
end

section
noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.TRGap

variable {n : ℕ} {ε : Fin n → Bool}

section Supp

variable {N : Type*} [AddCommGroup N] [Module ℂ N]

theorem tco_physSub_zero {y : TensorProduct ℂ N (Fock n)} (hy : y ∈ physicalSubspace ε) {s : Finset (Fin (n * n))}
    {m : Fin (n * n)} (hm : m ∈ s) (hnp : ¬IsPhys ε (finProdFinEquiv.symm m)) :
    tcoef ((fockBasis n).coord s) y = 0 := by
  set x := finProdFinEquiv.symm m with hxdef
  have h0 : cmT (N := N) x.1 x.2 y = 0 := (mem_physicalSubspace_iff ε y).1 hy x.1 x.2 hnp
  have h1 : tcoef ((fockBasis n).coord s) (cpT (N := N) x.1 x.2 (cmT x.1 x.2 y)) = 0 := by
    rw [h0, map_zero, map_zero]
  change tcoef ((fockBasis n).coord s) (LinearMap.lTensor N (cpFock x.1 x.2)
    (LinearMap.lTensor N (cmFock x.1 x.2) y)) = 0 at h1
  rw [tcoef_lTensor, tcoef_lTensor, tcoef_eq_sum] at h1
  rw [Finset.sum_eq_single s] at h1
  · have hxs : finProdFinEquiv x ∈ s := by rw [hxdef, Equiv.apply_symm_apply]; exact hm
    simpa [lf_num_basis, hxs] using h1
  · intro S _ hS
    simp only [LinearMap.coe_comp, Function.comp_apply, lf_num_basis]
    split_ifs
    · simp [Module.Basis.coord_apply, Finsupp.single_apply, Ne.symm hS]
    · simp
  · simp

theorem tensFock_inf_physSub (L : Submodule ℂ N) :
    tensFock (n := n) L ⊓ physicalSubspace ε = LinearMap.range (TensorProduct.map L.subtype (physFock ε).subtype) := by
  apply le_antisymm
  · rintro y ⟨hyT, hyP⟩
    have hmem : ∀ s, tcoef ((fockBasis n).coord s) y ∈ L := fun s => tcoef_mem hyT _
    refine ⟨∑ S : LfIdx ε, (⟨tcoef ((fockBasis n).coord S.1) y, hmem S.1⟩ : L) ⊗ₜ
      (⟨fockBasis n S.1, physWedge_mem S⟩ : physFock ε), ?_⟩
    rw [map_sum]
    simp only [TensorProduct.map_tmul, Submodule.coe_subtype]
    symm
    calc y = ∑ s, tcoef ((fockBasis n).coord s) y ⊗ₜ fockBasis n s := tcoef_expand y
      _ = ∑ s ∈ univ.filter (fun s => s ⊆ lfPhysModes ε),
          tcoef ((fockBasis n).coord s) y ⊗ₜ fockBasis n s := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun s _ => ?_
        split_ifs with h
        · rfl
        · obtain ⟨m, hm, hmp⟩ := Finset.not_subset.1 h
          have hnp : ¬IsPhys ε (finProdFinEquiv.symm m) := by
            simpa [lfPhysModes, IsPhys] using hmp
          rw [tco_physSub_zero hyP hm hnp, TensorProduct.zero_tmul]
      _ = ∑ S : LfIdx ε, tcoef ((fockBasis n).coord S.1) y ⊗ₜ fockBasis n S.1 :=
        Finset.sum_subtype _ (fun s => by simp) _
  · rintro _ ⟨x, rfl⟩
    refine ⟨?_, ?_⟩
    · refine ⟨TensorProduct.map LinearMap.id (physFock ε).subtype x, ?_⟩
      rw [← LinearMap.comp_apply, ← TensorProduct.map_comp]
      rfl
    · show _ ∈ physicalSubspace ε
      rw [mem_physicalSubspace_iff]
      intro j b hjb
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul l f =>
        have hf := f.2
        simp only [physFock, Submodule.mem_iInf, LinearMap.mem_ker] at hf
        simp only [TensorProduct.map_tmul, cmT, LinearMap.id_apply, Submodule.coe_subtype, hf j b hjb,
          TensorProduct.tmul_zero]
      | add x x' hx hx' => rw [map_add, map_add, hx, hx', add_zero]

end Supp

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}

theorem str_tensFock_physSub (hD : IsDerivedOn ε σ D E) {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε)
    {L : Submodule ℂ D} [FiniteDimensional ℂ L] (hL : ∀ x ∈ L, sigD hD hk x ∈ L)
    (hY0 : ∀ y ∈ tensFock (n := n) L ⊓ physicalSubspace ε, (gradT ∘ₗ wK hD hk) y ∈ tensFock L ⊓ physicalSubspace ε) :
    LinearMap.trace ℂ ↥(tensFock (n := n) L ⊓ physicalSubspace (N := D) ε)
        ((gradT ∘ₗ wK hD hk).restrict hY0) =
      LinearMap.trace ℂ L ((sigD hD hk).restrict hL) * physDet ε k := by
  set Φ := TensorProduct.map L.subtype (physFock ε).subtype with hΦ
  have hinj : Function.Injective Φ :=
    TensorProduct.map_injective_of_flat_flat _ _ L.injective_subtype (physFock ε).injective_subtype
  let e : TensorProduct ℂ L (physFock ε) ≃ₗ[ℂ] ↥(tensFock (n := n) L ⊓ physicalSubspace (N := D) ε) :=
    (LinearEquiv.ofInjective Φ hinj).trans (LinearEquiv.ofEq _ _ (tensFock_inf_physSub L).symm)
  have he : ∀ x, ((e x : ↥(tensFock (n := n) L ⊓ physicalSubspace (N := D) ε)) : TensorProduct ℂ D (Fock n)) = Φ x :=
    fun x => rfl
  set sL := (sigD hD hk).restrict hL
  set fP := (CliffordAlgebra.involute.toLinearMap ∘ₗ (ff ε k).toLinearMap).restrict (involute_ff_mapsTo k)
  have hsq : ∀ x, (gradT ∘ₗ wK hD hk) (Φ x) = Φ (TensorProduct.map sL fP x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul l f => rfl
    | add x x' hx hx' => rw [map_add, map_add, hx, hx', map_add, map_add]
  have hconj : (gradT ∘ₗ wK hD hk).restrict hY0 = e.conj (TensorProduct.map sL fP) := by
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    rw [LinearEquiv.conj_apply_apply, he, LinearMap.restrict_apply]
    show (gradT ∘ₗ wK hD hk) (y : TensorProduct ℂ D (Fock n)) = _
    rw [← hsq, ← he, LinearEquiv.apply_symm_apply]
  have : FiniteDimensional ℂ (Fock n) := Module.Finite.of_basis (fockBasis n)
  rw [hconj, LinearMap.trace_conj', LinearMap.trace_tensorProduct', ← strPhys_eq_trace, strPhys_eq_physDet]

end ReciprocityTheory.ChartRestriction.DS.TRGap
end
end

section
noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.TRGap

variable {n : ℕ} {ε : Fin n → Bool}

section T

variable {N : Type*} [AddCommGroup N] [Module ℂ N]

theorem tensFock_map_stable {S : Submodule ℂ N} {F : Module.End ℂ N} (hF : ∀ v ∈ S, F v ∈ S)
    {y : TensorProduct ℂ N (Fock n)} (hy : y ∈ tensFock (n := n) S) :
    TensorProduct.map F LinearMap.id y ∈ tensFock S := by
  obtain ⟨x, rfl⟩ := hy
  refine ⟨TensorProduct.map (F.restrict hF) LinearMap.id x, ?_⟩
  rw [← LinearMap.comp_apply, ← TensorProduct.map_comp, ← LinearMap.comp_apply, ← TensorProduct.map_comp]
  rfl

theorem tensFock_lTensor_stable {S : Submodule ℂ N} (g : Module.End ℂ (Fock n))
    {y : TensorProduct ℂ N (Fock n)} (hy : y ∈ tensFock (n := n) S) :
    TensorProduct.map LinearMap.id g y ∈ tensFock S := by
  obtain ⟨x, rfl⟩ := hy
  refine ⟨TensorProduct.map LinearMap.id g x, ?_⟩
  rw [← LinearMap.comp_apply, ← TensorProduct.map_comp, ← LinearMap.comp_apply, ← TensorProduct.map_comp]
  rfl

theorem dD_tensFock {E : Fin n → Fin n → Module.End ℂ N} {S : Submodule ℂ N}
    (hS : ∀ a b, ∀ v ∈ S, E a b v ∈ S) {y : TensorProduct ℂ N (Fock n)} (hy : y ∈ tensFock (n := n) S) :
    (dOp ε (eT E) cpT + dOp' ε (eT E) cmT) y ∈ tensFock S := by
  simp only [dOp, dOp', LinearMap.add_apply, LinearMap.neg_apply, LinearMap.sum_apply, Module.End.mul_apply]
  refine Submodule.add_mem _ (Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun a _ => ?_)
    (Submodule.neg_mem _ (Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun a _ => ?_))
  · exact tensFock_map_stable (hS a i) (tensFock_lTensor_stable _ hy)
  · exact tensFock_map_stable (hS i a) (tensFock_lTensor_stable _ hy)

theorem dD_physSub (E : Fin n → Fin n → Module.End ℂ N) {y : TensorProduct ℂ N (Fock n)}
    (hy : y ∈ physicalSubspace (N := N) ε) : (dOp ε (eT E) cpT + dOp' ε (eT E) cmT) y ∈ physicalSubspace ε :=
  Submodule.add_mem _ ((physSub_stable ε E).2.2.1 y hy) ((physSub_stable ε E).2.2.2.1 y hy)

theorem casimir_eT (E : Fin n → Fin n → Module.End ℂ N) :
    casimir (eT (n := n) E) = TensorProduct.map (casimir E) LinearMap.id := by
  apply TensorProduct.ext'
  intro m f
  simp [casimir, eT, LinearMap.sum_apply, TensorProduct.sum_tmul]

theorem gradT_D (E : Fin n → Fin n → Module.End ℂ N) (y : TensorProduct ℂ N (Fock n)) :
    gradT ((dOp ε (eT E) cpT + dOp' ε (eT E) cmT) y) = -(dOp ε (eT E) cpT + dOp' ε (eT E) cmT) (gradT y) := by
  have h1 := LinearMap.congr_fun (gradT_props ε E).2.1 y
  have h2 := LinearMap.congr_fun (gradT_props ε E).2.2 y
  simp only [Module.End.mul_apply, LinearMap.neg_apply] at h1 h2
  rw [LinearMap.add_apply, map_add, h1, h2, LinearMap.add_apply, neg_add]

end T

section Y

variable {N : Type*} [AddCommGroup N] [Module ℂ N]

def Y0 (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ N) (V : Submodule ℂ N) (J : ℕ) :
    Submodule ℂ (TensorProduct ℂ N (Fock n)) :=
  tensFock (layer ε E V J) ⊓ physicalSubspace ε

def YY (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ N) (V : Submodule ℂ N) (J : ℕ) :
    Submodule ℂ (TensorProduct ℂ N (Fock n)) :=
  Y0 ε E V J ⊔ (Y0 ε E V J).map (dOp ε (eT E) cpT + dOp' ε (eT E) cmT)

variable {E : Fin n → Fin n → Module.End ℂ N} {V : Submodule ℂ N}

theorem map_eq_smul_of_tensFock {S : Submodule ℂ N} {F : Module.End ℂ N} {c : ℂ} (hF : ∀ v ∈ S, F v = c • v)
    {y : TensorProduct ℂ N (Fock n)} (hy : y ∈ tensFock (n := n) S) :
    TensorProduct.map F LinearMap.id y = c • y := by
  obtain ⟨x, rfl⟩ := hy
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul m f =>
    simp only [TensorProduct.map_tmul, Submodule.coe_subtype, LinearMap.id_apply, hF m m.2,
      TensorProduct.smul_tmul']
  | add x x' hx hx' => rw [map_add, map_add, hx, hx', smul_add]

theorem layer_le_generated_tensorFock (J : ℕ) : Y0 ε E V J ≤ tensFock (n := n) (genSub E V) ⊓ physicalSubspace ε :=
  inf_le_inf_right _ (tensorFock_mono (layer_le_genSub J))

theorem YY_le_genSub (J : ℕ) : YY ε E V J ≤ tensFock (n := n) (genSub E V) ⊓ physicalSubspace ε := by
  refine sup_le (layer_le_generated_tensorFock J) ?_
  rintro _ ⟨y, hy, rfl⟩
  have hy' := layer_le_generated_tensorFock J hy
  exact ⟨dD_tensFock (fun a b v hv => generatedSub_stable E V a b hv) hy'.1, dD_physSub E hy'.2⟩

theorem diracSquare_mem_layer (hE : IsGlRep E) (hVk : IsKStableSub ε E V) {c : ℂ} (hc : ∀ v ∈ genSub E V, casimir E v = c • v)
    (J : ℕ) {y : TensorProduct ℂ N (Fock n)} (hy : y ∈ Y0 ε E V J) :
    (dOp ε (eT E) cpT + dOp' ε (eT E) cmT) ((dOp ε (eT E) cpT + dOp' ε (eT E) cmT) y) ∈ Y0 ε E V J := by
  have hL := layer_kStable hE hVk J
  have hA : ∀ a b, ε a = ε b → ∀ x ∈ Y0 ε E V J, diagE ε (eT E) cpT cmT a b x ∈ Y0 ε E V J :=
    fun a b hab x hx => ⟨tensorFock_diagAction_stable ε hL hab hx.1, (physSub_stable ε E).2.1 a b x hx.2⟩
  have h2 := LinearMap.congr_fun (two_D_sq (eT_isGlRep hE) cpT_cmT_isCAR (eT_commutesCAR E) ε) y
  rw [LinearMap.smul_apply, Module.End.mul_apply] at h2
  have hcas : casimir (eT (n := n) E) y = c • y := by
    rw [casimir_eT]
    exact map_eq_smul_of_tensFock (fun v hv => hc v (layer_le_genSub J hv)) hy.1
  have hmem : (2 : ℂ) • (dOp ε (eT E) cpT + dOp' ε (eT E) cmT) ((dOp ε (eT E) cpT + dOp' ε (eT E) cmT) y) ∈
      Y0 ε E V J := by
    rw [h2]
    simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.neg_apply, LinearMap.smul_apply,
      LinearMap.sum_apply]
    rw [hcas]
    refine Submodule.sub_mem _ (Submodule.add_mem _ (Submodule.neg_mem _ (Submodule.smul_mem _ _ hy)) ?_)
      (Submodule.smul_mem _ _ (Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (hA a a rfl y hy)))
    simp only [casimirK, LinearMap.sum_apply, Module.End.mul_apply]
    exact Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b hb =>
      hA a b (Finset.mem_filter.1 hb).2.symm _ (hA b a (Finset.mem_filter.1 hb).2 y hy)
  have := Submodule.smul_mem _ (1 / 2 : ℂ) hmem
  rwa [smul_smul, show (1 / 2 : ℂ) * 2 = 1 by norm_num, one_smul] at this

theorem YY_D (hE : IsGlRep E) (hVk : IsKStableSub ε E V) {c : ℂ} (hc : ∀ v ∈ genSub E V, casimir E v = c • v)
    (J : ℕ) {y : TensorProduct ℂ N (Fock n)} (hy : y ∈ YY ε E V J) :
    (dOp ε (eT E) cpT + dOp' ε (eT E) cmT) y ∈ YY ε E V J := by
  obtain ⟨y0, hy0, y1, ⟨x, hx, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hy
  rw [map_add]
  exact Submodule.add_mem _ (Submodule.mem_sup_right ⟨y0, hy0, rfl⟩)
    (Submodule.mem_sup_left (diracSquare_mem_layer hE hVk hc J hx))

theorem YY_gradT (J : ℕ) {y : TensorProduct ℂ N (Fock n)} (hy : y ∈ YY ε E V J) : gradT y ∈ YY ε E V J := by
  obtain ⟨y0, hy0, y1, ⟨x, hx, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hy
  have hG : ∀ z ∈ Y0 ε E V J, gradT z ∈ Y0 ε E V J := fun z hz =>
    ⟨tensFock_lTensor_stable _ hz.1, (physSub_stable ε E).2.2.2.2 z hz.2⟩
  rw [map_add, gradT_D]
  exact Submodule.add_mem _ (Submodule.mem_sup_left (hG y0 hy0))
    (Submodule.mem_sup_right ⟨-gradT x, Submodule.neg_mem _ (hG x hx), by rw [map_neg]⟩)

theorem YY_fd (hVf : FiniteDimensional ℂ V) (J : ℕ) : FiniteDimensional ℂ (YY ε E V J) := by
  have h1 : FiniteDimensional ℂ (tensFock (n := n) (layer ε E V J)) :=
    tensorFock_finiteDimensional (finiteDimensional_layer hVf J)
  have h2 : FiniteDimensional ℂ (Y0 ε E V J) := Submodule.finiteDimensional_of_le inf_le_left
  unfold YY
  infer_instance

end Y

section W

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
  {V : Submodule ℂ D}

theorem sigD_layer (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (hVs : IsKStableSub ε E V)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (J : ℕ) {k : Matrix (Fin n) (Fin n) ℂ}
    (hk : k ∈ Kset ε) {x : D} (hx : x ∈ layer ε E V J) : sigD hD hk x ∈ layer ε E V J := by
  obtain ⟨y, hy, hyx⟩ := layer_k_stable hσ hD hVs hVK J k hk x hx
  have : sigD hD hk x = y := Subtype.ext hyx.symm
  rw [this]
  exact hy

theorem wK_tensFock (hD : IsDerivedOn ε σ D E) {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε)
    {S : Submodule ℂ D} (hS : ∀ x ∈ S, sigD hD hk x ∈ S) {y : TensorProduct ℂ D (Fock n)}
    (hy : y ∈ tensFock (n := n) S) : wK hD hk y ∈ tensFock S := by
  obtain ⟨x, rfl⟩ := hy
  refine ⟨TensorProduct.map ((sigD hD hk).restrict hS) (ff ε k).toLinearMap x, ?_⟩
  rw [← LinearMap.comp_apply, ← TensorProduct.map_comp]
  show _ = (TensorProduct.map (sigD hD hk) (ff ε k).toLinearMap ∘ₗ
    TensorProduct.map S.subtype LinearMap.id) x
  rw [← TensorProduct.map_comp]
  rfl

theorem wK_D (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) {k : Matrix (Fin n) (Fin n) ℂ}
    (hk : k ∈ Kset ε) (x : TensorProduct ℂ D (Fock n)) :
    wK hD hk ((dOp ε (eT E) cpT + dOp' ε (eT E) cmT) x) =
      (dOp ε (eT E) cpT + dOp' ε (eT E) cmT) (wK hD hk x) := by
  have h1 := LinearMap.congr_fun (wK_dOp hσ hD hk) x
  have h2 := LinearMap.congr_fun (wK_dOp' hσ hD hk) x
  simp only [Module.End.mul_apply] at h1 h2
  rw [LinearMap.add_apply, map_add, h1, h2, LinearMap.add_apply]

theorem compactAction_mem_layer (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (hVs : IsKStableSub ε E V)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (J : ℕ) {k : Matrix (Fin n) (Fin n) ℂ}
    (hk : k ∈ Kset ε) {y : TensorProduct ℂ D (Fock n)} (hy : y ∈ Y0 ε E V J) : wK hD hk y ∈ Y0 ε E V J :=
  ⟨wK_tensFock hD hk (fun x hx => sigD_layer hσ hD hVs hVK J hk hx) hy.1, wK_physSub hD hk hy.2⟩

theorem YY_wK (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (hVs : IsKStableSub ε E V)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (J : ℕ) {k : Matrix (Fin n) (Fin n) ℂ}
    (hk : k ∈ Kset ε) {y : TensorProduct ℂ D (Fock n)} (hy : y ∈ YY ε E V J) : wK hD hk y ∈ YY ε E V J := by
  obtain ⟨y0, hy0, y1, ⟨x, hx, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hy
  rw [map_add, wK_D hσ hD hk]
  exact Submodule.add_mem _ (Submodule.mem_sup_left (compactAction_mem_layer hσ hD hVs hVK J hk hy0))
    (Submodule.mem_sup_right ⟨_, compactAction_mem_layer hσ hD hVs hVK J hk hx, rfl⟩)

set_option maxHeartbeats 1000000 in

theorem str_YY (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (hVs : IsKStableSub ε E V)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) {c : ℂ}
    (hc : ∀ v ∈ genSub E V, casimir E v = c • v) (J : ℕ) [FiniteDimensional ℂ (YY ε E V J)]
    (hKK : LinearMap.ker (dOp ε (eT E) cpT + dOp' ε (eT E) cmT) ⊓ tensFock (genSub E V) ⊓ physicalSubspace ε ≤
      Y0 ε E V J)
    (hgr : ∀ y ∈ LinearMap.ker (dOp ε (eT E) cpT + dOp' ε (eT E) cmT) ⊓ tensFock (genSub E V) ⊓ physicalSubspace ε,
      gradT y = ((-1 : ℂ) ^ sDeg ε) • y)
    {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) :
    LinearMap.trace ℂ (YY ε E V J) ((gradT ∘ₗ wK hD hk).restrict
        (fun y hy => YY_gradT J (YY_wK hσ hD hVs hVK J hk hy))) =
      ((-1 : ℂ) ^ sDeg ε) * LinearMap.trace ℂ
        (LinearMap.ker (dOp ε (eT E) cpT + dOp' ε (eT E) cmT) ⊓ tensFock (genSub E V) ⊓ physicalSubspace ε :
          Submodule ℂ (TensorProduct ℂ D (Fock n))) ((wK hD hk).restrict (wK_KK hσ hD hVK k hk)) := by
  classical
  set Y := YY ε E V J
  set Dop := dOp ε (eT E) cpT + dOp' ε (eT E) cmT
  have hU : IsInfUnitary ε E := isInfUnitary_of_isDerivedOn hσ hD
  have hE : IsGlRep E := hD.glRep
  let Dl : TSub Y →ₗ[ℂ] TSub Y := Dop.restrict (fun y hy => YY_D hE hVs hc J hy)
  let Γ : TSub Y →ₗ[ℂ] TSub Y := gradT.restrict (fun y hy => YY_gradT J hy)
  let B : TSub Y →ₗ[ℂ] TSub Y := (wK hD hk).restrict (fun y hy => YY_wK hσ hD hVs hVK J hk hy)
  obtain ⟨hker, htr⟩ := str_eq_str_ker Dl Γ B
    (fun x y => by rw [tsub_inner, tsub_inner]; exact tform_D hU _ _)
    (fun x => Subtype.ext (gradT_D E _)) (fun x => Subtype.ext (wK_D hσ hD hk _))
  have h1 : LinearMap.trace ℂ Y ((gradT ∘ₗ wK hD hk).restrict
      (fun y hy => YY_gradT J (YY_wK hσ hD hVs hVK J hk hy))) = LinearMap.trace ℂ (TSub Y) (Γ ∘ₗ B) := rfl
  rw [h1, htr]
  set KK : Submodule ℂ (TensorProduct ℂ D (Fock n)) :=
    LinearMap.ker Dop ⊓ tensFock (genSub E V) ⊓ physicalSubspace ε with hKKdef
  have hmemKK : ∀ x : LinearMap.ker Dl, tsubVal Y (x : TSub Y) ∈ KK := by
    intro x
    have hx : Dl (x : TSub Y) = 0 := x.2
    have hYle := YY_le_genSub (ε := ε) (E := E) (V := V) J (tsubVal_mem (x : TSub Y))
    refine ⟨⟨?_, hYle.1⟩, hYle.2⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    exact congrArg (tsubVal Y) hx
  let f : LinearMap.ker Dl →ₗ[ℂ] KK :=
    { toFun := fun x => ⟨tsubVal Y (x : TSub Y), hmemKK x⟩
      map_add' := fun x y => rfl
      map_smul' := fun c x => rfl }
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      have := congrArg Subtype.val hxy
      exact Subtype.ext (tsubVal_injective this)
    · intro y
      have hyY : (y : TensorProduct ℂ D (Fock n)) ∈ Y := Submodule.mem_sup_left (hKK y.2)
      let x : TSub Y := (⟨y, hyY⟩ : Y)
      have hx : x ∈ LinearMap.ker Dl := by
        rw [LinearMap.mem_ker]
        apply tsubVal_injective
        rw [map_zero]
        exact y.2.1.1
      exact ⟨⟨x, hx⟩, rfl⟩
  let e := LinearEquiv.ofBijective f hf
  rw [← LinearMap.trace_conj' _ e]
  set h := ((-1 : ℂ) ^ sDeg ε) • (wK hD hk).restrict (wK_KK hσ hD hVK k hk) with hhdef
  have hcomm : ∀ x : LinearMap.ker Dl, h (f x) = f ((Γ ∘ₗ B).restrict hker x) := by
    intro x
    have hx1 : ((h (f x) : KK) : TensorProduct ℂ D (Fock n)) =
        ((-1 : ℂ) ^ sDeg ε) • wK hD hk (tsubVal Y (x : TSub Y)) := by
      rw [hhdef, LinearMap.smul_apply, Submodule.coe_smul, LinearMap.restrict_coe_apply]
      rfl
    have hx2 : ((f ((Γ ∘ₗ B).restrict hker x) : KK) : TensorProduct ℂ D (Fock n)) =
        gradT (wK hD hk (tsubVal Y (x : TSub Y))) := rfl
    apply Subtype.ext
    rw [hx1, hx2, hgr _ (wK_KK hσ hD hVK k hk _ (hmemKK x))]
  have hc' : e.conj ((Γ ∘ₗ B).restrict hker) = h := by
    apply LinearMap.ext
    intro y
    rw [LinearEquiv.conj_apply_apply]
    calc e ((Γ ∘ₗ B).restrict hker (e.symm y)) = h (e (e.symm y)) := (hcomm _).symm
      _ = h y := by rw [LinearEquiv.apply_symm_apply]
  rw [hc', map_smul, smul_eq_mul]

end W

end ReciprocityTheory.ChartRestriction.DS.TRGap
end
end

section
noncomputable section

open Finset MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS.TRGap

section Int

variable {Kg : Type*} [TopologicalSpace Kg] [CompactSpace Kg] [MeasurableSpace Kg] [BorelSpace Kg]
  {μ : Measure Kg} [IsFiniteMeasure μ]

theorem integrable_of_cont {F : Type*} [NormedAddCommGroup F] [SecondCountableTopologyEither Kg F]
    {f : Kg → F} (hf : Continuous f) : Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [SecondCountableTopologyEither Kg H]

theorem trace_integral_restrict (L : Submodule ℂ H) [FiniteDimensional ℂ L] {c : Kg → ℂ} (hc : Continuous c)
    (A : Kg → (H →L[ℂ] H)) (hA : ∀ v, Continuous fun k => A k v) (hAL : ∀ k, ∀ x ∈ L, A k x ∈ L)
    (B : H →L[ℂ] H) (hB : ∀ w, B w = ∫ k, c k • A k w ∂μ) (hBL : ∀ x ∈ L, B x ∈ L) :
    LinearMap.trace ℂ L ((B : H →ₗ[ℂ] H).restrict hBL) =
      ∫ k, c k * LinearMap.trace ℂ L ((A k : H →ₗ[ℂ] H).restrict (hAL k)) ∂μ := by
  let b := stdOrthonormalBasis ℂ L
  have hint : ∀ i, Integrable (fun k => c k • A k ((b i : L) : H)) μ :=
    fun i => integrable_of_cont (hc.smul (hA _))
  have h1 : ∀ i, inner ℂ (b i) (((B : H →ₗ[ℂ] H).restrict hBL) (b i)) =
      ∫ k, c k * inner ℂ ((b i : L) : H) (A k ((b i : L) : H)) ∂μ := by
    intro i
    rw [Submodule.coe_inner, LinearMap.coe_restrict_apply]
    change inner ℂ ((b i : L) : H) (B ((b i : L) : H)) = _
    rw [hB, ← integral_inner (hint i)]
    simp only [inner_smul_right]
  rw [LinearMap.trace_eq_sum_inner _ b]
  simp only [h1]
  rw [← integral_finsetSum _ fun i _ => integrable_of_cont (μ := μ)
    (f := fun k => c k * inner ℂ ((b i : L) : H) (A k ((b i : L) : H))) (hc.mul (continuous_const.inner (hA _)))]
  congr 1
  funext k
  rw [LinearMap.trace_eq_sum_inner _ b, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Submodule.coe_inner, LinearMap.coe_restrict_apply]
  rfl

end Int

section Str

variable {n : ℕ} {ε : Fin n → Bool}
  {Kg : Type*} [TopologicalSpace Kg] [CompactSpace Kg] [MeasurableSpace Kg] [BorelSpace Kg]
  {μ : Measure Kg} [IsFiniteMeasure μ]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}

theorem int_str_eq (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {Y Y₀ : Submodule ℂ (TensorProduct ℂ D (Fock n))} [FiniteDimensional ℂ Y] (hle : Y₀ ≤ Y)
    (hSK : ∀ (k : Matrix (Fin n) (Fin n) ℂ) (hk : k ∈ Kset ε), ∀ y ∈ Y, wK hD hk y ∈ Y)
    (hY0K : ∀ (k : Matrix (Fin n) (Fin n) ℂ) (hk : k ∈ Kset ε), ∀ y ∈ Y₀, wK hD hk y ∈ Y₀)
    (hYG : ∀ y ∈ Y, gradT y ∈ Y) (hY0G : ∀ y ∈ Y₀, gradT y ∈ Y₀)
    {φ : Kg → Matrix (Fin n) (Fin n) ℂ} (hφc : Continuous φ) (hφK : ∀ g, φ g ∈ Kset ε)
    {c : Kg → ℂ} (hc : Continuous c)
    (hrange : ∀ y : TSub Y, tsubVal Y ((∫ k, c k • tOp hD hSK (φ k) ∂μ) y) ∈ Y₀) :
    ∫ k, c k * LinearMap.trace ℂ Y ((gradT ∘ₗ wK hD (hφK k)).restrict
        (fun y hy => hYG _ (hSK _ (hφK k) y hy))) ∂μ =
      ∫ k, c k * LinearMap.trace ℂ Y₀ ((gradT ∘ₗ wK hD (hφK k)).restrict
        (fun y hy => hY0G _ (hY0K _ (hφK k) y hy))) ∂μ := by
  classical
  set Yt := TSub Y
  let W : Kg → (Yt →L[ℂ] Yt) := fun k => tOp hD hSK (φ k)
  have hWc : Continuous W := by
    rw [continuous_clm_apply]
    intro y
    exact ((tOp_isURepOn hD hSK hσ).2.2 y).comp_continuous hφc hφK
  let Γt : Yt →L[ℂ] Yt := LinearMap.toContinuousLinearMap
    ((gradT.restrict hYG : Y →ₗ[ℂ] Y) : Yt →ₗ[ℂ] Yt)
  let Y0t : Submodule ℂ Yt := Y₀.comap (tsubVal Y)
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl Y0t
  let π : Yt →ₗ[ℂ] Yt := Y0t.subtype ∘ₗ Y0t.linearProjOfIsCompl C hC
  have hπ : ∀ z ∈ Y0t, π z = z := fun z hz => by
    show ((Y0t.linearProjOfIsCompl C hC z : Y0t) : Yt) = z
    have := Submodule.linearProjOfIsCompl_apply_left hC ⟨z, hz⟩
    exact congrArg Subtype.val this
  have hπr : ∀ z, π z ∈ Y0t := fun z => (Y0t.linearProjOfIsCompl C hC z).2
  let ℓl : (Yt →L[ℂ] Yt) →ₗ[ℂ] ℂ :=
    { toFun := fun A => LinearMap.trace ℂ Yt ((LinearMap.id - π) ∘ₗ (Γt : Yt →ₗ[ℂ] Yt) ∘ₗ (A : Yt →ₗ[ℂ] Yt))
      map_add' := fun A A' => by simp [LinearMap.comp_add]
      map_smul' := fun a A => by simp [LinearMap.comp_smul] }
  let ℓ := LinearMap.toContinuousLinearMap ℓl
  have hint : Integrable (fun k => c k • W k) μ := integrable_of_cont (hc.smul hWc)
  set Bt := ∫ k, c k • W k ∂μ
  have hB0 : ℓ Bt = 0 := by
    show LinearMap.trace ℂ Yt ((LinearMap.id - π) ∘ₗ (Γt : Yt →ₗ[ℂ] Yt) ∘ₗ (Bt : Yt →ₗ[ℂ] Yt)) = 0
    have : (LinearMap.id - π) ∘ₗ (Γt : Yt →ₗ[ℂ] Yt) ∘ₗ (Bt : Yt →ₗ[ℂ] Yt) = 0 := by
      apply LinearMap.ext
      intro y
      have hy : Γt (Bt y) ∈ Y0t := hY0G _ (hrange y)
      simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.zero_apply]
      rw [ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_coe, hπ _ hy, sub_self]
    rw [this, map_zero]
  have hcomm : ℓ Bt = ∫ k, c k * ℓ (W k) ∂μ := by
    rw [← ContinuousLinearMap.integral_comp_comm ℓ hint]
    simp only [map_smul, smul_eq_mul]

  have hWk : ∀ k, ((W k : Yt →L[ℂ] Yt) : Yt →ₗ[ℂ] Yt) =
      (((wK hD (hφK k)).restrict (hSK _ (hφK k)) : Y →ₗ[ℂ] Y) : Yt →ₗ[ℂ] Yt) := by
    intro k
    simp only [W, tOp, dif_pos (hφK k)]
    rfl
  have hY : ∀ k, LinearMap.trace ℂ Y ((gradT ∘ₗ wK hD (hφK k)).restrict
      (fun y hy => hYG _ (hSK _ (hφK k) y hy))) =
      LinearMap.trace ℂ Yt ((Γt : Yt →ₗ[ℂ] Yt) ∘ₗ (W k : Yt →ₗ[ℂ] Yt)) := by
    intro k
    rw [hWk]
    rfl
  have hY0 : ∀ k, LinearMap.trace ℂ Y₀ ((gradT ∘ₗ wK hD (hφK k)).restrict
      (fun y hy => hY0G _ (hY0K _ (hφK k) y hy))) =
      LinearMap.trace ℂ Yt (π ∘ₗ (Γt : Yt →ₗ[ℂ] Yt) ∘ₗ (W k : Yt →ₗ[ℂ] Yt)) := by
    intro k
    have hr : LinearMap.range (π ∘ₗ (Γt : Yt →ₗ[ℂ] Yt) ∘ₗ (W k : Yt →ₗ[ℂ] Yt)) ≤ Y0t := by
      rintro _ ⟨y, rfl⟩
      exact hπr _
    rw [trace_eq_trace_restrict_of_range_le _ _ hr]
    have hmem : ∀ z : Y0t, tsubVal Y (z : Yt) ∈ Y₀ := fun z => z.2
    let f : Y0t →ₗ[ℂ] Y₀ :=
      { toFun := fun z => ⟨tsubVal Y (z : Yt), hmem z⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hf : Function.Bijective f := by
      constructor
      · intro x y hxy
        have h' : ((f x : Y₀) : TensorProduct ℂ D (Fock n)) = ((f y : Y₀) : TensorProduct ℂ D (Fock n)) := by
          rw [hxy]
        exact Subtype.ext (tsubVal_injective h')
      · intro y
        exact ⟨⟨(show Yt from ⟨y, hle y.2⟩), y.2⟩, rfl⟩
    let e := LinearEquiv.ofBijective f hf
    rw [← LinearMap.trace_conj' _ e]
    congr 1
    apply LinearMap.ext
    intro y
    rw [LinearEquiv.conj_apply_apply]
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [LinearEquiv.symm_apply_apply]
    apply Subtype.ext
    have hx : (Γt : Yt →ₗ[ℂ] Yt) ((W k : Yt →ₗ[ℂ] Yt) (x : Yt)) ∈ Y0t := by
      rw [hWk]
      exact hY0G _ (hY0K _ (hφK k) _ x.2)
    show _ = tsubVal Y (π ((Γt : Yt →ₗ[ℂ] Yt) ((W k : Yt →ₗ[ℂ] Yt) (x : Yt))))
    rw [hπ _ hx, hWk]
    rfl
  have hℓ : ∀ k, ℓ (W k) = LinearMap.trace ℂ Yt ((Γt : Yt →ₗ[ℂ] Yt) ∘ₗ (W k : Yt →ₗ[ℂ] Yt)) -
      LinearMap.trace ℂ Yt (π ∘ₗ (Γt : Yt →ₗ[ℂ] Yt) ∘ₗ (W k : Yt →ₗ[ℂ] Yt)) := by
    intro k
    show LinearMap.trace ℂ Yt ((LinearMap.id - π) ∘ₗ (Γt : Yt →ₗ[ℂ] Yt) ∘ₗ (W k : Yt →ₗ[ℂ] Yt)) = _
    rw [LinearMap.sub_comp, map_sub, LinearMap.id_comp]
  have htc : Continuous fun k => LinearMap.trace ℂ Yt ((Γt : Yt →ₗ[ℂ] Yt) ∘ₗ (W k : Yt →ₗ[ℂ] Yt)) := by
    let m : (Yt →L[ℂ] Yt) →ₗ[ℂ] ℂ :=
      { toFun := fun A => LinearMap.trace ℂ Yt ((Γt : Yt →ₗ[ℂ] Yt) ∘ₗ (A : Yt →ₗ[ℂ] Yt))
        map_add' := fun A A' => by simp [LinearMap.comp_add]
        map_smul' := fun a A => by simp [LinearMap.comp_smul] }
    exact (LinearMap.continuous_of_finiteDimensional m).comp hWc
  have hℓc : Continuous fun k => ℓ (W k) := ℓ.continuous.comp hWc
  have hdiff : ∫ k, c k * (LinearMap.trace ℂ Yt ((Γt : Yt →ₗ[ℂ] Yt) ∘ₗ (W k : Yt →ₗ[ℂ] Yt)) -
      LinearMap.trace ℂ Yt (π ∘ₗ (Γt : Yt →ₗ[ℂ] Yt) ∘ₗ (W k : Yt →ₗ[ℂ] Yt))) ∂μ = 0 := by
    rw [← hB0, hcomm]
    simp only [hℓ]
  simp only [hY, hY0]
  have hi1 : Integrable (fun k => c k * LinearMap.trace ℂ Yt ((Γt : Yt →ₗ[ℂ] Yt) ∘ₗ (W k : Yt →ₗ[ℂ] Yt))) μ :=
    integrable_of_cont (hc.mul htc)
  have hi2 : Integrable (fun k => c k *
      LinearMap.trace ℂ Yt (π ∘ₗ (Γt : Yt →ₗ[ℂ] Yt) ∘ₗ (W k : Yt →ₗ[ℂ] Yt))) μ := by
    refine integrable_of_cont (hc.mul ?_)
    have : (fun k => LinearMap.trace ℂ Yt (π ∘ₗ (Γt : Yt →ₗ[ℂ] Yt) ∘ₗ (W k : Yt →ₗ[ℂ] Yt))) =
        fun k => LinearMap.trace ℂ Yt ((Γt : Yt →ₗ[ℂ] Yt) ∘ₗ (W k : Yt →ₗ[ℂ] Yt)) - ℓ (W k) := by
      funext k
      rw [hℓ]
      ring
    rw [this]
    exact htc.sub hℓc
  rw [← sub_eq_zero, ← integral_sub hi1 hi2]
  simpa only [mul_sub] using hdiff

end Str

section Range

variable {n : ℕ} {ε : Fin n → Bool}
  {Kg : Type*} [TopologicalSpace Kg] [CompactSpace Kg] [MeasurableSpace Kg] [BorelSpace Kg]
  {μ : Measure Kg} [IsFiniteMeasure μ]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [SecondCountableTopologyEither Kg H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}

theorem btot_range (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {Y : Submodule ℂ (TensorProduct ℂ D (Fock n))} [FiniteDimensional ℂ Y]
    (hSK : ∀ (k : Matrix (Fin n) (Fin n) ℂ) (hk : k ∈ Kset ε), ∀ y ∈ Y, wK hD hk y ∈ Y)
    {L : Submodule ℂ D} {φ : Kg → Matrix (Fin n) (Fin n) ℂ} (hφc : Continuous φ) (hφK : ∀ g, φ g ∈ Kset ε)
    {c : Kg → ℂ} (hc : Continuous c)
    (hL : ∀ (s s' : Finset (Fin (n * n))) (u : H),
      ∫ k, (c k * ffMat ε (φ k) s s') • σ (φ k) u ∂μ ∈ L.map D.subtype)
    (hYP : Y ≤ physicalSubspace ε) (y : TSub Y) :
    tsubVal Y ((∫ k, c k • tOp hD hSK (φ k) ∂μ) y) ∈ tensFock (n := n) L ⊓ physicalSubspace ε := by
  refine ⟨?_, hYP (tsubVal_mem _)⟩
  apply mem_tensorFock_of_coeffs
  intro s
  have hW : Continuous fun k => tOp hD hSK (φ k) := by
    rw [continuous_clm_apply]
    intro v
    exact ((tOp_isURepOn hD hSK hσ).2.2 v).comp_continuous hφc hφK
  have hint : Integrable (fun k => c k • tOp hD hSK (φ k)) μ := integrable_of_cont (hc.smul hW)
  let Ψ : TSub Y →L[ℂ] H := LinearMap.toContinuousLinearMap
    (D.subtype ∘ₗ tcoef ((fockBasis n).coord s) ∘ₗ tsubVal Y)
  have hΨ : ∀ z, Ψ z = ((tcoef ((fockBasis n).coord s) (tsubVal Y z) : D) : H) := fun z => rfl
  have h1 : Ψ ((∫ k, c k • tOp hD hSK (φ k) ∂μ) y) = ∫ k, c k • Ψ (tOp hD hSK (φ k) y) ∂μ := by
    rw [ContinuousLinearMap.integral_apply hint, ← ContinuousLinearMap.integral_comp_comm Ψ
      (hint.apply_continuousLinearMap y)]
    simp only [ContinuousLinearMap.smul_apply, map_smul]
  have h2 : ∀ k, c k • Ψ (tOp hD hSK (φ k) y) =
      ∑ s', (c k * ffMat ε (φ k) s s') • σ (φ k) ((tcoef ((fockBasis n).coord s') (tsubVal Y y) : D) : H) := by
    intro k
    rw [hΨ, tOp_apply hD hSK (hφK k), tco_wK, Submodule.coe_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun s' _ => ?_
    rw [coord_ff_basis, Submodule.coe_smul, smul_smul]
    rfl
  have hmem : Ψ ((∫ k, c k • tOp hD hSK (φ k) ∂μ) y) ∈ L.map D.subtype := by
    rw [h1]
    simp_rw [h2]
    rw [integral_finsetSum]
    · exact Submodule.sum_mem _ fun s' _ => hL s s' _
    · intro s' _
      exact integrable_of_cont ((hc.mul ((ffMat_continuous s s').comp hφc)).smul
        (((hσ.2.2 _).comp_continuous hφc fun g => kset_mem_UJset (hφK g))))
  obtain ⟨x, hx, hxe⟩ := hmem
  have : tcoef ((fockBasis n).coord s) (tsubVal Y ((∫ k, c k • tOp hD hSK (φ k) ∂μ) y)) = x :=
    Subtype.ext (hxe.trans (hΨ _)).symm
  rw [this]
  exact hx

end Range

end ReciprocityTheory.ChartRestriction.DS.TRGap
end
end

section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.TRGap

variable {n : ℕ} {ε : Fin n → Bool} {N : Type*} [AddCommGroup N] [Module ℂ N]

theorem involute_exteriorPower {p : ℕ} {w : Fock n} (hw : w ∈ ⋀[ℂ]^p (Fin n × Fin n → ℂ)) :
    CliffordAlgebra.involute w = ((-1 : ℂ) ^ p) • w := by
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at hw
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    exact involute_ιMulti p v
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, smul_add]
  | smul a x _ hx => rw [map_smul, hx, smul_comm]

theorem gradT_range_ext {V : Submodule ℂ N} {p : ℕ} {z : TensorProduct ℂ N (Fock n)}
    (hz : z ∈ LinearMap.range (TensorProduct.map V.subtype (⋀[ℂ]^p (Fin n × Fin n → ℂ)).subtype)) :
    gradT z = ((-1 : ℂ) ^ p) • z := by
  obtain ⟨x, rfl⟩ := hz
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v w =>
    simp only [TensorProduct.map_tmul, gradT, Submodule.coe_subtype, AlgHom.toLinearMap_apply,
      LinearMap.id_apply]
    rw [involute_exteriorPower w.2, TensorProduct.tmul_smul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, smul_add]

theorem gradT_cpcm (i a j b : Fin n) :
    gradT (N := N) * (cpT i a * cmT j b) = cpT i a * cmT j b * gradT := by
  rw [← mul_assoc, gradT_cpT, neg_mul, mul_assoc, gradT_cmT, mul_neg, neg_neg, mul_assoc]

theorem gradT_sgE (a b : Fin n) :
    gradT (N := N) * sgE ε cpT cmT a b = sgE ε cpT cmT a b * gradT := by
  unfold sgE
  split_ifs
  · rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun x _ => gradT_cpcm _ _ _ _
  · rw [mul_neg, neg_mul, Finset.mul_sum, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun x _ => gradT_cpcm _ _ _ _
  · simp

theorem gradT_diagE (E : Fin n → Fin n → Module.End ℂ N) (a b : Fin n) (y : TensorProduct ℂ N (Fock n)) :
    gradT (diagE ε (eT E) cpT cmT a b y) = diagE ε (eT E) cpT cmT a b (gradT y) := by
  have h1 := LinearMap.congr_fun (eT_gradT E a b) y
  have h2 := LinearMap.congr_fun (gradT_sgE (ε := ε) (N := N) a b) y
  simp only [Module.End.mul_apply] at h1 h2
  simp only [diagE, LinearMap.add_apply, map_add, h1, h2]

theorem gradT_kLowSpan (E : Fin n → Fin n → Module.End ℂ N) {z : TensorProduct ℂ N (Fock n)} {c : ℂ}
    (hz : gradT z = c • z) {y : TensorProduct ℂ N (Fock n)}
    (hy : y ∈ kLowSpan ε (diagE ε (eT E) cpT cmT) z) : gradT y = c • y := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, -, rfl⟩ := hx
    induction l with
    | nil => exact hz
    | cons p l ih =>
      simp only [lowWord]
      rw [gradT_diagE, ih, map_smul]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, smul_add]
  | smul a x _ hx => rw [map_smul, hx, smul_comm]

end ReciprocityTheory.ChartRestriction.DS.TRGap
end
end

section
noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS.TRGap

def SupTraceStatement (n : ℕ) : Prop :=
  ∀ (ε : Fin n → Bool) (lam : Fin n → ℝ) (h : ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),
    Formalism.MainNotions.S.IsDS ε lam σ → Formalism.QuantumDeterminants.IsHCParam lam → GapAtLeast ε lam h → thrStar ε < h →
    1 ≤ pOf ε → 1 ≤ qOf ε →
    ∃ (W : Type) (_ : NormedAddCommGroup W) (_ : InnerProductSpace ℂ W) (_ : FiniteDimensional ℂ W)
      (T : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)),
      Nontrivial W ∧ Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset ε) T ∧ Formalism.MainNotions.S.IsKTypeOf ε T (gaW ε lam) ⊤ ∧
      ∀ (P : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ) (B : H →L[ℂ] H),
        (∀ w : H, B w = ∫ k, (MvPolynomial.eval (entVar (Formalism.REAL.toMK k)) P * physDet ε (Formalism.REAL.toMK k)) •
          σ (Formalism.REAL.toMK k) w ∂(Formalism.REAL.muK ε)) →
        FiniteDimensional ℂ (LinearMap.range (B : H →ₗ[ℂ] H)) ∧
        LinearMap.trace ℂ (LinearMap.range (B : H →ₗ[ℂ] H))
            ((B : H →ₗ[ℂ] H).restrict (fun x _ => LinearMap.mem_range_self (B : H →ₗ[ℂ] H) x)) =
          (-1 : ℂ) ^ sDeg ε * ∫ k, MvPolynomial.eval (entVar (Formalism.REAL.toMK k)) P *
            LinearMap.trace ℂ W (T (Formalism.REAL.toMK k) : W →ₗ[ℂ] W) ∂(Formalism.REAL.muK ε)

section Helpers

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem trace_restrict_range (f : M →ₗ[ℂ] M) (L : Submodule ℂ M) [FiniteDimensional ℂ L] (hfL : ∀ x, f x ∈ L) :
    LinearMap.trace ℂ (LinearMap.range f) (f.restrict (fun x _ => LinearMap.mem_range_self f x)) =
      LinearMap.trace ℂ L (f.restrict (fun x _ => hfL x)) := by
  have hle : LinearMap.range f ≤ L := by
    rintro _ ⟨x, rfl⟩
    exact hfL x
  set R' : Submodule ℂ L := (LinearMap.range f).comap L.subtype
  have hr : LinearMap.range (f.restrict (fun x _ => hfL x) : L →ₗ[ℂ] L) ≤ R' := by
    rintro _ ⟨x, rfl⟩
    exact LinearMap.mem_range_self f _
  rw [trace_eq_trace_restrict_of_range_le _ _ hr]
  let e : R' ≃ₗ[ℂ] LinearMap.range f := Submodule.comapSubtypeEquivOfLe hle
  rw [← LinearMap.trace_conj' _ e]
  congr 1

end Helpers

section Helpers2

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {D : Submodule ℂ H}

theorem trace_map_subtype {L : Submodule ℂ D} [FiniteDimensional ℂ L] (g : D →ₗ[ℂ] D) (hg : ∀ x ∈ L, g x ∈ L)
    (f : H →ₗ[ℂ] H) (hf : ∀ x ∈ L.map D.subtype, f x ∈ L.map D.subtype) (hfg : ∀ x : D, f x = g x) :
    LinearMap.trace ℂ (L.map D.subtype) (f.restrict hf) = LinearMap.trace ℂ L (g.restrict hg) := by
  let e : L ≃ₗ[ℂ] L.map D.subtype := L.equivMapOfInjective D.subtype D.injective_subtype
  rw [← LinearMap.trace_conj' (g.restrict hg) e]
  congr 1
  apply LinearMap.ext
  intro y
  rw [LinearEquiv.conj_apply_apply]
  apply Subtype.ext
  obtain ⟨x, rfl⟩ := e.surjective y
  rw [LinearEquiv.symm_apply_apply]
  show f ((x : D) : H) = ((g (x : D) : D) : H)
  exact hfg x

end Helpers2

open MeasureTheory in

theorem supTrace (n : ℕ) : SupTraceStatement n := by
  intro ε lam h H _ _ σ hDS hHC hgap hthr hp hq
  have : CompleteSpace H := hDS.1
  have hσ : IsURepOn (UJset ε) σ := hDS.2.2.1
  obtain ⟨hanti, hint⟩ := hHC
  have hstd : StdGap ε lam := ⟨hanti, h, hgap, lt_of_le_of_lt (le_max_left _ _) hthr⟩
  obtain ⟨V, hV, hV0, hVK, hc⟩ := arb_datum hDS (casOnSmooth_of_isDS hDS hstd)
  have hD := isDerivedOn_smE hσ
  have htop := data_closGen_eq_top hstd hσ hD hV hc hVK hDS.2.2.2.1 hV0
  obtain ⟨W, i1, i2, i3, T, hWnt, hTU, hTK, hTtr⟩ :=
    kType_clause hσ hD hV hc hVK hint hanti hgap hthr hp hq
  refine ⟨W, i1, i2, i3, T, hWnt, hTU, hTK, fun P B hB => ?_⟩
  obtain ⟨z, -, hzV, hzK, hzdeg, hKK, -⟩ := ker_D_eq_kLowSpan hσ hD hV hc hVK hint hanti hgap hthr hp hq
  have hemb : Topology.IsEmbedding (fun k : Formalism.REAL.KG ε => Formalism.REAL.toMK k) :=
    (Formalism.REAL.isClosedEmbeddingMatrix n ε).1.isEmbedding.comp Topology.IsEmbedding.subtypeVal
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  have : SecondCountableTopology (Formalism.REAL.KG ε) := hemb.isInducing.secondCountableTopology
  set φ : Formalism.REAL.KG ε → Matrix (Fin n) (Fin n) ℂ := fun k => Formalism.REAL.toMK k with hφdef
  have hφc : Continuous φ := hemb.continuous
  have hφK : ∀ g, φ g ∈ Kset ε := fun g => g.2
  have hφ1 : φ 1 = 1 := rfl
  have hφm : ∀ a b, φ (a * b) = φ a * φ b := fun a b => rfl
  have hφs : ∀ m ∈ Kset ε, ∃ g, φ g = m := by
    intro m hm
    have : m ∈ Set.range (fun k : Formalism.REAL.KG ε => Formalism.REAL.toMK k) := by
      rw [Formalism.REAL.range_toMK]
      exact hm
    obtain ⟨g, hg⟩ := this
    exact ⟨g, hg⟩

  choose Qm hQm using fun s s' => ffMat_poly (ε := ε) s s'
  set Q := ∑ s ∈ Finset.univ.filter (IsPhysSet ε), ((-1 : ℂ) ^ s.card) • Qm s s with hQdef
  have hQ : ∀ m, MvPolynomial.eval (entVar m) Q = physDet ε m := by
    intro m
    rw [← strPhys_eq_physDet, strPhys, hQdef, map_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [MvPolynomial.smul_eval, hQm]
    rfl
  have hL3 := fun R => range_one_layer hstd hσ hD hV hc htop (Formalism.REAL.muK ε) φ hφc hφ1 hφm hφK hφs R
  obtain ⟨j0, hj0⟩ := hL3 (P * Q)
  choose js hjs using fun (s s' : Finset (Fin (n * n))) => hL3 (P * Qm s s')
  set J := max j0 (Finset.univ.sup fun p : Finset (Fin (n * n)) × Finset (Fin (n * n)) => js p.1 p.2) with hJ
  have hj0J : j0 ≤ J := le_max_left _ _
  have hjsJ : ∀ s s', js s s' ≤ J := fun s s' =>
    le_trans (Finset.le_sup (f := fun p : Finset (Fin (n * n)) × Finset (Fin (n * n)) => js p.1 p.2)
      (Finset.mem_univ (s, s'))) (le_max_right _ _)

  have hE : IsGlRep (smE ε σ) := hD.glRep
  have hLDf : FiniteDimensional ℂ (layer ε (smE ε σ) V J) := finiteDimensional_layer hV.1 J
  have hlayer : ∀ {j : ℕ}, j ≤ J → (layer ε (smE ε σ) V j).map (smD ε σ).subtype ≤
      (layer ε (smE ε σ) V J).map (smD ε σ).subtype := fun hj => Submodule.map_mono (layer_mono hj)
  set LH := (layer ε (smE ε σ) V J).map (smD ε σ).subtype with hLHdef
  have hLHf : FiniteDimensional ℂ LH := Module.Finite.map _ _
  have hent : ∀ R : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ,
      Continuous fun k => MvPolynomial.eval (entVar (φ k)) R := by
    intro R
    refine (MvPolynomial.continuous_eval R).comp (continuous_pi fun p => ?_)
    rcases p with p | p
    · exact (continuous_apply p.2).comp ((continuous_apply p.1).comp hφc)
    · exact continuous_star.comp ((continuous_apply p.2).comp ((continuous_apply p.1).comp hφc))
  have hBL : ∀ w, B w ∈ LH := by
    intro w
    rw [hB]
    have := hlayer hj0J (hj0 w)
    simpa only [map_mul, hQ] using this
  have hrB : LinearMap.range (B : H →ₗ[ℂ] H) ≤ LH := by
    rintro _ ⟨w, rfl⟩
    exact hBL w
  refine ⟨Submodule.finiteDimensional_of_le hrB, ?_⟩
  rw [trace_restrict_range (B : H →ₗ[ℂ] H) LH hBL]
  have hAL : ∀ k, ∀ x ∈ LH, σ (φ k) x ∈ LH := by
    rintro k _ ⟨y, hy, rfl⟩
    exact ⟨sigD hD (hφK k) y, sigD_layer hσ hD hV.2.1 hVK J (hφK k) hy, rfl⟩
  have hAc : ∀ v, Continuous fun k => σ (φ k) v := fun v =>
    (hσ.2.2 v).comp_continuous hφc fun g => kset_mem_UJset (hφK g)
  have hcont : Continuous fun k => MvPolynomial.eval (entVar (φ k)) P * physDet ε (φ k) := by
    have := hent (P * Q)
    simpa only [map_mul, hQ] using this
  rw [trace_integral_restrict (μ := Formalism.REAL.muK ε) LH hcont (fun k => σ (φ k)) hAc hAL B hB
    (fun x _ => hBL x)]

  have hYf : FiniteDimensional ℂ (YY ε (smE ε σ) V J) := YY_fd hV.1 J
  have hY0G : ∀ y ∈ Y0 ε (smE ε σ) V J, gradT y ∈ Y0 ε (smE ε σ) V J := fun y hy =>
    ⟨tensFock_lTensor_stable _ hy.1, (physSub_stable ε (smE ε σ)).2.2.2.2 y hy.2⟩
  have hY0K : ∀ (k : Matrix (Fin n) (Fin n) ℂ) (hk : k ∈ Kset ε), ∀ y ∈ Y0 ε (smE ε σ) V J,
      wK hD hk y ∈ Y0 ε (smE ε σ) V J := fun k hk y hy => compactAction_mem_layer hσ hD hV.2.1 hVK J hk hy
  have hYK : ∀ (k : Matrix (Fin n) (Fin n) ℂ) (hk : k ∈ Kset ε), ∀ y ∈ YY ε (smE ε σ) V J,
      wK hD hk y ∈ YY ε (smE ε σ) V J := fun k hk y hy => YY_wK hσ hD hV.2.1 hVK J hk hy
  have hle : Y0 ε (smE ε σ) V J ≤ YY ε (smE ε σ) V J := le_sup_left

  have hpt : ∀ k, MvPolynomial.eval (entVar (φ k)) P * physDet ε (φ k) *
      LinearMap.trace ℂ LH (((σ (φ k) : H →L[ℂ] H) : H →ₗ[ℂ] H).restrict (hAL k)) =
      MvPolynomial.eval (entVar (φ k)) P * LinearMap.trace ℂ (Y0 ε (smE ε σ) V J)
        ((gradT ∘ₗ wK hD (hφK k)).restrict (fun y hy => hY0G _ (hY0K _ (hφK k) y hy))) := by
    intro k
    rw [trace_map_subtype (sigD hD (hφK k)) (fun x hx => sigD_layer hσ hD hV.2.1 hVK J (hφK k) hx) _ _
      (fun x => rfl)]
    have := str_tensFock_physSub hD (hφK k) (fun x hx => sigD_layer hσ hD hV.2.1 hVK J (hφK k) hx)
      (fun y hy => hY0G _ (hY0K _ (hφK k) y hy))
    rw [show LinearMap.trace ℂ (Y0 ε (smE ε σ) V J)
        ((gradT ∘ₗ wK hD (hφK k)).restrict (fun y hy => hY0G _ (hY0K _ (hφK k) y hy))) = _ from this]
    ring
  simp_rw [hpt]

  have hcP := hent P
  have hrange := fun y => btot_range (μ := Formalism.REAL.muK ε) hσ hD hYK (L := layer ε (smE ε σ) V J) hφc hφK hcP
    (fun s s' u => by
      have h1 := hlayer (hjsJ s s') (hjs s s' u)
      have h2 : ∫ k, (MvPolynomial.eval (entVar (φ k)) P * ffMat ε (φ k) s s') • σ (φ k) u ∂(Formalism.REAL.muK ε) =
          ∫ k, MvPolynomial.eval (entVar (φ k)) (P * Qm s s') • σ (φ k) u ∂(Formalism.REAL.muK ε) := by
        congr 1
        funext k
        rw [map_mul, hQm]
        rfl
      show ∫ k, (MvPolynomial.eval (entVar (φ k)) P * ffMat ε (φ k) s s') • σ (φ k) u ∂(Formalism.REAL.muK ε) ∈ _
      rw [h2]
      exact h1) (YY_le_genSub J |>.trans inf_le_right) y
  rw [← int_str_eq (μ := Formalism.REAL.muK ε) hσ hD hle hYK hY0K (fun y hy => YY_gradT J hy) hY0G hφc hφK hcP hrange]

  have hcg : ∀ v ∈ genSub (smE ε σ) V, casimir (smE ε σ) v = ((casVal lam : ℝ) : ℂ) • v :=
    casimir_scalar_on_generated hE hc
  have hAK : IsKStableSub ε (diagE ε (eT (smE ε σ)) cpT cmT) (tensFock (n := n) V) :=
    fun a b hab y hy => tensorFock_diagAction_stable ε hV.2.1 hab hy
  have hKKY0 : LinearMap.ker (dOp ε (eT (smE ε σ)) cpT + dOp' ε (eT (smE ε σ)) cmT) ⊓
      tensFock (genSub (smE ε σ) V) ⊓ physicalSubspace ε ≤ Y0 ε (smE ε σ) V J := by
    intro y hy
    have hyP : y ∈ physicalSubspace (N := smD ε σ) ε := hy.2
    rw [hKK] at hy
    have hyV : y ∈ tensFock (n := n) V := kLowSpan_le hAK hzV hy
    exact ⟨tensorFock_mono (layer_mono (E := smE ε σ) (V := V) (ε := ε) (Nat.zero_le J)) hyV, hyP⟩
  have hgr : ∀ y ∈ LinearMap.ker (dOp ε (eT (smE ε σ)) cpT + dOp' ε (eT (smE ε σ)) cmT) ⊓
      tensFock (genSub (smE ε σ) V) ⊓ physicalSubspace ε, gradT y = ((-1 : ℂ) ^ sDeg ε) • y := by
    intro y hy
    rw [hKK] at hy
    exact gradT_kLowSpan (smE ε σ) (gradT_range_ext hzdeg) hy
  have hfin : ∀ k, MvPolynomial.eval (entVar (φ k)) P * LinearMap.trace ℂ (YY ε (smE ε σ) V J)
      ((gradT ∘ₗ wK hD (hφK k)).restrict (fun y hy => YY_gradT J (hYK _ (hφK k) y hy))) =
      (-1 : ℂ) ^ sDeg ε * (MvPolynomial.eval (entVar (φ k)) P * LinearMap.trace ℂ W (T (φ k) : W →ₗ[ℂ] W)) := by
    intro k
    rw [str_YY hσ hD hV.2.1 hVK hcg J hKKY0 hgr (hφK k), hTtr (φ k) (hφK k)]
    ring
  simp_rw [hfin]
  rw [integral_const_mul]

end ReciprocityTheory.ChartRestriction.DS.TRGap
end
end
