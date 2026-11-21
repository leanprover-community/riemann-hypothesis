import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemSupportBDIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
import Formalism.LocalToGlobal.ProjectiveLattices.EmbKCoe
import BuildAid.ForwardExisting

section
section
noncomputable section

open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor Polynomial IntermediateField

namespace GlobalTheory.EigDecomp

theorem exists_integral_separating (E : Type) [Field E] [NumberField E] :
    ∃ α : 𝓞 E, (∀ τ τ' : E →+* ℂ, τ (α : E) = τ' (α : E) → τ = τ') ∧
      ∀ a : 𝓞 E, ∃ N : ℤ, N ≠ 0 ∧ ∃ g : ℤ[X], aeval α g = N • a := by
  obtain ⟨α0, hα0⟩ := Field.exists_primitive_element ℚ E
  obtain ⟨d, hd, hint⟩ := exists_integral_multiples ℤ ℚ ({α0} : Finset E)
  have hi : IsIntegral ℤ (d • α0) := hint α0 (Finset.mem_singleton_self _)
  let α : 𝓞 E := ⟨d • α0, hi⟩
  have hαE : (α : E) = d • α0 := rfl
  have hadjF : ℚ⟮(α : E)⟯ = ⊤ := by
    refine top_le_iff.mp (hα0 ▸ IntermediateField.adjoin_simple_le_iff.mpr ?_)
    have h1 : α0 = ((d : ℚ)⁻¹) • (α : E) := by
      rw [hαE, zsmul_eq_mul, Algebra.smul_def, ← mul_assoc, ← map_intCast (algebraMap ℚ E) d, ← map_mul,
        inv_mul_cancel₀ (Int.cast_ne_zero.mpr hd), map_one, one_mul]
    rw [h1]
    exact IntermediateField.smul_mem _ (IntermediateField.mem_adjoin_simple_self ℚ _)
  have hadj : Algebra.adjoin ℚ {(α : E)} = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (α : E)), hadjF, IntermediateField.top_toSubalgebra]
  refine ⟨α, fun τ τ' h => ?_, fun a => ?_⟩
  · have := AlgHom.ext_of_adjoin_eq_top hadj (φ₁ := τ.toRatAlgHom) (φ₂ := τ'.toRatAlgHom)
      (by rintro x rfl; exact h)
    ext x
    exact congrArg (fun f : E →ₐ[ℚ] ℂ => f x) this
  · have ha : (a : E) ∈ Algebra.adjoin ℚ {(α : E)} := hadj ▸ Algebra.mem_top
    rw [Algebra.adjoin_singleton_eq_range_aeval] at ha
    obtain ⟨g, hg⟩ := ha
    obtain ⟨b, hbM, hb⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) g
    refine ⟨b, nonZeroDivisors.ne_zero hbM, IsLocalization.integerNormalization (nonZeroDivisors ℤ) g, ?_⟩
    apply RingOfIntegers.coe_injective
    have hg' : aeval (algebraMap (𝓞 E) E α) g = algebraMap (𝓞 E) E a := hg
    rw [← aeval_algebraMap_apply, ← aeval_map_algebraMap ℚ, hb, map_zsmul, hg', map_zsmul]

end GlobalTheory.EigDecomp

namespace GlobalTheory.EigDecomp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H}

theorem nodal_eq_minpoly_map (c : Coeff l) (α : 𝓞 E)
    (hinj : Function.Injective fun τ : E →+* ℂ => embK c τ α) :
    Lagrange.nodal Finset.univ (fun τ : E →+* ℂ => embK c τ α) = (minpoly ℤ α).map (Int.castRingHom c.F) := by
  have hint : IsIntegral ℤ α := Algebra.IsIntegral.isIntegral α
  have hintE : IsIntegral ℤ (α : E) := RingOfIntegers.isIntegral_coe α
  symm
  refine eq_of_monic_of_dvd_of_natDegree_le Lagrange.nodal_monic ((minpoly.monic hint).map _) ?_ ?_
  · rw [Lagrange.nodal]
    refine Finset.prod_dvd_of_coprime ((pairwise_coprime_X_sub_C hinj).set_pairwise _) fun τ _ => dvd_iff_isRoot.mpr ?_
    have h := aeval_algHom_apply (embK c τ).toIntAlgHom α (minpoly ℤ α)
    rw [minpoly.aeval, map_zero] at h
    rw [IsRoot.def, eval_map, ← algebraMap_int_eq, ← aeval_def]
    exact h
  · rw [natDegree_map_eq_of_injective (RingHom.injective_int _), Lagrange.natDegree_nodal, Finset.card_univ,
      NumberField.Embeddings.card E ℂ, ← RingOfIntegers.minpoly_coe,
      ← natDegree_map_eq_of_injective (algebraMap ℤ ℚ).injective_int,
      ← minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hintE]
    exact minpoly.natDegree_le _

end GlobalTheory.EigDecomp

namespace GlobalTheory.EigDecomp

theorem X_sub_C_mul_basis {ι F : Type*} [Field F] [DecidableEq ι] {s : Finset ι} {v : ι → F} {i : ι}
    (hi : i ∈ s) :
    (X - C (v i)) * Lagrange.basis s v i = C (Lagrange.nodalWeight s v i) * Lagrange.nodal s v := by
  rw [Lagrange.basis_eq_prod_sub_inv_mul_nodal_div hi, mul_left_comm]
  congr 1
  exact EuclideanDomain.mul_div_cancel' (X_sub_C_ne_zero _) (Lagrange.X_sub_C_dvd_nodal v hi)

theorem exists_unique_eigen_sum : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {l : Level H} (c : Coeff l) {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] (φ : c.F →+* R)
    (ρ : 𝓞 E →+* Module.End R V) (v : V), ∃! w : (E →+* ℂ) → V,
      (∀ τ a, ρ a (w τ) = φ (embK c τ a) • w τ) ∧ ∑ τ, w τ = v := by
  intro E _ _ _ H l c R V _ _ _ φ ρ v
  classical
  obtain ⟨α, hinj, hden⟩ := exists_integral_separating E
  let lam : (E →+* ℂ) → c.F := fun τ => embK c τ α
  have hlinj : Function.Injective lam := fun τ τ' h => hinj τ τ' (by
    have := congrArg (fun x : c.F => (x : ℂ)) h
    simpa [lam, embK_coe] using this)
  let A : Module.End R V := ρ α
  let ψ : c.F →+* Module.End R V := (algebraMap R (Module.End R V)).comp φ
  have hc : ∀ x, Commute (ψ x) A := fun x => Algebra.commute_algebraMap_left (φ x) A
  let ev : Polynomial c.F →+* Module.End R V := eval₂RingHom' ψ A hc
  have hev : ∀ p, ev p = p.eval₂ ψ A := fun p => rfl
  have hev_int : ∀ g : ℤ[X], ev (g.map (Int.castRingHom c.F)) = aeval A g := by
    intro g
    rw [hev, eval₂_map, aeval_def]
    congr 1
    exact RingHom.ext_int _ _
  have heig : ∀ (μ : c.F) (x : V), A x = φ μ • x → ∀ p : Polynomial c.F, ev p x = φ (p.eval μ) • x := by
    intro μ x hx p
    induction p using Polynomial.induction_on' with
    | add p q hp hq => rw [map_add, LinearMap.add_apply, hp, hq, eval_add, map_add, add_smul]
    | monomial k a =>
      have hk : ∀ k : ℕ, (A ^ k) x = φ μ ^ k • x := by
        intro k
        induction k with
        | zero => simp
        | succ k ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, hx, smul_smul, pow_succ, mul_comm]
      rw [hev, eval₂_monomial, eval_monomial, Module.End.mul_apply, hk, map_mul, map_pow]
      simp [ψ, smul_smul, mul_comm]
  have hnodal : ev (Lagrange.nodal Finset.univ lam) = 0 := by
    rw [nodal_eq_minpoly_map c α hlinj, hev_int]
    have h := aeval_algHom_apply ρ.toIntAlgHom α (minpoly ℤ α)
    rw [minpoly.aeval, map_zero] at h
    exact h
  let P : (E →+* ℂ) → Module.End R V := fun τ => ev (Lagrange.basis Finset.univ lam τ)
  have hPeig : ∀ τ x, A (P τ x) = φ (lam τ) • P τ x := by
    intro τ x
    have h := congrArg (fun p => ev p x) (X_sub_C_mul_basis (s := Finset.univ) (v := lam) (Finset.mem_univ τ))
    simp only [map_mul, map_sub, hnodal, mul_zero, Module.End.mul_apply, LinearMap.sub_apply,
      LinearMap.zero_apply] at h
    rw [hev X, eval₂_X, hev (C _), eval₂_C] at h
    simpa [ψ, sub_eq_zero, P] using h
  have hsum : ∑ τ, P τ = 1 := by
    simp only [P]
    rw [← map_sum, Lagrange.sum_basis hlinj.injOn Finset.univ_nonempty, map_one]
  have hall : ∀ τ x, A x = φ (lam τ) • x → ∀ a, ρ a x = φ (embK c τ a) • x := by
    intro τ x hx a
    obtain ⟨N, hN, g, hg⟩ := hden a
    have h1 : ρ (N • a) x = φ (embK c τ (N • a)) • x := by
      rw [← hg]
      have e1 := aeval_algHom_apply ρ.toIntAlgHom α g
      have e2 := aeval_algHom_apply (embK c τ).toIntAlgHom α g
      change ρ (aeval α g) x = φ (embK c τ (aeval α g)) • x
      rw [← show aeval A g = ρ (aeval α g) from e1, ← show aeval (lam τ) g = embK c τ (aeval α g) from e2,
        ← hev_int, heig _ _ hx, eval_map, ← algebraMap_int_eq, ← aeval_def]
    have hu : IsUnit (N : R) := by
      rw [← map_intCast φ]
      exact (isUnit_iff_ne_zero.mpr (Int.cast_ne_zero.mpr hN)).map φ
    rw [map_zsmul, map_zsmul, map_zsmul, LinearMap.smul_apply, ← Int.cast_smul_eq_zsmul R,
      ← Int.cast_smul_eq_zsmul R, smul_assoc] at h1
    exact hu.smul_left_cancel.mp h1
  refine ⟨fun τ => P τ v, ⟨fun τ a => hall τ _ (hPeig τ v) a, ?_⟩, ?_⟩
  · show ∑ τ, P τ v = v
    rw [← LinearMap.sum_apply, hsum, Module.End.one_apply]
  · rintro w ⟨hw, hws⟩
    funext τ
    show w τ = P τ v
    rw [← hws, map_sum, Finset.sum_eq_single τ]
    · rw [heig (lam τ) _ (hw τ α), Lagrange.eval_basis_self hlinj.injOn (Finset.mem_univ τ), map_one, one_smul]
    · intro τ' _ hne
      rw [heig (lam τ') _ (hw τ' α), Lagrange.eval_basis_of_ne (Ne.symm hne) (Finset.mem_univ τ'), map_zero, zero_smul]
    · simp

end GlobalTheory.EigDecomp
end
end

open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_embedding_eigenspace_sum : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l) {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] (φ : c.F →+* R) (ρ : 𝓞 E →+* Module.End R V) (v : V), ∃! w : (E →+* ℂ) → V, (∀ τ a, ρ a (w τ) = φ (embK c τ a) • w τ) ∧ ∑ τ, w τ = v := by
  atlas_forward_decl GlobalTheory.EigDecomp.exists_unique_eigen_sum
end

section
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.ChernReg
open scoped TensorProduct ContDiff

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.FlagMod (ev lieBasis rdet detChg)

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

section Basis

variable {R : Type} [CommRing R] {φ : c.F →+* R} {x : Sp R ⟶ Z.X}

theorem exists_eigBasis (g : EigFrame Z φ x) : ∃ b : Module.Basis (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) R (TanM x Z.t.G),
    ∀ p, b p = g.vec p.1 p.2 := by
  have heig : ∀ (τ : E →+* ℂ) (a : Fin (Dw.mult τ) → R) (b : 𝓞 E),
      actR Z.t.act b (∑ i, a i • g.vec τ i) = φ (embK c τ b) • ∑ i, a i • g.vec τ i := fun τ a b => by
    simp only [map_sum, map_smul, g.act_vec, Finset.smul_sum, smul_comm (a _)]
  have hli : LinearIndependent R (fun p : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) => g.vec p.1 p.2) := by
    rw [Fintype.linearIndependent_iff]
    intro a ha p
    have hw := (GlobalTheory.T.existsUnique_embedding_eigenspace_sum c φ (actR Z.t.act) 0).unique
      (y₁ := fun τ => ∑ i, a ⟨τ, i⟩ • g.vec τ i) (y₂ := fun _ => 0)
      ⟨fun τ b => heig τ _ b, by rw [← ha, Fintype.sum_sigma]⟩ ⟨fun τ b => by simp, by simp⟩
    have h0 := congrFun hw p.1
    exact Fintype.linearIndependent_iff.1 (g.linearIndependent_vec p.1) (fun i => a ⟨p.1, i⟩) h0 p.2
  have hsp : ⊤ ≤ Submodule.span R (Set.range fun p : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) => g.vec p.1 p.2) := by
    intro v _
    obtain ⟨w, ⟨hw, hs⟩, -⟩ := GlobalTheory.T.existsUnique_embedding_eigenspace_sum c φ (actR Z.t.act) v
    rw [← hs]
    refine Submodule.sum_mem _ fun τ _ => ?_
    obtain ⟨a, ha, -⟩ := g.existsUnique_sum τ (w τ) (hw τ)
    rw [ha]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨τ, i⟩, rfl⟩)
  exact ⟨Module.Basis.mk hli hsp, fun p => by rw [Module.Basis.mk_apply]⟩

def eigBasis (g : EigFrame Z φ x) : Module.Basis (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) R (TanM x Z.t.G) :=
  (exists_eigBasis g).choose

theorem eigBasis_apply (g : EigFrame Z φ x) (p : Σ τ : E →+* ℂ, Fin (Dw.mult τ)) : eigBasis g p = g.vec p.1 p.2 :=
  (exists_eigBasis g).choose_spec p

def eigBasisFin (g : EigFrame Z φ x) : Module.Basis (Fin (Fintype.card (Σ τ : E →+* ℂ, Fin (Dw.mult τ)))) R (TanM x Z.t.G) :=
  (eigBasis g).reindex (Fintype.equivFin _)

def frameDet (M : GlobalTheory.Reg.MChart Z) (h : ⊤ ≤ x ⁻¹ᵁ M.U) (g : EigFrame Z φ x) : R :=
  rdet ((lieBasis M x h).toMatrix (eigBasisFin g))

theorem isUnit_frameDet (M : GlobalTheory.Reg.MChart Z) (h : ⊤ ≤ x ⁻¹ᵁ M.U) (g : EigFrame Z φ x) : IsUnit (frameDet M h g) :=
  GlobalTheory.FlagMod.isUnit_rdet_toMatrix _ _

theorem ev_detChg_mul_frameDet (M M' : GlobalTheory.Reg.MChart Z) (h : ⊤ ≤ x ⁻¹ᵁ M.U) (h' : ⊤ ≤ x ⁻¹ᵁ M'.U)
    (hh : ⊤ ≤ x ⁻¹ᵁ (M.U ⊓ M'.U)) (g : EigFrame Z φ x) :
    ev x _ hh (detChg M M').val * frameDet M' h' g = frameDet M h g := by
  rw [GlobalTheory.FlagMod.ev_detChg M M' x h h' hh, frameDet, frameDet, GlobalTheory.FlagMod.rdet_toMatrix_mul]

open Classical in

theorem eigBasis_toMatrix (g g' : EigFrame Z φ x) :
    (eigBasis g).toMatrix (eigBasis g') = Matrix.blockDiagonal' fun τ => g.co g' τ := by
  classical
  ext ⟨σ, b⟩ ⟨τ, i⟩
  have hv : ∀ a, g.vec τ a = eigBasis g ⟨τ, a⟩ := fun a => (eigBasis_apply g ⟨τ, a⟩).symm
  rw [Module.Basis.toMatrix_apply, eigBasis_apply, g.vec_eq g' τ i]
  simp only [hv, map_sum, map_smul, Module.Basis.repr_self, Finsupp.coe_finset_sum, Finset.sum_apply,
    Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
  by_cases h : σ = τ
  · subst h
    simp [Matrix.blockDiagonal'_apply_eq]
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ h]
    exact Finset.sum_eq_zero fun a _ => by rw [if_neg fun e => h (congrArg Sigma.fst e).symm, MulZeroClass.mul_zero]

open Classical in
theorem frameDet_change (M : GlobalTheory.Reg.MChart Z) (h : ⊤ ≤ x ⁻¹ᵁ M.U) (g g' : EigFrame Z φ x) :
    frameDet M h g' = frameDet M h g * ∏ τ, (g.co g' τ).det := by
  rw [frameDet, frameDet, ← GlobalTheory.FlagMod.rdet_toMatrix_mul _ (eigBasisFin g), GlobalTheory.FlagMod.rdet_self]
  congr 1
  have e : (eigBasisFin g).toMatrix (eigBasisFin g') =
      ((eigBasis g).toMatrix (eigBasis g')).submatrix (Fintype.equivFin _).symm (Fintype.equivFin _).symm := by
    ext i j
    simp [eigBasisFin, Module.Basis.toMatrix_apply]
  rw [e, Matrix.det_submatrix_equiv_self, eigBasis_toMatrix, ReciprocityTheory.ChartRestriction.G.T0.HDiscLat.det_blockDiagonal']

theorem toMatrix_map_of_semilinear {R' : Type} [CommRing R'] {N N' : Type} [AddCommGroup N] [Module R N]
    [AddCommGroup N'] [Module R' N'] {ψ : R →+* R'} (f : N →ₛₗ[ψ] N') {n m : ℕ} (b : Module.Basis (Fin n) R N)
    (b' : Module.Basis (Fin n) R' N') (v : Fin m → N) (v' : Fin m → N') (hb : ∀ i, f (b i) = b' i)
    (hv : ∀ j, f (v j) = v' j) : b'.toMatrix v' = (b.toMatrix v).map ψ := by
  ext i j
  have e : v' j = ∑ k, ψ (b.repr (v j) k) • b' k := by
    rw [← hv, ← b.sum_repr (v j), map_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [map_smulₛₗ, hb, b.sum_repr]
  rw [Module.Basis.toMatrix_apply, e, Module.Basis.repr_sum_self]
  rfl

theorem frameDet_isMap {R' : Type} [CommRing R'] {φ' : c.F →+* R'} {x' : Sp R' ⟶ Z.X} (ψ : R →+* R')
    (e : spMap ψ ≫ x = x') (M : GlobalTheory.Reg.MChart Z) (h : ⊤ ≤ x ⁻¹ᵁ M.U) (h' : ⊤ ≤ x' ⁻¹ᵁ M.U)
    (g : EigFrame Z φ x) (g' : EigFrame Z φ' x') (hg : g.IsMap ψ g') :
    frameDet M h' g' = ψ (frameDet M h g) := by
  rw [frameDet, frameDet, GlobalTheory.FlagMod.map_rdet]
  congr 1
  refine toMatrix_map_of_semilinear (GlobalTheory.FlagMod.tanPull ψ e) _ _ _ _
    (fun j => GlobalTheory.FlagMod.tanPull_lieBasis M ψ e h h' j) fun j => ?_
  simp only [eigBasisFin, Module.Basis.reindex_apply, eigBasis_apply]
  apply GlobalTheory.FlagMod.tan_ext_left
  rw [GlobalTheory.FlagMod.tanPull_left]
  simp only [EigFrame.vec, GlobalTheory.LieMet.left_tanOf]
  exact (hg _ _).symm

end Basis

section Flag

variable {F : Type} [Field F] {e : F ≃+* c.F} (C : FlagCpt Z e)

theorem ev_fromSpecStalk_eq {Y : Scheme.{0}} (x : Y) {V : Y.Opens} (hx : x ∈ V) (h : ⊤ ≤ Y.fromSpecStalk x ⁻¹ᵁ V)
    (u : Γ(Y, V)) : ev (Y.fromSpecStalk x) V h u = (Y.presheaf.germ V x hx).hom u := by
  have : (Y.fromSpecStalk x).appLE V ⊤ h ≫ (Scheme.ΓSpecIso (Y.presheaf.stalk x)).hom =
      Y.presheaf.germ V x hx := by
    rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hx]
    simp only [Category.assoc, ← Functor.map_comp]
    rw [show ∀ q : (Opposite.op (⊤ : (Spec (Y.presheaf.stalk x)).Opens) ⟶ Opposite.op ⊤),
      (Spec (Y.presheaf.stalk x)).presheaf.map q = 𝟙 _ from fun q => by
        rw [Subsingleton.elim q (𝟙 _)]; exact CategoryTheory.Functor.map_id _ _]
    simp
  exact congrArg (fun q => CommRingCat.Hom.hom q u) this

theorem top_le_stalk_preimage {X Y : Scheme.{0}} (y : X) (f : X ⟶ Y) {V : Y.Opens} (hy : f y ∈ V) :
    ⊤ ≤ (X.fromSpecStalk y ≫ f) ⁻¹ᵁ V := by
  intro z _
  have hz : X.fromSpecStalk y z ⤳ y := by
    have : X.fromSpecStalk y z ∈ Set.range (X.fromSpecStalk y) := ⟨z, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  exact (hz.map f.continuous).mem_open V.isOpen hy

theorem fnOf_app_eq_ev {X Y : Scheme.{0}} [IsIntegral X] (f : X ⟶ Y) {V : Y.Opens} (hg : genericPoint X ∈ f ⁻¹ᵁ V)
    (hh : ⊤ ≤ (X.fromSpecStalk (genericPoint X) ≫ f) ⁻¹ᵁ V) (a : Γ(Y, V)) :
    fnOf (f ⁻¹ᵁ V) hg ((f.app V).hom a) = ev (X.fromSpecStalk (genericPoint X) ≫ f) V hh a := by
  have h1 : ⊤ ≤ X.fromSpecStalk (genericPoint X) ⁻¹ᵁ (f ⁻¹ᵁ V) := top_le_stalk_preimage (genericPoint X) (𝟙 X) hg
  refine (ev_fromSpecStalk_eq (genericPoint X) hg h1 _).symm.trans (Eq.trans ?_
    (GlobalTheory.FlagMod.ev_appLE (X.fromSpecStalk (genericPoint X)) f le_rfl h1 hh a))
  rw [Scheme.Hom.app_eq_appLE]

variable {C}

theorem top_le_of_mem_pull {y : C.Y.X} {J : ((FlagMod.detOm Z).pull (C.π ≫ genι Z)).ι}
    (hy : y ∈ ((FlagMod.detOm Z).pull (C.π ≫ genι Z)).U J) : ⊤ ≤ (stalkPt C.Y y ≫ C.π ≫ genι Z) ⁻¹ᵁ (J PUnit.unit).U :=
  top_le_stalk_preimage y _ (mem_pull.1 hy)

theorem top_le_gen_of_mem_pull {J : ((FlagMod.detOm Z).pull (C.π ≫ genι Z)).ι}
    (hy : genericPoint C.Y.X ∈ ((FlagMod.detOm Z).pull (C.π ≫ genι Z)).U J) :
    ⊤ ≤ (genericPt C.Y ≫ C.π ≫ genι Z) ⁻¹ᵁ (J PUnit.unit).U :=
  top_le_stalk_preimage _ _ (mem_pull.1 hy)

variable (C)

open Classical in

def FlagCpt.detRat (J : ((FlagMod.detOm Z).pull (C.π ≫ genι Z)).ι) : C.Y.X.functionFieldˣ :=
  if h : genericPoint C.Y.X ∈ ((FlagMod.detOm Z).pull (C.π ≫ genι Z)).U J then
    ((isUnit_frameDet (J PUnit.unit) (top_le_gen_of_mem_pull h) C.f0).unit)⁻¹ else 1

theorem FlagCpt.detRat_val {J : ((FlagMod.detOm Z).pull (C.π ≫ genι Z)).ι}
    (h : genericPoint C.Y.X ∈ ((FlagMod.detOm Z).pull (C.π ≫ genι Z)).U J) :
    (C.detRat J : C.Y.X.functionField) = (frameDet (J PUnit.unit) (top_le_gen_of_mem_pull h) C.f0)⁻¹ := by
  rw [FlagCpt.detRat, dif_pos h, Units.val_inv_eq_inv_val, IsUnit.unit_spec]

end Flag

section Presents

variable {F : Type} [Field F] {e : F ≃+* c.F} (C : FlagCpt Z e)

theorem fnOf_pull_detOm_g (J J' : ((FlagMod.detOm Z).pull (C.π ≫ genι Z)).ι)
    (hg : genericPoint C.Y.X ∈ ((FlagMod.detOm Z).pull (C.π ≫ genι Z)).U J ⊓ ((FlagMod.detOm Z).pull (C.π ≫ genι Z)).U J')
    (hh : ⊤ ≤ (genericPt C.Y ≫ C.π ≫ genι Z) ⁻¹ᵁ ((J PUnit.unit).U ⊓ (J' PUnit.unit).U)) :
    fnOf _ hg (((FlagMod.detOm Z).pull (C.π ≫ genι Z)).g J J' : Γ(C.Y.X, _)) =
      (ev (genericPt C.Y ≫ C.π ≫ genι Z) _ hh (detChg (J PUnit.unit) (J' PUnit.unit)).val)⁻¹ := by
  show fnOf _ hg (Units.val (∏ _k : PUnit.{1}, _ ^ (1 : ℤ))) = _
  rw [Fintype.prod_unique]
  erw [zpow_one, LB.val_res, fnOf_resG]
  have hg' : genericPoint C.Y.X ∈ (C.π ≫ genι Z) ⁻¹ᵁ ((J PUnit.unit).U ⊓ (J' PUnit.unit).U) :=
    ⟨mem_pull.1 hg.1, mem_pull.1 hg.2⟩
  refine (fnOf_app_eq_ev (C.π ≫ genι Z) hg' hh _).trans ?_
  exact map_units_inv (ev (genericPt C.Y ≫ C.π ≫ genι Z) _ hh).toMonoidHom _

end Presents

section Presents2

variable {F : Type} [Field F] {e : F ≃+* c.F} (C : FlagCpt Z e)

theorem FlagCpt.isRatSec_detRat : IsRatSec ((FlagMod.detOm Z).pull (C.π ≫ genι Z)) C.detRat := by
  intro J J' hg
  have hJ := top_le_gen_of_mem_pull (C := C) hg.1
  have hJ' := top_le_gen_of_mem_pull (C := C) hg.2
  have hh := GlobalTheory.FlagMod.le_preimage_inf hJ hJ'
  rw [C.detRat_val hg.1, C.detRat_val hg.2, fnOf_pull_detOm_g C J J' hg hh,
    ← ev_detChg_mul_frameDet (J PUnit.unit) (J' PUnit.unit) hJ hJ' hh C.f0, mul_inv]

theorem isEqn_finset_sum {X : Scheme.{0}} [IsIntegral X] {T : Type} (s : Finset T) (D : T → CartierDiv X) (y : X)
    (t : T → X.functionFieldˣ) (ht : ∀ i, (D i).IsEqn y (t i)) : (∑ i ∈ s, D i).IsEqn y (∏ i ∈ s, t i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact CartierDiv.isEqn_zero y
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact (ht a).add ih

theorem FlagCpt.isEqn_detRat (J : ((FlagMod.detOm Z).pull (C.π ≫ genι Z)).ι) (y : C.Y.X)
    (hy : y ∈ ((FlagMod.detOm Z).pull (C.π ≫ genι Z)).U J) :
    (-∑ x : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), C.gr x.1 x.2).IsEqn y (C.detRat J) := by
  have hgen : genericPoint C.Y.X ∈ ((FlagMod.detOm Z).pull (C.π ≫ genι Z)).U J := gen_mem hy
  have hJ := top_le_gen_of_mem_pull (C := C) hgen
  have hy' := top_le_of_mem_pull (C := C) hy
  obtain ⟨φy, fy, t, htri, heq⟩ := C.gr_spec y
  obtain ⟨fy', hmap⟩ := fy.exists_isMap (algebraMap (C.Y.X.presheaf.stalk y) C.Y.X.functionField) htri.2.1 htri.1
  have e1 := frameDet_isMap _ htri.1.symm (J PUnit.unit) hy' hJ fy fy' hmap
  have e2 := frameDet_change (J PUnit.unit) hJ fy' C.f0
  have e3 : ∀ τ, (fy'.co C.f0 τ).det = ∏ i, (t τ i : C.Y.Fn) := fun τ => by
    obtain ⟨h1, h2⟩ := EigFrame.Tri.co τ htri hmap
    rw [Matrix.det_of_upperTriangular (fun i j hij => h1 i j hij)]
    exact Finset.prod_congr rfl fun i _ => h2 i
  have h0 := (isEqn_finset_sum Finset.univ (fun x : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) => C.gr x.1 x.2) y
    (fun x => t x.1 x.2) fun x => heq x.1 x.2).neg
  rw [h0.iff_unitAt, C.detRat_val hgen, e2, e1]
  have hu := isUnit_frameDet (J PUnit.unit) hy' fy
  have hP : ((∏ x : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), t x.1 x.2 : C.Y.Fnˣ) : C.Y.Fn) = ∏ τ, (fy'.co C.f0 τ).det := by
    rw [Units.coe_prod, Fintype.prod_sigma]
    exact Finset.prod_congr rfl fun τ _ => (e3 τ).symm
  have hP0 : (∏ τ, (fy'.co C.f0 τ).det) ≠ 0 := hP ▸ Units.ne_zero _
  rw [Units.val_inv_eq_inv_val, hP, mul_inv, mul_div_assoc, div_self (inv_ne_zero hP0), _root_.mul_one]
  exact UnitAt.inv ⟨_, hu, rfl⟩

theorem FlagCpt.presents_detRat (hL : (FlagMod.detOm Z).IsLB) :
    Presents (-∑ x : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), C.gr x.1 x.2) ((FlagMod.detOm Z).pull (C.π ≫ genι Z))
      C.detRat :=
  ⟨pull_isLB hL _, C.isRatSec_detRat, fun J y hy => C.isEqn_detRat J y hy⟩

theorem FlagCpt.lbIso_detOm_pull (hL : (FlagMod.detOm Z).IsLB) :
    LBIso (C.Y.lb (-∑ x : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), C.gr x.1 x.2))
      ((FlagMod.detOm Z).pull (C.π ≫ genι Z)) :=
  (presents_toLB _).lbIso (C.presents_detRat hL)

end Presents2

theorem lbIso_detOm_flag : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag)
    (k : s.Comp), LBIso ((Φ.C k).Y.lb (-∑ x : Letter S.Dw, (Φ.C k).gr x.1 x.2))
      ((FlagMod.detOm s.T.Z).pull ((Φ.C k).π ≫ genι s.T.Z)) :=
  fun _ _ _ _ _ _ s Φ k => (Φ.C k).lbIso_detOm_pull s.isRec.isLB_detOm

end GlobalTheory.ShFam
end
end
