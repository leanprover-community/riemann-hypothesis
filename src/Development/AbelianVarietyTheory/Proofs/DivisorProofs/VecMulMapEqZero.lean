import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EigenvectorLieDegree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.AdelicDegreeTameRamification
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsLieBasisIffIsUnitDet
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LieCombBaseChange
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmCurveBaseChangeComp
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueDifferentialMonHomLieBasis
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomLieEquivScalarTmul
import Development.AbelianVarietyTheory.Counterexamples.AbelianLawCounterexamples.HomExtendsOverDVRHolds
import BuildAid.ForwardExisting

section
section
namespace GlobalTheory

theorem exists_basis_matrix_of_integral_preimage
    (O k : Type) [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Field k] [Algebra O k]
    [IsFractionRing O k] (m n : ℕ) (P : Matrix (Fin m) (Fin n) k)
    (hP : ∀ c, Matrix.vecMul c P = 0 → c = 0) :
    ∃ M : Matrix (Fin m) (Fin m) k, M.det ≠ 0 ∧ ∀ c : Fin m → k,
      (∃ a : Fin n → O, Matrix.vecMul c P = fun j => algebraMap O k (a j)) ↔
        ∃ b : Fin m → O, c = Matrix.vecMul (fun i => algebraMap O k (b i)) M := by
  classical
  let ι : (Fin n → O) →ₗ[O] (Fin n → k) := (Algebra.linearMap O k).compLeft (Fin n)
  let f : (Fin m → k) →ₗ[O] (Fin n → k) := (Matrix.vecMulLinear P).restrictScalars O
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    exact hP c hc
  let L : Submodule O (Fin m → k) := (LinearMap.range ι).comap f
  have hL : ∀ c, c ∈ L ↔ ∃ a : Fin n → O,
      Matrix.vecMul c P = fun j => algebraMap O k (a j) := by
    intro c
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨a, ha.symm⟩
    · rintro ⟨a, ha⟩
      exact ⟨a, ha.symm⟩
  have hfg : L.FG := by
    have h1 : (LinearMap.range ι).FG := by
      rw [← Module.Finite.iff_fg]; infer_instance
    have h2 : (L.map f).FG := by
      have : IsNoetherian O (LinearMap.range ι) := isNoetherian_of_fg_of_noetherian _ h1
      have : IsNoetherian O (L.map f) := isNoetherian_of_le (Submodule.map_comap_le f _)
      rw [← Module.Finite.iff_fg]; infer_instance
    exact Submodule.fg_of_fg_map_injective f hf h2
  have hsp : Submodule.span k (L : Set (Fin m → k)) = ⊤ := by
    rw [eq_top_iff]
    intro c _
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O)
      (Matrix.vecMul c P)
    choose a ha using hd
    have hd0 : algebraMap O k d ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors d.2
    have hmem : (algebraMap O k d) • c ∈ L := by
      rw [hL]
      refine ⟨a, ?_⟩
      funext j
      rw [Matrix.smul_vecMul, ha j]
      simp [Algebra.smul_def]
    have : c = (algebraMap O k d)⁻¹ • ((algebraMap O k d) • c) := by
      rw [smul_smul, inv_mul_cancel₀ hd0, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)
  haveI : Submodule.IsLattice k L := ⟨hfg, hsp⟩
  have hr : Module.finrank O L = m := by
    simpa using Submodule.IsLattice.finrank_of_pi k L
  let b : Module.Basis (Fin m) O L := Module.finBasisOfFinrankEq O L hr
  let M : Matrix (Fin m) (Fin m) k := Matrix.of fun i => (b i : Fin m → k)
  have hv : ∀ x : Fin m → O, Matrix.vecMul (fun i => algebraMap O k (x i)) M
      = ((∑ i, x i • b i : L) : Fin m → k) := by
    intro x
    funext j
    simp [Matrix.vecMul, dotProduct, M, Algebra.smul_def]
  refine ⟨M, ?_, ?_⟩
  · have hli : LinearIndependent k M.row := by
      have := (b.extendOfIsLattice k).linearIndependent
      have e : M.row = ⇑(b.extendOfIsLattice k) := by
        funext i
        rw [Module.Basis.extendOfIsLattice_apply]
        rfl
      rw [e]
      exact this
    have := Matrix.linearIndependent_rows_iff_isUnit.mp hli
    exact ((Matrix.isUnit_iff_isUnit_det M).mp this).ne_zero
  · intro c
    rw [← hL]
    constructor
    · intro hc
      refine ⟨b.repr ⟨c, hc⟩, ?_⟩
      rw [hv, b.sum_repr]
    · rintro ⟨x, rfl⟩
      rw [hv]
      exact Subtype.property _

end GlobalTheory
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_row_space_basis_exists : ∀ (O k : Type) [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Field k] [Algebra O k] [IsFractionRing O k] (m n : ℕ) (P : Matrix (Fin m) (Fin n) k), (∀ c, Matrix.vecMul c P = 0 → c = 0) → ∃ M : Matrix (Fin m) (Fin m) k, M.det ≠ 0 ∧ ∀ c : Fin m → k, (∃ a : Fin n → O, Matrix.vecMul c P = fun j => algebraMap O k (a j)) ↔ ∃ b : Fin m → O, c = Matrix.vecMul (fun i => algebraMap O k (b i)) M := by
  atlas_forward_decl GlobalTheory.exists_basis_matrix_of_integral_preimage
end

section
section
namespace GlobalTheory

open Matrix

theorem matrix_exists_rightInverse_of_saturated_rows {O : Type} [CommRing O] [IsDomain O]
    [IsPrincipalIdealRing O] {m n : ℕ} (N : Matrix (Fin m) (Fin n) O)
    (hinj : ∀ b, Matrix.vecMul b N = 0 → b = 0)
    (hsat : ∀ (r : O) (x : Fin n → O) (b : Fin m → O), r ≠ 0 → r • x = Matrix.vecMul b N →
      ∃ b', x = Matrix.vecMul b' N) :
    ∃ Q : Matrix (Fin n) (Fin m) O, N * Q = 1 := by
  let g : (Fin m → O) →ₗ[O] (Fin n → O) := Matrix.vecMulLinear N
  have hg : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro b hb
    exact hinj b hb
  haveI : Module.IsTorsionFree O ((Fin n → O) ⧸ LinearMap.range g) := by
    refine Module.IsTorsionFree.of_smul_eq_zero ?_
    intro r x h
    by_cases hr : r = 0
    · exact Or.inl hr
    right
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h
    obtain ⟨b, hb⟩ := h
    obtain ⟨b', hb'⟩ := hsat r x b hr hb.symm
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨b', hb'.symm⟩
  haveI : Module.Free O ((Fin n → O) ⧸ LinearMap.range g) := inferInstance
  have hex : Function.Exact g (LinearMap.range g).mkQ := LinearMap.exact_map_mkQ_range g
  obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective (LinearMap.range g).mkQ
    (Submodule.range_mkQ _)
  have hs' : ∃ s, (LinearMap.range g).mkQ ∘ₗ s = LinearMap.id := ⟨s, hs⟩
  have hl' : ∃ l, l ∘ₗ g = LinearMap.id :=
    ((hex.split_tfae hg (Submodule.mkQ_surjective _)).out 0 1).mp hs'
  obtain ⟨l, hl⟩ := hl'
  refine ⟨LinearMap.toMatrixRight' l, ?_⟩
  ext i j
  have h1 : ∀ x, Matrix.vecMul x (LinearMap.toMatrixRight' l) = l x := by
    intro x
    have := LinearMap.toMatrixRight'.symm_apply_apply l
    conv_rhs => rw [← this]
    rfl
  have h2 : Matrix.vecMul (Pi.single i 1) (N * LinearMap.toMatrixRight' l) = Pi.single i 1 := by
    rw [← Matrix.vecMul_vecMul, h1]
    exact LinearMap.congr_fun hl _
  have := congrFun h2 j
  rw [Matrix.single_one_vecMul] at this
  simpa [Matrix.one_apply, Pi.single_apply, eq_comm] using this

theorem det_saturated_lattice_baseChange : ∀ (O k V K : Type) [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Field k] [Algebra O k] [IsFractionRing O k] [CommRing V] [Field K] [Algebra V K] [IsFractionRing V K] (f : O →+* V) (em : k →+* K), (∀ a, algebraMap V K (f a) = em (algebraMap O k a)) → ∀ (m n : ℕ) (P : Matrix (Fin m) (Fin n) k) (M : Matrix (Fin m) (Fin m) k) (C : Matrix (Fin m) (Fin m) K), (∀ c, Matrix.vecMul c P = 0 → c = 0) → M.det ≠ 0 → (∀ c : Fin m → k, (∃ a : Fin n → O, Matrix.vecMul c P = fun j => algebraMap O k (a j)) ↔ ∃ b : Fin m → O, c = Matrix.vecMul (fun i => algebraMap O k (b i)) M) → (∀ c : Fin m → K, (∃ a : Fin n → V, Matrix.vecMul c (P.map em) = fun j => algebraMap V K (a j)) ↔ ∃ b : Fin m → V, c = Matrix.vecMul (fun i => algebraMap V K (b i)) C) → ∃ u : Vˣ, C.det = algebraMap V K u * em M.det := by
  intro O k V K _ _ _ _ _ _ _ _ _ _ f em hf m n P M C hP hM hO hV
  have iO : Function.Injective (algebraMap O k) := IsFractionRing.injective O k
  have iV : Function.Injective (algebraMap V K) := IsFractionRing.injective V K

  have hN : ∃ N : Matrix (Fin m) (Fin n) O, M * P = N.map (algebraMap O k) := by
    have : ∀ i, ∃ a : Fin n → O, Matrix.vecMul (M i) P = fun j => algebraMap O k (a j) := by
      intro i
      refine (hO _).mpr ⟨Pi.single i 1, ?_⟩
      have : (fun j => algebraMap O k ((Pi.single i 1 : Fin m → O) j)) = Pi.single i 1 := by
        ext j; by_cases h : j = i <;> simp [Pi.single_apply, h]
      rw [this, Matrix.single_one_vecMul]; rfl
    choose a ha using this
    refine ⟨Matrix.of a, ?_⟩
    ext i j
    exact congrFun (ha i) j
  obtain ⟨N, hN⟩ := hN
  have hmap : ∀ b : Fin m → O, Matrix.vecMul (Matrix.vecMul (fun i => algebraMap O k (b i)) M) P
      = fun j => algebraMap O k (Matrix.vecMul b N j) := by
    intro b
    rw [Matrix.vecMul_vecMul, hN]
    ext j
    simp [Matrix.vecMul, dotProduct]
  obtain ⟨Q, hQ⟩ := matrix_exists_rightInverse_of_saturated_rows N (by
      intro b hb
      have h1 := hmap b
      rw [hb] at h1
      have h2 := hP _ (h1.trans (by ext j; simp))
      have h3 := Matrix.eq_zero_of_vecMul_eq_zero hM h2
      ext i
      apply iO
      simpa using congrFun h3 i) (by
      intro r x b hr hx
      have hr' : algebraMap O k r ≠ 0 := fun h => hr (iO (by simpa using h))
      obtain ⟨b', hb'⟩ := (hO ((algebraMap O k r)⁻¹ •
        Matrix.vecMul (fun i => algebraMap O k (b i)) M)).mp ⟨x, by
          rw [Matrix.smul_vecMul, hmap, ← hx]
          ext j
          simp only [Pi.smul_apply, smul_eq_mul, map_mul]
          field_simp⟩
      refine ⟨b', ?_⟩
      have h1 := hmap b'
      rw [← hb', Matrix.smul_vecMul, hmap, ← hx] at h1
      ext j
      apply iO
      rw [← congrFun h1 j]
      simp only [Pi.smul_apply, smul_eq_mul, map_mul]
      field_simp)
  have hcomp : (algebraMap V K).comp f = em.comp (algebraMap O k) := RingHom.ext hf
  set M' := M.map em with hM'
  set P' := P.map em with hP'
  set Q' := (Q.map f).map (algebraMap V K) with hQ'
  have hMP : M' * P' = (N.map f).map (algebraMap V K) := by
    rw [hM', hP', ← Matrix.map_mul, hN]
    ext i j
    simp [hf]
  have h1 : M' * (P' * Q') = 1 := by
    rw [← Matrix.mul_assoc, hMP, hQ', ← Matrix.map_mul, ← Matrix.map_mul, hQ]
    simp
  have h2 : (P' * Q') * M' = 1 := mul_eq_one_comm.mp h1
  have hsingle : ∀ i : Fin m, (fun j => algebraMap V K ((Pi.single i 1 : Fin m → V) j)) = Pi.single i 1 := by
    intro i
    ext j; by_cases h : j = i <;> simp [Pi.single_apply, h]
  have hU : ∃ U : Matrix (Fin m) (Fin m) V, C = U.map (algebraMap V K) * M' := by
    have : ∀ i, ∃ a : Fin n → V, Matrix.vecMul (C i) P' = fun j => algebraMap V K (a j) := by
      intro i
      refine (hV _).mpr ⟨Pi.single i 1, ?_⟩
      rw [hsingle, Matrix.single_one_vecMul]; rfl
    choose a ha using this
    have hA : C * P' = (Matrix.of a).map (algebraMap V K) := by
      ext i j
      exact congrFun (ha i) j
    refine ⟨Matrix.of a * Q.map f, ?_⟩
    rw [Matrix.map_mul, ← hA, ← hQ', Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc P', h2,
      Matrix.mul_one]
  have hU' : ∃ U' : Matrix (Fin m) (Fin m) V, M' = U'.map (algebraMap V K) * C := by
    have : ∀ i, ∃ b : Fin m → V, M' i = Matrix.vecMul (fun i => algebraMap V K (b i)) C := by
      intro i
      refine (hV _).mp ⟨(N.map f) i, ?_⟩
      ext j
      exact congrFun (congrFun hMP i) j
    choose b hb using this
    refine ⟨Matrix.of b, ?_⟩
    ext i j
    exact congrFun (hb i) j
  obtain ⟨U, hU⟩ := hU
  obtain ⟨U', hU'⟩ := hU'
  have hd : M'.det = em M.det := by rw [hM', RingHom.map_det]; rfl
  have hd0 : em M.det ≠ 0 := by simpa using hM
  have e1 : C.det = algebraMap V K U.det * em M.det := by
    rw [hU, Matrix.det_mul, hd, RingHom.map_det (algebraMap V K)]; rfl
  have e2 : em M.det = algebraMap V K U'.det * C.det := by
    have := congrArg Matrix.det hU'
    rw [Matrix.det_mul, hd] at this
    rw [this, RingHom.map_det (algebraMap V K)]; rfl
  have e3 : U.det * U'.det = 1 := by
    apply iV
    rw [map_mul, map_one]
    apply mul_right_cancel₀ hd0
    rw [one_mul]
    conv_rhs => rw [e2, e1]
    ring
  exact ⟨Units.mkOfMulEqOne _ _ e3, e1⟩

end GlobalTheory
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_basis_change_determinant : ∀ (O k V K : Type) [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Field k] [Algebra O k] [IsFractionRing O k] [CommRing V] [Field K] [Algebra V K] [IsFractionRing V K] (f : O →+* V) (em : k →+* K), (∀ a, algebraMap V K (f a) = em (algebraMap O k a)) → ∀ (m n : ℕ) (P : Matrix (Fin m) (Fin n) k) (M : Matrix (Fin m) (Fin m) k) (C : Matrix (Fin m) (Fin m) K), (∀ c, Matrix.vecMul c P = 0 → c = 0) → M.det ≠ 0 → (∀ c : Fin m → k, (∃ a : Fin n → O, Matrix.vecMul c P = fun j => algebraMap O k (a j)) ↔ ∃ b : Fin m → O, c = Matrix.vecMul (fun i => algebraMap O k (b i)) M) → (∀ c : Fin m → K, (∃ a : Fin n → V, Matrix.vecMul c (P.map em) = fun j => algebraMap V K (a j)) ↔ ∃ b : Fin m → V, c = Matrix.vecMul (fun i => algebraMap V K (b i)) C) → ∃ u : Vˣ, C.det = algebraMap V K u * em M.det := by
  atlas_forward_decl GlobalTheory.det_saturated_lattice_baseChange
end

section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM Matrix

namespace GlobalTheory.FlatDegreeCompare

section Lie

variable {R K : Type} [CommRing R] [CommRing K]

def Integral (f : R →+* K) {G : Over (Sp R)} [GrpObj G] {A : Over (Sp K)} (φ : A.left ⟶ G.left)
    (w : epsR K ⟶ A) : Prop :=
  ∃ u : epsR R ⟶ G, IsTangent u ∧ IsVecOver f φ u w

def Indep {A : Over (Sp K)} [GrpObj A] {m : ℕ} (x : Fin m → (epsR K ⟶ A)) : Prop :=
  (∀ i, IsTangent (x i)) ∧ ∀ c c' w, IsLieComb c x w → IsLieComb c' x w → c = c'

theorem Indep.of_basis {A : Over (Sp K)} [GrpObj A] [IsCommMonObj A] {n : ℕ} {e : Fin n → (epsR K ⟶ A)}
    (he : IsLieBasis e) : Indep e :=
  ⟨he.1, fun c _ w h h' => (he.2 w ((LieComb.lieComb_algebra K A n e he.1).2.1 c w h)).unique h h'⟩

theorem Indep.of_eigBasis {O : Type} [CommRing O] {A : Over (Sp K)} [GrpObj A] [IsCommMonObj A] {act : OAct O A}
    {χ : O →+* K} {m : ℕ} {x : Fin m → (epsR K ⟶ A)} (h : EigenvectorLieDegree.IsEigBasis act χ x) : Indep x := by
  refine ⟨fun i => (h.1 i).1, fun c c' w hc hc' => (h.2 w ?_).unique hc hc'⟩
  let y : Fin m → Serre.Lie act := fun i => Serre.Lie.mk act (x i) (h.1 i).1
  have hy : ∀ a i, a • y i = χ a • y i := fun a i => Serre.Lie.ext (Over.OverMorphism.ext ((h.1 i).2 a))
  obtain rfl := (Serre.Lie.isLieComb_iff c y w).1 hc
  refine ⟨Serre.Lie.isTangent _, fun a => ?_⟩
  have : a • ∑ i, c i • y i = χ a • ∑ i, c i • y i := by
    rw [Finset.smul_sum, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_comm a, hy, smul_comm]
  exact congrArg (fun z : Serre.Lie act => z.hom.left) this

theorem comb_comb {A : Over (Sp K)} [GrpObj A] [IsCommMonObj A] {n m : ℕ} {e : Fin n → (epsR K ⟶ A)}
    (he : ∀ j, IsTangent (e j)) {x : Fin m → (epsR K ⟶ A)} {P : Matrix (Fin m) (Fin n) K}
    (hP : ∀ i, IsLieComb (P i) e (x i)) (c : Fin m → K) (w : epsR K ⟶ A) :
    IsLieComb c x w ↔ IsLieComb (c ᵥ* P) e w := by
  obtain ⟨h₁, h₂, h₃, -⟩ := LieComb.lieComb_algebra K A n e he
  have key : ∀ w, IsLieComb c x w → IsLieComb (c ᵥ* P) e w := fun w hw => by
    rw [Matrix.vecMul_eq_sum]; exact h₃ m P x c w hP hw
  refine ⟨key w, fun hw => ?_⟩
  obtain ⟨w', hw'⟩ := ((LieComb.lieComb_algebra K A m x fun i => h₂ _ _ (hP i)).1 c).exists
  rwa [(h₁ _).unique hw (key w' hw')]

variable {f : R →+* K} {G : Over (Sp R)} [GrpObj G] {A : Over (Sp K)} [GrpObj A] {φ : A.left ⟶ G.left}

theorem integral_iff [IsCommMonObj G] (hφ : IsGrpPullback A G (spMap f) φ) {n : ℕ} {e : Fin n → (epsR R ⟶ G)}
    (he : IsLieBasis e) {e' : Fin n → (epsR K ⟶ A)} (h : ∀ j, IsVecOver f φ (e j) (e' j)) (w : epsR K ⟶ A) :
    Integral f φ w ↔ ∃ a : Fin n → R, IsLieComb (fun j => f (a j)) e' w := by
  obtain ⟨h₁, h₂, -⟩ := LieComb.lieComb_algebra R G n e he.1
  constructor
  · rintro ⟨u, hu, hw⟩
    obtain ⟨a, ha, -⟩ := he.2 u hu
    exact ⟨a, (lieComb_baseChange R K f G A φ hφ n e u a e' w h ha).1 hw⟩
  · rintro ⟨a, ha⟩
    obtain ⟨u, hu⟩ := (h₁ a).exists
    exact ⟨u, h₂ _ _ hu, (lieComb_baseChange R K f G A φ hφ n e u a e' w h hu).2 ha⟩

theorem lattice_iff [IsCommMonObj G] [IsCommMonObj A] (hφ : IsGrpPullback A G (spMap f) φ) {n m : ℕ}
    {e : Fin n → (epsR R ⟶ G)} (he : IsLieBasis e) {e' : Fin n → (epsR K ⟶ A)} (he' : IsLieBasis e')
    (h : ∀ j, IsVecOver f φ (e j) (e' j)) {x : Fin m → (epsR K ⟶ A)} {P : Matrix (Fin m) (Fin n) K}
    (hP : ∀ i, IsLieComb (P i) e' (x i)) (c : Fin m → K) :
    (∃ w, IsLieComb c x w ∧ Integral f φ w) ↔ ∃ a : Fin n → R, c ᵥ* P = fun j => f (a j) := by
  simp only [integral_iff hφ he h, comb_comb he'.1 hP]
  constructor
  · rintro ⟨w, hw, a, ha⟩
    exact ⟨a, (Indep.of_basis he').2 _ _ w hw ha⟩
  · rintro ⟨a, ha⟩
    obtain ⟨w, hw⟩ := ((LieComb.lieComb_algebra K A n e' he'.1).1 (c ᵥ* P)).exists
    exact ⟨w, hw, a, ha ▸ hw⟩

theorem exists_frame [IsLocalRing R] (hG : IsSemiAbelian G) (hφ : IsGrpPullback A G (spMap f) φ) {m : ℕ}
    {x : Fin m → (epsR K ⟶ A)} (hx : ∀ i, IsTangent (x i)) :
    ∃ (n : ℕ) (e : Fin n → (epsR R ⟶ G)) (e' : Fin n → (epsR K ⟶ A)) (P : Matrix (Fin m) (Fin n) K),
      IsLieBasis e ∧ IsLieBasis e' ∧ (∀ j, IsVecOver f φ (e j) (e' j)) ∧ ∀ i, IsLieComb (P i) e' (x i) := by
  have := hG.smooth
  obtain ⟨n, e, he⟩ := Chart.exists_isLieBasis G hG.smooth
  choose e' h _ using fun j => existsUnique_isVecOver hφ.1 (e j)
  have he' := Chart.isLieBasis_baseChange f hφ he h
  choose P hP _ using fun i => he'.2 _ (hx i)
  exact ⟨n, e, e', P, he, he', h, hP⟩

theorem Indep.vecMul_eq_zero [IsCommMonObj A] {n m : ℕ} {e : Fin n → (epsR K ⟶ A)} (he : ∀ j, IsTangent (e j))
    {x : Fin m → (epsR K ⟶ A)} (hx : Indep x) {P : Matrix (Fin m) (Fin n) K}
    (hP : ∀ i, IsLieComb (P i) e (x i)) (c : Fin m → K) (hc : c ᵥ* P = 0) : c = 0 := by
  obtain ⟨w, hw⟩ := ((LieComb.lieComb_algebra K A m x hx.1).1 0).exists
  refine hx.2 _ _ w ?_ hw
  rw [comb_comb he hP] at hw ⊢
  rwa [hc, ← Matrix.zero_vecMul P]

end Lie

theorem Integral.of_models {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
    [IsFractionRing V K] {G G' : Over (Sp V)} [GrpObj G] [GrpObj G'] {A : Over (Sp K)} [GrpObj A]
    {φ : A.left ⟶ G.left} {φ' : A.left ⟶ G'.left} (hG : IsSemiAbelian G) (hG' : IsSemiAbelian G')
    (hφ : IsGrpPullback A G (spMap (algebraMap V K)) φ) (hφ' : IsGrpPullback A G' (spMap (algebraMap V K)) φ')
    {w : epsR K ⟶ A} (h : Integral (algebraMap V K) φ w) : Integral (algebraMap V K) φ' w := by
  obtain ⟨e, he, h₁⟩ := grpPullback_iso hφ (isGrpPullback_pullback G _)
  obtain ⟨e', he', h₂⟩ := grpPullback_iso hφ' (isGrpPullback_pullback G' _)
  obtain ⟨F, ⟨hF, hFf⟩, -⟩ := HomExtExamples.homExtSt_holds V K G G' hG hG' (e.inv ≫ e'.hom) inferInstance
  have a : ((Over.pullback (spMap (algebraMap V K))).map F).left ≫ pullback.fst G'.hom _ =
      pullback.fst G.hom _ ≫ F.left := pullback.lift_fst _ _ _
  have key : φ ≫ F.left = φ' := by
    rw [← h₁, Category.assoc, ← a, hFf, ← Category.assoc, ← Over.comp_left, e.hom_inv_id_assoc, h₂]
  obtain ⟨u, hu, hw⟩ := h
  refine ⟨u ≫ F, DiffCoord.isTangent_comp_hom F hu, ?_⟩
  unfold IsVecOver at hw ⊢
  rw [← key, ← Category.assoc, hw, Category.assoc]
  rfl

theorem vecMul_map_eq_zero {k K : Type} [Field k] [Field K] (em : k →+* K) {m n : ℕ} {P : Matrix (Fin m) (Fin n) k}
    (hP : ∀ c, c ᵥ* P = 0 → c = 0) (c : Fin m → K) (hc : c ᵥ* P.map em = 0) : c = 0 := by
  obtain ⟨g, hg⟩ := (Matrix.vecMulLinear P).exists_leftInverse_of_injective (LinearMap.ker_eq_bot'.2 hP)
  have h1 : P * LinearMap.toMatrixRight' g = 1 := by
    apply Matrix.toLinearMapRight'.injective
    rw [Matrix.toLinearMapRight'_mul, Matrix.toLinearMapRight'_one]
    change Matrix.toLinearMapRight' (LinearMap.toMatrixRight' g) ∘ₗ Matrix.vecMulLinear P = _
    simpa using hg
  have h2 : P.map em * (LinearMap.toMatrixRight' g).map em = 1 := by
    rw [← Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [← Matrix.vecMul_one c, ← h2, ← Matrix.vecMul_vecMul, hc, Matrix.zero_vecMul]

theorem valuation_valRing {k : Type} [Field k] [NumberField k] (𝔭 : HeightOneSpectrum (𝓞 k)) (x : k) :
    (IsDiscreteValuationRing.maximalIdeal (AdelicDegreeTameRamification.valRing k 𝔭)).valuation k x = 𝔭.valuation k x := by
  set w := (IsDiscreteValuationRing.maximalIdeal (AdelicDegreeTameRamification.valRing k 𝔭)).valuation k
  have hE : w.IsEquiv (𝔭.valuation k) := by
    refine Valuation.isEquiv_iff_val_le_one.2 fun {a} => ⟨fun h => ?_, fun h => ?_⟩
    · obtain ⟨r, rfl⟩ := IsDiscreteValuationRing.exists_lift_of_le_one h
      exact r.2
    · exact (IsDiscreteValuationRing.maximalIdeal (AdelicDegreeTameRamification.valRing k 𝔭)).valuation_le_one (K := k) ⟨a, h⟩
  obtain ⟨π, hπ⟩ := 𝔭.valuation_exists_uniformizer k
  obtain ⟨ρ, hρ⟩ := (IsDiscreteValuationRing.maximalIdeal (AdelicDegreeTameRamification.valRing k 𝔭)).valuation_exists_uniformizer k
  change w ρ = _ at hρ
  have lt : ∀ z : WithZero (Multiplicative ℤ), z < 1 → z ≤ WithZero.exp (-1) := fun z hz => by
    rcases eq_or_ne z 0 with rfl | h0
    · exact zero_le'
    · rw [← WithZero.exp_log h0] at hz ⊢
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hz
      rw [WithZero.exp_le_exp]; omega
  have l1 : (WithZero.exp (-1) : WithZero (Multiplicative ℤ)) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  have hw : w π = WithZero.exp (-1) := by
    refine le_antisymm (lt _ (hE.lt_one_iff_lt_one.2 (hπ ▸ l1))) ?_
    rw [← hρ, hE, hπ]
    exact lt _ (hE.lt_one_iff_lt_one.1 (hρ ▸ l1))
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have h0 : 𝔭.valuation k x ≠ 0 := by simpa using hx
  have : w x = w (π ^ (-WithZero.log (𝔭.valuation k x))) := by
    rw [hE.eq_iff, map_zpow₀, hπ, ← WithZero.exp_zsmul]
    simp [WithZero.exp_log h0]
  rw [this, map_zpow₀, hw, ← WithZero.exp_zsmul]
  simp [WithZero.exp_log h0]

section Local

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {k : Type} [Field k] [NumberField k]
  {t : SAB H (Sp k)} {m : ℕ} {x : Fin m → (epsR k ⟶ t.G)} {𝔭 : HeightOneSpectrum (𝓞 k)}

def HasModel (t : SAB H (Sp k)) (𝔭 : HeightOneSpectrum (𝓞 k)) : Prop :=
  ∃ (G : Over (Sp (AdelicDegreeTameRamification.valRing k 𝔭))) (_ : GrpObj G) (φ : t.G.left ⟶ G.left),
    IsSemiAbelian G ∧ IsGrpPullback t.G G (spMap (algebraMap (AdelicDegreeTameRamification.valRing k 𝔭) k)) φ

theorem mem_latticeCoords {A : Over (Sp k)} [GrpObj A] {V : ValuationSubring k} {G : Over (Sp V)} [GrpObj G]
    {φ : A.left ⟶ G.left} {x : Fin m → (epsR k ⟶ A)} (c : Fin m → k) :
    c ∈ AdelicDegreeTameRamification.latticeCoords V G φ x ↔ ∃ w, IsLieComb c x w ∧ Integral (algebraMap V k) φ w :=
  exists_congr fun _ => ⟨fun ⟨u, h₁, h₂⟩ => ⟨h₁, u, h₂⟩, fun ⟨h₁, u, h₂⟩ => ⟨u, h₁, h₂⟩⟩

theorem exists_gen (hx : Indep x) (h : HasModel t 𝔭) : ∃ a, AdelicDegreeTameRamification.IsLocalGen t x 𝔭 a := by
  obtain ⟨G, _, φ, hG, hφ⟩ := h
  have := hG.comm
  obtain ⟨n, e, e', P, he, he', h, hP⟩ := exists_frame hG hφ hx.1
  obtain ⟨M, hM, hL⟩ := GlobalTheory.T.integral_row_space_basis_exists (AdelicDegreeTameRamification.valRing k 𝔭) k m n P (hx.vecMul_eq_zero he'.1 hP)
  exact ⟨_, G, _, φ, M, hG, hφ,
    fun c => (mem_latticeCoords c).trans ((lattice_iff hφ he he' h hP c).trans (hL c)), rfl, hM⟩

theorem locOrd_of_gen (hx : Indep x) {a : k} (h : AdelicDegreeTameRamification.IsLocalGen t x 𝔭 a) :
    EigenvectorLieDegree.IsLocOrd t.G x 𝔭 (WithZero.log (𝔭.valuation k a) : ℤ) := by
  obtain ⟨G, _, φ, M, hG, hφ, hL, rfl, hM⟩ := h
  have := hG.comm
  have hu : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).2 hM.isUnit
  have hrow : ∀ i, ∃ w, IsLieComb (M i) x w ∧ Integral (algebraMap (AdelicDegreeTameRamification.valRing k 𝔭) k) φ w := fun i =>
    (mem_latticeCoords _).1 ((hL _).2 ⟨Pi.single i 1, by
      ext j; simp [Matrix.vecMul, dotProduct, Pi.single_apply, apply_ite Subtype.val]⟩)
  choose u' h₁ u h₂ h₃ using hrow
  obtain ⟨n, e, e', P, he, he', h, hP⟩ := exists_frame hG hφ hx.1
  have hid : spMap (RingHom.id k) = 𝟙 (Sp k) := Spec.map_id _
  have : IsMonHom (Iso.refl t.G).hom := inferInstanceAs (IsMonHom (𝟙 t.G))
  refine ⟨AdelicDegreeTameRamification.valRing k 𝔭, k, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, RingHom.id k, 1, G, inferInstance, t.G, inferInstance, φ, 𝟙 _, x, u, u', M⁻¹,
    WithZero.log (𝔭.valuation k M.det), one_pos, fun z => by rw [valuation_valRing, pow_one]; rfl, hG, hφ,
    (isGrpPullback_of_iso (Iso.refl t.G)).congr hid.symm rfl, fun i => ?_, fun i => ⟨h₂ i, h₃ i, _, h₁ i⟩,
    fun w w' hw hw' ⟨c, hc⟩ => ?_, fun i => ?_, ?_, by simp⟩
  · have : Chart.dualMapR (RingHom.id k) = RingHom.id _ := by
      refine RingHom.ext fun a => ?_
      ext <;> simp [Chart.dualMapR]
    unfold IsVecOver
    rw [this, Category.comp_id]
    exact ((congrArg (· ≫ _) (Spec.map_id _)).trans (Category.id_comp _)).symm
  · have key : ∀ b : Fin m → AdelicDegreeTameRamification.valRing k 𝔭, IsLieComb b u w →
        c = (fun i => (b i : k)) ᵥ* M := fun b hb =>
      hx.2 _ _ w' hc ((comb_comb hx.1 h₁ _ _).1 ((lieComb_baseChange _ _ _ G t.G φ hφ m u w b u' w' h₃ hb).1 hw'))
    obtain ⟨b, hb⟩ := (hL c).1 ((mem_latticeCoords c).2 ⟨w', hc, w, hw, hw'⟩)
    refine ⟨b, ?_, fun b' hb' => ?_⟩
    · obtain ⟨a₁, a₂, -⟩ := LieComb.lieComb_algebra _ G m u h₂
      obtain ⟨w₀, hw₀⟩ := (a₁ b).exists
      have o : IsVecOver (algebraMap (AdelicDegreeTameRamification.valRing k 𝔭) k) φ w₀ w' :=
        (lieComb_baseChange _ _ _ G t.G φ hφ m u w₀ b u' w' h₃ hw₀).2 ((comb_comb hx.1 h₁ _ _).2 (hb ▸ hc))
      obtain ⟨p, hp, -⟩ := he.2 w hw
      obtain ⟨q, hq, -⟩ := he.2 w₀ (a₂ _ _ hw₀)
      have := (Indep.of_basis he').2 _ _ w' ((lieComb_baseChange _ _ _ G t.G φ hφ n e w p e' w' h hp).1 hw')
        ((lieComb_baseChange _ _ _ G t.G φ hφ n e w₀ q e' w' h hq).1 o)
      obtain rfl : p = q := funext fun j => Subtype.ext (congrFun this j)
      rwa [((LieComb.lieComb_algebra _ G n e he.1).1 p).unique hp hq]
    · have := Matrix.vecMul_injective_of_isUnit hu ((key b' hb').symm.trans hb)
      exact funext fun j => Subtype.ext (congrFun this j)
  · rw [comb_comb hx.1 h₁]
    have : M⁻¹ i ᵥ* M = Pi.single i 1 := by
      have := congrFun (Matrix.nonsing_inv_mul M hM.isUnit) i
      exact this.trans (by ext j; simp [Matrix.one_apply, Pi.single_apply, eq_comm])
    rw [this]
    exact (LieComb.lieComb_algebra _ _ m x hx.1).2.2.2.1 i
  · rw [valuation_valRing, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', map_inv₀, WithZero.exp_neg,
      WithZero.exp_log (by simpa using hM)]

theorem eq_of_locOrd (hx : Indep x) {a : k} (h : AdelicDegreeTameRamification.IsLocalGen t x 𝔭 a) {r : ℝ}
    (hr : EigenvectorLieDegree.IsLocOrd t.G x 𝔭 r) : r = (WithZero.log (𝔭.valuation k a) : ℤ) := by
  obtain ⟨G₀, _, φ₀, M₀, hG₀, hφ₀, hL, rfl, hM₀⟩ := h
  obtain ⟨V, K, _, _, _, _, _, _, em, ε, G, _, A, _, φ, ψ, x', u, u', M, ν, hε, hv, hG, hφ, hψ, hx', hu, hb, hM, hν,
    rfl⟩ := hr
  have := hG₀.comm
  have := hG.comm
  have := PolPull.isCommMonObj_of_isGrpPullback hψ
  have hin : ∀ z : AdelicDegreeTameRamification.valRing k 𝔭, ∃ y : V, algebraMap V K y = em z := fun z =>
    IsDiscreteValuationRing.exists_lift_of_le_one (by rw [hv]; exact pow_le_one' z.2 _)
  let eV := RingEquiv.ofBijective (algebraMap V K).rangeRestrict
    ⟨fun a b e => IsFractionRing.injective V K (congrArg Subtype.val e), (algebraMap V K).rangeRestrict_surjective⟩
  let g := (em.comp (algebraMap (AdelicDegreeTameRamification.valRing k 𝔭) k)).codRestrict (algebraMap V K).range hin
  obtain ⟨f, hf⟩ : ∃ f : AdelicDegreeTameRamification.valRing k 𝔭 →+* V, ∀ z, algebraMap V K (f z) = em (algebraMap _ k z) :=
    ⟨eV.symm.toRingHom.comp g, fun z => congrArg Subtype.val (eV.apply_symm_apply (g z))⟩
  have hf' : (algebraMap V K).comp f = em.comp (algebraMap _ k) := RingHom.ext hf
  obtain ⟨n, e, e₀, P, he, he₀, h, hP⟩ := exists_frame hG₀ hφ₀ hx.1
  have hinj := hx.vecMul_eq_zero he₀.1 hP
  obtain ⟨G₁, _, χ, h', hG₁⟩ : ∃ (G₁ : Over (Sp V)) (_ : GrpObj G₁) (χ : G₁.left ⟶ G₀.left),
      IsGrpPullback G₁ G₀ (spMap f) χ ∧ IsSemiAbelian G₁ :=
    ⟨_, _, _, isGrpPullback_pullback G₀ (spMap f), IsSemiAbelian.pullback _ G₀ hG₀⟩
  have := hG₁.comm
  have := hG₀.smooth
  have := hG₁.smooth
  have n' : IsGrpPullback A G₀ (spMap (algebraMap V K) ≫ spMap f) (ψ ≫ φ₀) :=
    (hψ.comp hφ₀).congr (by rw [spMap_comp_spMap, spMap_comp_spMap, hf']) rfl
  have w : (ψ ≫ φ₀) ≫ G₀.hom = (A.hom ≫ spMap (algebraMap V K)) ≫ spMap f :=
    n'.1.w.trans (Category.assoc _ _ _).symm
  have q := h'.1.lift_fst _ _ w
  have hφ₁ := h'.cancel (n'.congr rfl q.symm) (h'.1.lift_snd _ _ w)
  choose e₁ h₁ _ using fun j => existsUnique_isVecOver h'.1 (e j)
  have he₁ := Chart.isLieBasis_baseChange f h' he h₁
  choose e' h₂ _ using fun j => existsUnique_isVecOver hψ.1 (e₀ j)
  have h₃ := fun j => EllComp.isVecOver_cancel h'.1 hφ₁.1 (h₁ j)
    (by rw [q, hf']; exact EllComp.isVecOver_comp (h j) (h₂ j))
  have he' := Chart.isLieBasis_baseChange _ hφ₁ he₁ h₃
  have hP' : ∀ i, IsLieComb (P.map em i) e' (x' i) := fun i =>
    (lieComb_baseChange _ _ em t.G A ψ hψ n e₀ (x i) (P i) e' (x' i) h₂ (hP i)).1 (hx' i)
  have tx : ∀ i, IsTangent (x' i) := fun i => (hx' i).isTangent hψ (hx.1 i)
  have ix : ∀ c c' w, IsLieComb c x' w → IsLieComb c' x' w → c = c' := fun c c' w a b => by
    rw [comb_comb he'.1 hP'] at a b
    refine sub_eq_zero.1 (vecMul_map_eq_zero em hinj _ ?_)
    rw [Matrix.sub_vecMul, (Indep.of_basis he').2 _ _ w a b, sub_self]
  choose C hC using fun i => (hu i).2.2
  let C' : Matrix (Fin m) (Fin m) K := C
  have hC' : ∀ i, IsLieComb (C' i) x' (u' i) := hC
  obtain ⟨s, hs⟩ := GlobalTheory.T.integral_basis_change_determinant _ k V K f em hf m n P M₀ C' hinj hM₀
    (fun c => (lattice_iff hφ₀ he he₀ h hP c).symm.trans ((mem_latticeCoords c).symm.trans (hL c))) fun c => by
      rw [← lattice_iff hφ₁ he₁ he' h₃ hP' c]
      constructor
      · rintro ⟨z, hz, hi⟩
        obtain ⟨y, hy, hy'⟩ := hi.of_models hG₁ hG hφ₁ hφ
        obtain ⟨b, hb, -⟩ := hb y z hy hy' ⟨c, hz⟩
        exact ⟨b, ix _ _ z hz ((comb_comb tx hC' _ _).1
          ((lieComb_baseChange _ _ _ G A φ hφ m u y b u' z (fun i => (hu i).2.1) hb).1 hy'))⟩
      · rintro ⟨b, rfl⟩
        obtain ⟨a₁, a₂, -⟩ := LieComb.lieComb_algebra _ G m u fun i => (hu i).1
        obtain ⟨y, hy⟩ := (a₁ b).exists
        obtain ⟨z, hz, -⟩ := existsUnique_isVecOver hφ.1 y
        exact ⟨z, (comb_comb tx hC' _ _).1
          ((lieComb_baseChange _ _ _ G A φ hφ m u y b u' z (fun i => (hu i).2.1) hy).1 hz),
          Integral.of_models hG hG₁ hφ hφ₁ ⟨y, a₂ _ _ hy, hz⟩⟩
  have hMC : M * C' = 1 := by
    ext i j
    have := ix _ _ _ ((comb_comb tx hC' _ _).1 (hM i)) ((LieComb.lieComb_algebra _ _ m x' tx).2.2.2.1 i)
    exact (congrFun this j).trans (by simp [Matrix.one_apply, Pi.single_apply, eq_comm])
  have d := congrArg (fun N => (IsDiscreteValuationRing.maximalIdeal V).valuation K (Matrix.det N)) hMC
  have hs1 : (IsDiscreteValuationRing.maximalIdeal V).valuation K (algebraMap V K s) = 1 :=
    ((IsDiscreteValuationRing.maximalIdeal V).valuation_eq_one_iff_notMem).2
      (IsLocalRing.notMem_maximalIdeal.2 s.isUnit)
  have h0 : 𝔭.valuation k M₀.det ≠ 0 := by simpa using hM₀
  simp only [Matrix.det_mul, Matrix.det_one, map_mul, map_one, hs, hs1, hν, hv, _root_.one_mul] at d
  rw [← WithZero.exp_log h0, ← WithZero.exp_nsmul, ← WithZero.exp_add, WithZero.exp_eq_one] at d
  have hν' : ν = ε * WithZero.log (𝔭.valuation k M₀.det) := by
    rw [nsmul_eq_mul] at d; omega
  have : (ε : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hε.ne'
  rw [hν']; push_cast; field_simp

end Local

end GlobalTheory.FlatDegreeCompare
end
end
