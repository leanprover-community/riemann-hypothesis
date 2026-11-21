import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOfValILeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockLuDecompositionExists

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FlagZ GlobalTheory.FlagPoly Formalism.DegreeFormula
open IsLocalRing

namespace GlobalTheory.FlagZ

variable {ι κ : Type} [Fintype ι] [Finite κ] {N : ℕ} (a : κ → ι) (l : κ → Fin (N + 1))

theorem exists_eq_flagPt_of_valuationRing (V K : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field K]
    [Algebra V K] [IsFractionRing V K] (s : Sp K ⟶ Sp (GLRing ι N)) (t : Sp V ⟶ Part a l)
    (w : s ≫ orbit a l = Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ t) :
    ∃ k : ι → GL (Fin N) V, t = flagPt a l k := by
  obtain ⟨ψ, rfl⟩ := Spec.map_surjective s
  let g : ι → GL (Fin N) K := fun τ => GeneralLinearGroup.map ψ.hom (univGL ι N τ)
  have hg : Spec.map ψ ≫ orbit a l = flagPt a l g := by
    rw [← flagPt_univGL]
    exact spMap_flagPt a l ψ.hom _
  choose k b hb hkb using fun τ => GlobalTheory.ValIwasawa.iwasawa V K N (g τ)
  have e : flagPt a l g = Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ flagPt a l k := by
    have : g = (fun τ => GeneralLinearGroup.map (algebraMap V K) (k τ)) * b := funext hkb
    rw [this, flagPt_mul a l _ b fun c i j h₁ h₂ => hb (a c) (h₁.trans_le h₂)]
    exact (spMap_flagPt a l (algebraMap V K) k).symm
  refine ⟨k, ?_⟩
  have hu := GlobalTheory.ProjSpace.existsUnique_extend_of_isProjOver (V := V) (K := K) (isProjOver_str a l)
    (Int.castRingHom V) (flagPt a l g) (toZ_ext _ _)
  exact hu.unique ⟨toZ_ext _ _, w.symm.trans hg⟩ ⟨toZ_ext _ _, e.symm⟩

theorem mem_range_orbit_of_specializes (x' : Sp (GLRing ι N)) (y : Part a l) (h : orbit a l x' ⤳ y) :
    y ∈ Set.range (orbit a l) := by
  let φ : (Part a l).presheaf.stalk y ⟶ (Sp (GLRing ι N)).residueField x' :=
    (Part a l).presheaf.stalkSpecializes h ≫ (orbit a l).stalkMap x' ≫ (Sp (GLRing ι N)).residue x'
  obtain ⟨A, hA, hA_local⟩ := exists_factor_valuationRing φ.hom
  let χ : (Part a l).presheaf.stalk y ⟶ .of A := CommRingCat.ofHom (φ.hom.codRestrict _ hA)
  have w : (Sp (GLRing ι N)).fromSpecResidueField x' ≫ orbit a l =
      Spec.map (CommRingCat.ofHom (algebraMap A ((Sp (GLRing ι N)).residueField x'))) ≫
        Spec.map χ ≫ (Part a l).fromSpecStalk y := by
    rw [Scheme.fromSpecResidueField, Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk,
      ← Scheme.SpecMap_stalkSpecializes_fromSpecStalk h]
    simp_rw [← Spec.map_comp_assoc]
    rfl
  obtain ⟨k, hk⟩ := exists_eq_flagPt_of_valuationRing a l A ((Sp (GLRing ι N)).residueField x') _ _ w
  refine ⟨spMap (evalGL k) (closedPoint A), ?_⟩
  have h₁ : Spec.map χ (closedPoint A) = closedPoint ((Part a l).presheaf.stalk y) :=
    comap_closedPoint (S := A) (φ.hom.codRestrict A.toSubring hA)
  have h₂ : (Spec.map χ ≫ (Part a l).fromSpecStalk y) (closedPoint A) = y :=
    (Scheme.Hom.comp_apply _ _ _).trans
      ((congrArg ((Part a l).fromSpecStalk y) h₁).trans (Part a l).fromSpecStalk_closedPoint)
  rw [hk] at h₂
  exact (Scheme.Hom.comp_apply _ _ _).symm.trans h₂

theorem surjective_orbit : ∀ (ι κ : Type) [Fintype ι] [Finite κ] (N : ℕ) (a : κ → ι) (l : κ → Fin (N + 1)),
    Function.Surjective (orbit a l) := by
  intro ι κ _ _ N a l y
  have hd : DenseRange (orbit a l) := (orbit a l).denseRange
  have hη := (genericPoint_spec (Sp (GLRing ι N))).image (orbit a l).continuous
  rw [Set.image_univ, hd.closure_range] at hη
  exact mem_range_orbit_of_specializes a l _ y (hη.specializes (Set.mem_univ y))

end GlobalTheory.FlagZ
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FlagZ GlobalTheory.FlagPoly Formalism.DegreeFormula
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_orbit_map_surjective : ∀ (ι κ : Type) [Fintype ι] [Finite κ] (N : ℕ) (a : κ → ι) (l : κ → Fin (N + 1)), Function.Surjective (orbit a l) := by
  atlas_forward_decl GlobalTheory.FlagZ.surjective_orbit
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FlagZ GlobalTheory.FlagPoly Formalism.DegreeFormula

namespace GlobalTheory

theorem exists_perm_rows_leading_minors_ne_zero_of_det_ne_zero (K : Type) [Field K] :
    ∀ (N : ℕ) (A : Matrix (Fin N) (Fin N) K), A.det ≠ 0 →
      ∃ w : Equiv.Perm (Fin N), ∀ (k : ℕ) (hk : k ≤ N),
        ((A.submatrix w id).submatrix (Fin.castLE hk) (Fin.castLE hk)).det ≠ 0 := by
  intro N
  induction N with
  | zero =>
    intro A _
    refine ⟨1, fun k hk => ?_⟩
    obtain rfl : k = 0 := by omega
    simp
  | succ n ih =>
    intro A hA
    have h1 : ∃ i : Fin (n + 1),
        (A.submatrix i.succAbove (Fin.last n).succAbove).det ≠ 0 := by
      by_contra h
      push_neg at h
      apply hA
      rw [Matrix.det_succ_column A (Fin.last n)]
      simp only [h, mul_zero, Finset.sum_const_zero]
    obtain ⟨i, hi⟩ := h1
    obtain ⟨w', hw'⟩ := ih _ hi
    let w : Equiv.Perm (Fin (n + 1)) :=
      (finSuccEquiv' (Fin.last n)).trans ((Equiv.optionCongr w').trans (finSuccEquiv' i).symm)
    have hw : ∀ j : Fin n, w ((Fin.last n).succAbove j) = i.succAbove (w' j) := by
      intro j
      simp only [w, Equiv.trans_apply, finSuccEquiv'_succAbove, Equiv.optionCongr_apply,
        Option.map_some, finSuccEquiv'_symm_some]
    refine ⟨w, fun k hk => ?_⟩
    rcases Nat.lt_or_ge n k with hlt | hle
    · obtain rfl : k = n + 1 := by omega
      have : (Fin.castLE hk : Fin (n + 1) → Fin (n + 1)) = id := by
        funext x; simp
      rw [this, Matrix.submatrix_id_id, Matrix.det_permute]
      refine mul_ne_zero ?_ hA
      rcases Int.units_eq_one_or (Equiv.Perm.sign w) with h | h <;> simp [h]
    · have hc : ∀ x : Fin k, (Fin.castLE hk x : Fin (n + 1))
          = (Fin.last n).succAbove (Fin.castLE hle x) := by
        intro x
        rw [Fin.succAbove_last]
        rfl
      convert hw' k hle using 2
      ext a b
      simp only [Matrix.submatrix_apply, id, hc, hw]

theorem GL_exists_perm_rows_leading_minors_ne_zero :
    ∀ (K : Type) [Field K] (N : ℕ) (g : GL (Fin N) K), ∃ w : Equiv.Perm (Fin N),
      ∀ (k : ℕ) (hk : k ≤ N),
        ((g.1.submatrix w id).submatrix (Fin.castLE hk) (Fin.castLE hk)).det ≠ 0 := by
  intro K _ N g
  exact exists_perm_rows_leading_minors_ne_zero_of_det_ne_zero K N g.1
    (Matrix.GeneralLinearGroup.det_ne_zero g)

end GlobalTheory
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FlagZ GlobalTheory.FlagPoly Formalism.DegreeFormula
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_lu_decomposition_exists : ∀ (A : Type) [CommRing A] (N : ℕ) (S : Set ℕ) (g : GL (Fin N) A), (∀ (k : ℕ) (hk : k ≤ N), IsUnit (g.1.submatrix (Fin.castLE hk) (Fin.castLE hk)).det) → ∃ L b : GL (Fin N) A, g = L * b ∧ (∀ i j : Fin N, ¬ (∃ s ∈ S, (j : ℕ) < s ∧ s ≤ (i : ℕ)) → L.1 i j = (1 : Matrix (Fin N) (Fin N) A) i j) ∧ ∀ i j : Fin N, (∃ s ∈ S, (j : ℕ) < s ∧ s ≤ (i : ℕ)) → b.1 i j = 0 := by
  first | exact @GlobalTheory.exists_blockLower_mul_blockUpper | exact GlobalTheory.exists_blockLower_mul_blockUpper | (intros; apply GlobalTheory.exists_blockLower_mul_blockUpper <;> assumption)
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FlagZ GlobalTheory.FlagPoly Formalism.DegreeFormula

namespace GlobalTheory.FlagZ

noncomputable def permRowsGL {K : Type} [CommRing K] {N : ℕ} (w : Equiv.Perm (Fin N)) (g : GL (Fin N) K) :
    GL (Fin N) K :=
  GeneralLinearGroup.mk'' (g.1.submatrix w id) (by
    rw [det_permute]
    exact ((Equiv.Perm.sign w).isUnit.map (Int.castRingHom _)).mul ((isUnit_iff_isUnit_det _).1 g.isUnit))

theorem exists_flagPt_eq_comp_cell {ι κ : Type} [Fintype ι] [Finite κ] {N : ℕ} (a : κ → ι)
    (l : κ → Fin (N + 1)) {K : Type} [Field K] (g : ι → GL (Fin N) K) :
    ∃ (w : ι → Equiv.Perm (Fin N)) (ψ : CellRing a l →+* K), flagPt a l g = spMap ψ ≫ cell a l w := by
  choose w hw using fun τ => GlobalTheory.GL_exists_perm_rows_leading_minors_ne_zero K N (g τ)
  choose L b hLb hL hb using fun τ => GlobalTheory.T.block_lu_decomposition_exists K N {s | ∃ k, a k = τ ∧ (l k : ℕ) = s}
    (permRowsGL (w τ) (g τ)) fun k hk => (hw τ k hk).isUnit
  have hB (τ : ι) (i j : Fin N) : Below a l τ i j ↔
      ∃ s ∈ {s | ∃ k, a k = τ ∧ (l k : ℕ) = s}, (j : ℕ) < s ∧ s ≤ (i : ℕ) :=
    ⟨fun ⟨k, h₁, h₂⟩ => ⟨_, ⟨k, h₁, rfl⟩, h₂⟩, fun ⟨_, ⟨k, h₁, e⟩, h₂⟩ => ⟨k, h₁, e ▸ h₂⟩⟩
  have e : g = (fun τ => permRowsGL (w τ).symm (L τ)) * b := by
    funext τ
    ext i j
    have := congrArg (fun m : GL (Fin N) K => m.1 ((w τ).symm i) j) (hLb τ)
    simpa [permRowsGL, Matrix.mul_apply] using this
  refine ⟨fun τ => (w τ).symm, _, e.symm ▸ flagPt_eq_comp_cell a l (fun τ => (w τ).symm)
    (fun τ => permRowsGL (w τ).symm (L τ)) b (fun τ i j h => ?_) fun τ i j h => hb τ i j ((hB _ _ _).1 h)⟩
  exact hL τ _ j fun h' => h ((hB _ _ _).2 h')

theorem exists_mem_range_cell (ι κ : Type) [Fintype ι] [Finite κ] (N : ℕ) (a : κ → ι) (l : κ → Fin (N + 1))
    (x : Part a l) : ∃ w : ι → Equiv.Perm (Fin N), x ∈ Set.range (cell a l w) := by
  obtain ⟨p, rfl⟩ := GlobalTheory.T.flag_orbit_map_surjective ι κ N a l x
  let q : PrimeSpectrum (GLRing ι N) := p
  let ψ : GLRing ι N →+* q.asIdeal.ResidueField := algebraMap _ _
  obtain ⟨w, φ, h⟩ := exists_flagPt_eq_comp_cell a l fun τ => GeneralLinearGroup.map ψ (univGL ι N τ)
  rw [flagPt, evalGL_map_univGL] at h
  let o : Sp q.asIdeal.ResidueField := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum _)
  have hp : spMap ψ o = p := by
    apply PrimeSpectrum.ext
    change Ideal.comap ψ ⊥ = q.asIdeal
    exact Ideal.ker_algebraMap_residueField _
  refine ⟨w, spMap φ o, ?_⟩
  rw [← hp, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, h]

end GlobalTheory.FlagZ
end
