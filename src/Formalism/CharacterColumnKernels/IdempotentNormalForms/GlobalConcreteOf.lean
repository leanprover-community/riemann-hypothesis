import Formalism.CharacterColumnKernels.StatementN
import Formalism.CharacterColumnKernels.StatementG
import Formalism.CharacterColumnKernels.StatementX
import Formalism.CharacterColumnKernels.IdempotentNormalForms.LenCokerOfDetNeZero
import Formalism.CharacterColumnKernels.Statement

section
open Finset

noncomputable section

namespace Formalism.NG

section GenKey

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

lemma gen_relMap_apply {a b : Type*} [Fintype a] [Fintype b] (X : Matrix a b O) (v : b → KO O) (i : a) :
    relMap O (KO O) X v i = ∑ j, X i j • v j := rfl

lemma gen_relMap_mul {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    (X : Matrix a b O) (Y : Matrix b c O) :
    relMap O (KO O) (X * Y) = relMap O (KO O) X ∘ₗ relMap O (KO O) Y := by
  refine LinearMap.ext fun v => funext fun i => ?_
  simp only [LinearMap.comp_apply, gen_relMap_apply, Matrix.mul_apply, Finset.sum_smul,
    Finset.smul_sum, mul_smul]
  exact Finset.sum_comm

lemma gen_relMap_one {a : Type*} [Fintype a] [DecidableEq a] (v : a → KO O) :
    relMap O (KO O) (1 : Matrix a a O) v = v := by
  funext i
  simp [gen_relMap_apply, Matrix.one_apply, ite_smul]

lemma gen_key {M G : Type} [Fintype M] [DecidableEq M] [Fintype G] [DecidableEq G]
    (A : Matrix M G O) : ∃ (n : ℕ) (U : Matrix M M O) (f : Fin n ↪ M) (e : Fin n ↪ G),
      (∃ C0 : Matrix G M O, IsUnit (Matrix.of fun p q => (C0 * U) (e p) (f q)).det) ∧
      ∀ C' : Matrix G M O, IsUnit (Matrix.of fun p q => (C' * U) (e p) (f q)).det →
        LinearMap.ker (relMap O (KO O) (C' * A)) = LinearMap.ker (relMap O (KO O) A) := by
  classical
  obtain ⟨n, snf⟩ := (LinearMap.range (Matrix.mulVecLin A)).smithNormalForm (Pi.basisFun O M)
  set U : Matrix M M O := (Pi.basisFun O M).toMatrix snf.bM with hUdef
  set W : Matrix M M O := snf.bM.toMatrix (Pi.basisFun O M) with hWdef
  have hWU : W * U = 1 := Module.Basis.toMatrix_mul_toMatrix_flip _ _
  have hUW : U * W = 1 := Module.Basis.toMatrix_mul_toMatrix_flip _ _
  have hn : n ≤ Fintype.card G := by
    have h1 := Module.finrank_eq_card_basis snf.bN
    have h2 := LinearMap.finrank_range_le (Matrix.mulVecLin A)
    rw [h1, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h2
    exact h2
  let e : Fin n ↪ G := (Fin.castLEEmb hn).trans (Fintype.equivFin G).symm.toEmbedding
  refine ⟨n, U, snf.f, e, ?_, ?_⟩
  · refine ⟨Matrix.of fun i l => ∑ p, if e p = i then W (snf.f p) l else 0, ?_⟩
    have hZ : (Matrix.of fun p q =>
        ((Matrix.of fun i l => ∑ p, if e p = i then W (snf.f p) l else 0) * U) (e p) (snf.f q)) = 1 := by
      ext p q
      simp only [Matrix.of_apply, Matrix.mul_apply, e.injective.eq_iff, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
      rw [← Matrix.mul_apply, hWU]
      simp [Matrix.one_apply, snf.f.injective.eq_iff]
    rw [hZ, Matrix.det_one]
    exact isUnit_one
  · intro C' hC
    set Y : Matrix M G O := W * A with hYdef
    have hAY : A = U * Y := by rw [hYdef, ← Matrix.mul_assoc, hUW, Matrix.one_mul]
    have hY : ∀ k, k ∉ Set.range snf.f → ∀ j, Y k j = 0 := by
      intro k hk j
      have hmem : (fun l => A l j) ∈ LinearMap.range (Matrix.mulVecLin A) :=
        ⟨Pi.single j 1, by
          funext l
          simp⟩
      have h0 := snf.repr_eq_zero_of_notMem_range ⟨_, hmem⟩ hk
      rw [← Module.Basis.toMatrix_mulVec_repr (Pi.basisFun O M)] at h0
      simpa [hYdef, Matrix.mulVec, dotProduct, Matrix.mul_apply] using h0
    apply le_antisymm
    · intro v hv
      rw [LinearMap.mem_ker] at hv ⊢
      set y := relMap O (KO O) Y v with hydef
      have hy0 : ∀ k, k ∉ Set.range snf.f → y k = 0 := by
        intro k hk
        simp [hydef, gen_relMap_apply, hY k hk]
      have hv' : relMap O (KO O) (C' * U) y = 0 := by
        rw [hydef, ← LinearMap.comp_apply, ← gen_relMap_mul, Matrix.mul_assoc, ← hAY]
        exact hv
      set Z : Matrix (Fin n) (Fin n) O := Matrix.of fun p q => (C' * U) (e p) (snf.f q) with hZdef
      have hz : relMap O (KO O) Z (y ∘ snf.f) = 0 := by
        funext p
        have := congrFun hv' (e p)
        rw [gen_relMap_apply, Pi.zero_apply] at this
        rw [gen_relMap_apply, Pi.zero_apply]
        exact (Fintype.sum_of_injective snf.f snf.f.injective _ _
          (fun k hk => by simp [hy0 k hk]) (fun q => rfl)).trans this
      have hyf : y ∘ snf.f = 0 := by
        rw [← gen_relMap_one (y ∘ snf.f), ← Matrix.nonsing_inv_mul Z hC, gen_relMap_mul,
          LinearMap.comp_apply, hz, map_zero]
      have hy : y = 0 := by
        funext k
        by_cases hk : k ∈ Set.range snf.f
        · obtain ⟨q, rfl⟩ := hk
          exact congrFun hyf q
        · exact hy0 k hk
      rw [hAY, gen_relMap_mul, LinearMap.comp_apply, ← hydef, hy, map_zero]
    · intro v hv
      rw [LinearMap.mem_ker] at hv ⊢
      rw [gen_relMap_mul, LinearMap.comp_apply, hv, map_zero]

end GenKey

lemma gen_bigMat_mul {R O : Type*} [Ring R] [CommRing O] [Algebra O R] {m g d : Type*}
    [Fintype m] [Fintype d] [DecidableEq d] (ρ : R →ₐ[O] Matrix d d O) (C : Matrix g m R) (P : Matrix m g R) :
    bigMat (⇑ρ) (C * P) = bigRect (⇑ρ) C * bigRect (⇑ρ) P := by
  ext p q
  simp only [bigMat, bigRect, Matrix.mul_apply, map_sum, map_mul, Matrix.sum_apply,
    Fintype.sum_prod_type]

theorem generic : StatGeneric := by
  intro R O _ _ _ _ _ _ m g s _ _ _ _ d _ _ ρ hρ P
  classical
  have hk := fun w => gen_key (O := O) (bigRect (ρ w) P)
  choose n U f e hC0 hgood using hk
  choose C0 hC0 using hC0
  let res := IsLocalRing.residue O
  let r : ∀ w, d w → d w → R := fun w a b => Function.surjInv (hρ w) (Matrix.single a b 1)
  let c : (Σ w : s, g × m × d w × d w) → Matrix g m R := fun j =>
    Matrix.single j.2.1 j.2.2.1 (r j.1 j.2.2.2.1 j.2.2.2.2)
  let L : ∀ w, Matrix (g × d w) (m × d w) (MvPolynomial (Σ w : s, g × m × d w × d w)
      (IsLocalRing.ResidueField O)) := fun w p q =>
    ∑ j, MvPolynomial.X j * MvPolynomial.C (res (ρ w (c j p.1 q.1) p.2 q.2))
  let Q : s → MvPolynomial (Σ w : s, g × m × d w × d w) (IsLocalRing.ResidueField O) := fun w =>
    (Matrix.of fun p q => ∑ l, L w (e w p) l * MvPolynomial.C (res (U w l (f w q)))).det
  have hevalQ : ∀ w (t : (Σ w : s, g × m × d w × d w) → O),
      MvPolynomial.eval (fun j => res (t j)) (Q w) =
        res (Matrix.of fun p q => (bigRect (ρ w) (∑ j, t j • c j) * U w) (e w p) (f w q)).det := by
    intro w t
    simp only [Q]
    rw [RingHom.map_det, RingHom.map_det]
    congr 1
    ext p q
    simp [L, Matrix.mul_apply, bigRect, Matrix.sum_apply, map_sum]

  have hsum : ∀ w (φ : g × m × d w × d w → O),
      bigRect (ρ w) (∑ j : (Σ w : s, g × m × d w × d w),
        (Pi.single (M := fun w => g × m × d w × d w → O) w φ j.1 j.2) • c j) =
        fun p q => φ (p.1, q.1, p.2, q.2) := by
    intro w φ
    funext p q
    simp only [bigRect, Matrix.sum_apply, Matrix.smul_apply, map_sum, map_smul]
    rw [Fintype.sum_sigma]
    rw [Fintype.sum_eq_single w (fun x hx => by simp [Pi.single_eq_of_ne hx])]
    simp only [Pi.single_eq_same]
    rw [Fintype.sum_eq_single (p.1, q.1, p.2, q.2)]
    · simp [c, r, Function.surjInv_eq (hρ w)]
    · rintro ⟨i', k', a', b'⟩ hy
      simp only [c, r, Matrix.single_apply]
      split_ifs with h1
      · obtain ⟨rfl, rfl⟩ := h1
        rw [Function.surjInv_eq (hρ w), Matrix.single_apply, if_neg, smul_zero]
        rintro ⟨rfl, rfl⟩
        exact hy rfl
      · simp
  have hQne : ∀ w, Q w ≠ 0 := by
    intro w hQ
    set t0 : (Σ w : s, g × m × d w × d w) → O := fun j =>
      Pi.single (M := fun w => g × m × d w × d w → O) w
        (fun x => C0 w (x.1, x.2.2.1) (x.2.1, x.2.2.2)) j.1 j.2 with ht0
    have h1 := hevalQ w t0
    rw [hQ, map_zero] at h1
    have h2 : bigRect (ρ w) (∑ j, t0 j • c j) = C0 w := by
      rw [ht0, hsum]
    rw [h2] at h1
    exact (IsLocalRing.residue_ne_zero_iff_isUnit _).2 (hC0 w) h1.symm
  have hprod : (∏ w, Q w) ≠ 0 := Finset.prod_ne_zero_iff.2 (fun w _ => hQne w)
  obtain ⟨x, hx⟩ : ∃ x, MvPolynomial.eval x (∏ w, Q w) ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    exact hprod (MvPolynomial.funext fun x => by rw [hcon x, map_zero])
  rw [map_prod] at hx
  have hxw : ∀ w, MvPolynomial.eval x (Q w) ≠ 0 := fun w =>
    (Finset.prod_ne_zero_iff.1 hx) w (Finset.mem_univ w)
  let t : (Σ w : s, g × m × d w × d w) → O := fun j =>
    Function.surjInv (IsLocalRing.residue_surjective (R := O)) (x j)
  have htx : (fun j => res (t j)) = x := funext fun j => Function.surjInv_eq _ _
  refine ⟨∑ j, t j • c j, fun w => ?_⟩
  have hu : IsUnit (Matrix.of fun p q =>
      (bigRect (ρ w) (∑ j, t j • c j) * U w) (e w p) (f w q)).det := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, ← hevalQ w t, htx]
    exact hxw w
  show Module.length O (LinearMap.ker (relMap O (KO O) (bigMat (ρ w) (_ * P)))) = _
  rw [gen_bigMat_mul, hgood w _ hu]

end Formalism.NG
end
end

section
open Finset

noncomputable section

namespace Formalism.NG

lemma genfin_det_totalDegree {ι K n : Type*} [CommRing K] [Fintype n] [DecidableEq n]
    (A : Matrix n n (MvPolynomial ι K)) (h : ∀ i j, (A i j).totalDegree ≤ 1) :
    A.det.totalDegree ≤ Fintype.card n := by
  rw [Matrix.det_apply]
  refine (MvPolynomial.totalDegree_finset_sum _ _).trans (Finset.sup_le fun σ _ => ?_)
  have hprod : (∏ i, A (σ i) i).totalDegree ≤ Fintype.card n := by
    refine (MvPolynomial.totalDegree_finset_prod _ _).trans ?_
    calc ∑ i, (A (σ i) i).totalDegree ≤ ∑ _i : n, 1 := Finset.sum_le_sum fun i _ => h _ _
      _ = Fintype.card n := by simp
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
  · rw [hs, one_smul]
    exact hprod
  · rw [hs, Units.neg_smul, one_smul, MvPolynomial.totalDegree_neg]
    exact hprod

theorem genericFin : StatGenericFin := by
  intro R O _ _ _ _ _ m g s _ _ _ _ d _ _ hcard ρ hρ P
  classical
  have hk := fun w => gen_key (O := O) (bigRect (ρ w) P)
  choose n U f e hC0 hgood using hk
  choose C0 hC0 using hC0
  let res := IsLocalRing.residue O
  let r : ∀ w, d w → d w → R := fun w a b => Function.surjInv (hρ w) (Matrix.single a b 1)
  let c : (Σ w : s, g × m × d w × d w) → Matrix g m R := fun j =>
    Matrix.single j.2.1 j.2.2.1 (r j.1 j.2.2.2.1 j.2.2.2.2)
  let L : ∀ w, Matrix (g × d w) (m × d w) (MvPolynomial (Σ w : s, g × m × d w × d w)
      (IsLocalRing.ResidueField O)) := fun w p q =>
    ∑ j, MvPolynomial.X j * MvPolynomial.C (res (ρ w (c j p.1 q.1) p.2 q.2))
  let Q : s → MvPolynomial (Σ w : s, g × m × d w × d w) (IsLocalRing.ResidueField O) := fun w =>
    (Matrix.of fun p q => ∑ l, L w (e w p) l * MvPolynomial.C (res (U w l (f w q)))).det
  have hevalQ : ∀ w (t : (Σ w : s, g × m × d w × d w) → O),
      MvPolynomial.eval (fun j => res (t j)) (Q w) =
        res (Matrix.of fun p q => (bigRect (ρ w) (∑ j, t j • c j) * U w) (e w p) (f w q)).det := by
    intro w t
    simp only [Q]
    rw [RingHom.map_det, RingHom.map_det]
    congr 1
    ext p q
    simp [L, Matrix.mul_apply, bigRect, Matrix.sum_apply, map_sum]

  have hsum : ∀ w (φ : g × m × d w × d w → O),
      bigRect (ρ w) (∑ j : (Σ w : s, g × m × d w × d w),
        (Pi.single (M := fun w => g × m × d w × d w → O) w φ j.1 j.2) • c j) =
        fun p q => φ (p.1, q.1, p.2, q.2) := by
    intro w φ
    funext p q
    simp only [bigRect, Matrix.sum_apply, Matrix.smul_apply, map_sum, map_smul]
    rw [Fintype.sum_sigma]
    rw [Fintype.sum_eq_single w (fun x hx => by simp [Pi.single_eq_of_ne hx])]
    simp only [Pi.single_eq_same]
    rw [Fintype.sum_eq_single (p.1, q.1, p.2, q.2)]
    · simp [c, r, Function.surjInv_eq (hρ w)]
    · rintro ⟨i', k', a', b'⟩ hy
      simp only [c, r, Matrix.single_apply]
      split_ifs with h1
      · obtain ⟨rfl, rfl⟩ := h1
        rw [Function.surjInv_eq (hρ w), Matrix.single_apply, if_neg, smul_zero]
        rintro ⟨rfl, rfl⟩
        exact hy rfl
      · simp
  have hQne : ∀ w, Q w ≠ 0 := by
    intro w hQ
    set t0 : (Σ w : s, g × m × d w × d w) → O := fun j =>
      Pi.single (M := fun w => g × m × d w × d w → O) w
        (fun x => C0 w (x.1, x.2.2.1) (x.2.1, x.2.2.2)) j.1 j.2 with ht0
    have h1 := hevalQ w t0
    rw [hQ, map_zero] at h1
    have h2 : bigRect (ρ w) (∑ j, t0 j • c j) = C0 w := by
      rw [ht0, hsum]
    rw [h2] at h1
    exact (IsLocalRing.residue_ne_zero_iff_isUnit _).2 (hC0 w) h1.symm
  have hprod : (∏ w, Q w) ≠ 0 := Finset.prod_ne_zero_iff.2 (fun w _ => hQne w)

  have hL : ∀ w p q, (L w p q).totalDegree ≤ 1 := fun w p q =>
    MvPolynomial.totalDegree_finsetSum_le fun j _ => (MvPolynomial.totalDegree_mul _ _).trans
      (by rw [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_C])
  have hQdeg : ∀ w, (Q w).totalDegree ≤ Fintype.card g * Fintype.card (d w) := by
    intro w
    simp only [Q]
    refine (genfin_det_totalDegree _ fun p q => ?_).trans ?_
    · rw [Matrix.of_apply]
      exact MvPolynomial.totalDegree_finsetSum_le fun l _ => (MvPolynomial.totalDegree_mul _ _).trans
        (by rw [MvPolynomial.totalDegree_C, add_zero]; exact hL _ _ _)
    · rw [Fintype.card_fin, ← Fintype.card_prod]
      have he := Fintype.card_le_of_embedding (e w)
      rwa [Fintype.card_fin] at he
  set D : ℕ := Fintype.card g * ∑ w, Fintype.card (d w) with hD
  have hdeg : (∏ w, Q w).totalDegree ≤ D := by
    refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
    rw [hD, Finset.mul_sum]
    exact Finset.sum_le_sum fun w _ => hQdeg w

  obtain ⟨S, hS⟩ : ∃ S : Finset (IsLocalRing.ResidueField O), D < S.card := by
    rcases finite_or_infinite (IsLocalRing.ResidueField O) with hk | hk
    · cases nonempty_fintype (IsLocalRing.ResidueField O)
      refine ⟨Finset.univ, ?_⟩
      rw [Finset.card_univ]
      rw [Cardinal.mk_fintype, Nat.cast_lt] at hcard
      exact hcard
    · obtain ⟨S, hS⟩ := Infinite.exists_subset_card_eq (IsLocalRing.ResidueField O) (D + 1)
      exact ⟨S, by omega⟩

  obtain ⟨x, hx⟩ : ∃ x, MvPolynomial.eval x (∏ w, Q w) ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    exact hprod (MvPolynomial.eq_zero_of_eval_zero_at_prod_finset _ (fun _ => S)
      (fun i => lt_of_le_of_lt ((MvPolynomial.degreeOf_le_totalDegree _ i).trans hdeg) hS)
      (fun x _ => hcon x))
  rw [map_prod] at hx
  have hxw : ∀ w, MvPolynomial.eval x (Q w) ≠ 0 := fun w =>
    (Finset.prod_ne_zero_iff.1 hx) w (Finset.mem_univ w)
  let t : (Σ w : s, g × m × d w × d w) → O := fun j =>
    Function.surjInv (IsLocalRing.residue_surjective (R := O)) (x j)
  have htx : (fun j => res (t j)) = x := funext fun j => Function.surjInv_eq _ _
  refine ⟨∑ j, t j • c j, fun w => ?_⟩
  have hu : IsUnit (Matrix.of fun p q =>
      (bigRect (ρ w) (∑ j, t j • c j) * U w) (e w p) (f w q)).det := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, ← hevalQ w t, htx]
    exact hxw w
  show Module.length O (LinearMap.ker (relMap O (KO O) (bigMat (ρ w) (_ * P)))) = _
  rw [gen_bigMat_mul, hgood w _ hu]

section KerHomRectAux

variable {R : Type*} [Ring R] {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {m g d : Type} [Fintype m] [Fintype g] [DecidableEq g] [Fintype d] [DecidableEq d]
  (ρ : R →+* Matrix d d O) [SMulCommClass R O (LatQ O d ρ)]

theorem genfin_uncurry_relMap (P : Matrix m g R) (v : g → LatQ O d ρ) :
    uncurryEquiv (g := m) ρ (relMap O (LatQ O d ρ) P v) =
      relMap O (KO O) (fun (p : m × d) (q : g × d) => ρ (P p.1 q.1) p.2 q.2)
        (uncurryEquiv ρ v) := by
  funext p
  obtain ⟨i, a⟩ := p
  show (∑ j, P i j • v j : LatQ O d ρ) a = ∑ q : g × d, ρ (P i q.1) a q.2 • v q.1 q.2
  rw [Fintype.sum_prod_type]
  have hsum : (∑ j, P i j • v j : LatQ O d ρ) a = ∑ j, ((P i j • v j : LatQ O d ρ) : d → KO O) a :=
    Finset.sum_apply (M := fun _ : d => KO O) a univ (fun j => (P i j • v j : LatQ O d ρ))
  rw [hsum]
  rfl

theorem genfin_ker_map_uncurry (P : Matrix m g R) :
    (LinearMap.ker (relMap O (LatQ O d ρ) P)).map (uncurryEquiv (g := g) ρ).toLinearMap =
      LinearMap.ker (relMap O (KO O) (fun (p : m × d) (q : g × d) => ρ (P p.1 q.1) p.2 q.2)) := by
  ext w
  rw [Submodule.mem_map_equiv, LinearMap.mem_ker, LinearMap.mem_ker]
  constructor
  · intro h
    have := genfin_uncurry_relMap ρ P ((uncurryEquiv ρ).symm w)
    rw [h, map_zero, LinearEquiv.apply_symm_apply] at this
    exact this.symm
  · intro h
    have := genfin_uncurry_relMap ρ P ((uncurryEquiv ρ).symm w)
    rw [LinearEquiv.apply_symm_apply, h] at this
    exact (uncurryEquiv ρ).map_eq_zero_iff.mp this

end KerHomRectAux

theorem kerHomRect : StatKerHomRect := by
  intro R O _ _ _ _ m g d _ _ _ _ _ ρ _ P
  rw [(homEquiv (O := O) (M := LatQ O d ρ) P).length_eq]
  exact ((LinearEquiv.ofSubmodules (uncurryEquiv ρ) _ _ (genfin_ker_map_uncurry ρ P)).length_eq).symm

end Formalism.NG
end
end

section
open Finset

noncomputable section

namespace Formalism.NG


end Formalism.NG
end
end

section
open Finset

namespace Formalism.NG

theorem descent : StatDescent := by
  intro O _ X X' T T' Z p q b hexp hind f' hf' hvan π'
  obtain ⟨a, haT, rfl⟩ := hexp f' hf'
  have hker : ∀ k, (⟨a k, haT k⟩ : T) ∈ ccIdeal T Z := by
    intro k
    rw [ccIdeal, RingHom.mem_ker]
    funext x
    have hx : x.1 ∉ Z := x.2
    have h0 := hind x.1 hx (fun k => a k x.1) (fun x' hx' => by
      have e := hvan x' (by rw [hx']; exact hx)
      simpa [hx', Finset.sum_apply, Pi.mul_apply, Function.comp] using e)
    have e2 := congrFun h0 k
    simpa [resOff] using e2
  rw [Finset.sum_apply]
  refine Ideal.sum_mem _ fun k _ => ?_
  simp only [Pi.mul_apply, Function.comp_apply]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨_, hker k, rfl⟩)

theorem vccSpan : StatVccSpan := by
  intro O _ _ _ X T Z x y hy
  induction hy using Submodule.span_induction with
  | mem s hs =>
    obtain ⟨c, hc, rfl⟩ := hs
    exact iInf₂_le c hc
  | zero => simp
  | add a b _ _ ha hb =>
    exact le_trans (le_min ha hb) IsDiscreteValuationRing.addVal_add
  | smul r a _ ha =>
    rw [smul_eq_mul, IsDiscreteValuationRing.addVal_mul]
    exact le_trans ha le_add_self

end Formalism.NG
end

section
open Finset

noncomputable section

namespace Formalism.NG

namespace GlobalDeterminantRelations

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {X' : Type*}
  {d : Type} [Fintype d] [DecidableEq d] (R' : Subalgebra O (X' → Matrix d d (FractionRing O)))
  (x' : X')

lemma evalSp_smul (r : R') (v : EvalSp O d R' x') (a : d) :
    (r • v : d → FractionRing O) a =
      ∑ b, (r : X' → Matrix d d (FractionRing O)) x' a b * (v : d → FractionRing O) b := rfl

instance : SMulCommClass R' (FractionRing O) (EvalSp O d R' x') where
  smul_comm r c v := by
    funext a
    change (∑ b, (r : X' → Matrix d d (FractionRing O)) x' a b * (c * (v : d → FractionRing O) b)) =
      c * ∑ b, (r : X' → Matrix d d (FractionRing O)) x' a b * (v : d → FractionRing O) b
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring

instance : FiniteDimensional (FractionRing O) (EvalSp O d R' x') :=
  inferInstanceAs (FiniteDimensional (FractionRing O) (d → FractionRing O))

def curryE (g : Type) : (g × d → FractionRing O) ≃ₗ[FractionRing O] (g → EvalSp O d R' x') where
  toFun v i a := v (i, a)
  invFun w q := (w q.1 : d → FractionRing O) q.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

lemma det_relMap_eq (g : Type) [Fintype g] [DecidableEq g] (Θ : Matrix g g R') :
    LinearMap.det (relMap (FractionRing O) (EvalSp O d R' x') Θ) =
      (bigMat (fun r : R' => (r : X' → Matrix d d (FractionRing O)) x') Θ).det := by
  have hconj := LinearMap.det_conj (relMap (FractionRing O) (EvalSp O d R' x') Θ) (curryE R' x' g).symm
  rw [← hconj, ← LinearMap.det_toLin']
  congr 1
  apply LinearMap.ext
  intro v
  funext p
  obtain ⟨i, a⟩ := p
  let ev : EvalSp O d R' x' →+ FractionRing O :=
    { toFun := fun w => (w : d → FractionRing O) a
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  show ev (∑ j, Θ i j • (curryE R' x' g v) j) =
    Matrix.mulVec (bigMat (fun r : R' => (r : X' → Matrix d d (FractionRing O)) x') Θ) v (i, a)
  rw [map_sum]
  have hev : ∀ j, ev (Θ i j • (curryE R' x' g v) j) =
      ∑ b, (Θ i j : X' → Matrix d d (FractionRing O)) x' a b * v (j, b) := fun j =>
    evalSp_smul R' x' (Θ i j) ((curryE R' x' g v) j) a
  rw [Finset.sum_congr rfl (fun j _ => hev j), Matrix.mulVec]
  first
    | (rw [dotProduct, Fintype.sum_prod_type]; rfl)
    | (rw [Matrix.dotProduct, Fintype.sum_prod_type]; rfl)
    | (simp only [dotProduct, Fintype.sum_prod_type]; rfl)

end GlobalDeterminantRelations

universe u v w

open GlobalDeterminantRelations in
theorem globalConcrete_of (hD : StatDescent.{u, v, w}) (hV : StatVccSpan.{u, v}) :
    CharacterColumnGlobal.{u, v, w} := by
  intro O _ _ _ X X' T T' Z p q b hT hZ d _ _ R' m g _ _ _ P hdet hφ π' ρπ hρπ α _ _ bl hbl ρk
    hsurj hblk hcard
  classical
  obtain ⟨C, hC⟩ := genericFin R' O m g α (fun k => {a // bl a = k}) hcard ρk hsurj P
  obtain ⟨f, hfT, hf⟩ := hdet (C * P)
  have hcomp : ∀ (x' : X') (v : g → EvalSp O d R' x'),
      relMap (FractionRing O) (EvalSp O d R' x') (C * P) v =
        relMap (FractionRing O) (EvalSp O d R' x') C (relMap (FractionRing O) (EvalSp O d R' x') P v) := by
    intro x' v
    funext i
    show ∑ j, (C * P) i j • v j = ∑ l, C i l • ∑ j, P l j • v j
    simp only [Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, mul_smul]
    exact Finset.sum_comm
  have hvanish : ∀ x', p x' ∉ Z → f x' = 0 := by
    intro x' hx
    obtain ⟨φ, hφ0⟩ := hφ x' hx
    let e := (homEquiv P : (Coker P →ₗ[R'] EvalSp O d R' x') ≃ₗ[FractionRing O]
      LinearMap.ker (relMap (FractionRing O) (EvalSp O d R' x') P))
    have hne : e φ ≠ 0 := fun h => hφ0 (e.injective (h.trans (map_zero e).symm))
    have hv0 : ((e φ : LinearMap.ker _) : g → EvalSp O d R' x') ≠ 0 := fun h => hne (Subtype.ext h)
    have hvk := LinearMap.mem_ker.mp (e φ).2
    have hnot : ¬ Function.Injective (relMap (FractionRing O) (EvalSp O d R' x') (C * P)) := by
      intro hinj
      apply hv0
      apply hinj
      rw [hcomp, hvk, map_zero, map_zero]
    have hdet0 : LinearMap.det (relMap (FractionRing O) (EvalSp O d R' x') (C * P)) = 0 := by
      by_contra hne'
      apply hnot
      have hu : IsUnit (relMap (FractionRing O) (EvalSp O d R' x') (C * P)) :=
        (LinearMap.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hne')
      exact ((Module.End.isUnit_iff _).mp hu).injective
    rw [GlobalDeterminantRelations.det_relMap_eq] at hdet0
    apply IsFractionRing.injective O (FractionRing O)
    rw [hf x', hdet0, map_zero]
  have hspan := hD O X X' T T' Z p q b hT hZ f hfT hvanish π'
  refine (hV O X T Z (p π') (f π') hspan).trans (le_of_eq ?_)
  have hfπ : f π' = (bigMat (fun r : R' => ρπ r) (C * P)).det := by
    apply IsFractionRing.injective O (FractionRing O)
    rw [hf π', RingHom.map_det]
    congr 1
    refine Matrix.ext fun x y => ?_
    simp [bigMat, RingHom.mapMatrix_apply, ← hρπ]
  rcases isEmpty_or_nonempty g with hg | hg
  · have h1 : f π' = 1 := by
      rw [hfπ]
      exact Matrix.det_isEmpty
    rw [h1, IsDiscreteValuationRing.addVal_one]
    symm
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [Module.length_eq_zero_iff]
    exact ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
  have hBT : (bigMat (fun r : R' => ρπ r) (C * P)).BlockTriangular (fun x : g × d => bl x.2) := by
    intro x y hxy
    exact hbl _ hxy
  have himage : (Finset.univ.image fun x : g × d => bl x.2) = Finset.univ.image bl := by
    ext k
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨x.2, hx⟩
    · rintro ⟨a, ha⟩
      exact ⟨(Classical.arbitrary g, a), ha⟩
  have hprod : ∀ (s : Finset α) (F : α → O), IsDiscreteValuationRing.addVal O (∏ k ∈ s, F k) =
      ∑ k ∈ s, IsDiscreteValuationRing.addVal O (F k) := by
    intro s F
    refine Finset.induction_on s ?_ ?_
    · rw [Finset.prod_empty, Finset.sum_empty, IsDiscreteValuationRing.addVal_one]
    · intro a s ha ih
      rw [Finset.prod_insert ha, Finset.sum_insert ha, IsDiscreteValuationRing.addVal_mul, ih]
  have hblock : ∀ k, ((bigMat (fun r : R' => ρπ r) (C * P)).toSquareBlock
      (fun x : g × d => bl x.2) k).det = (bigMat (fun r : R' => ρk k r) (C * P)).det := by
    intro k
    let eK : g × {a // bl a = k} ≃ {x : g × d // bl x.2 = k} :=
      { toFun := fun y => ⟨(y.1, y.2.1), y.2.2⟩
        invFun := fun x => (x.1.1, ⟨x.1.2, x.2⟩)
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [← Matrix.det_reindex_self eK.symm]
    congr 1
    refine Matrix.ext fun x y => ?_
    obtain ⟨pp, i⟩ := x
    obtain ⟨qq, j⟩ := y
    show _ = (ρk k) ((C * P) pp qq) i j
    rw [← hblk]
    rfl
  rw [hfπ, hBT.det, hprod, himage]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hblock k, ← (lenKer : StatLenKer) O _ (bigMat (fun r : R' => ρk k r) (C * P))]
  exact hC k

theorem globalConcrete : CharacterColumnGlobal := globalConcrete_of descent vccSpan

end Formalism.NG
end
end
