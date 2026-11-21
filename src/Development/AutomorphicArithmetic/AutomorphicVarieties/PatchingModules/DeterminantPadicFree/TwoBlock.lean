import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.LatInt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.SelfdualRamified
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.OrthonormalLocal
import Mathlib.RingTheory.PowerSeries.Ideal
import Mathlib.RingTheory.AdicCompletion.Completeness

section
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem henselian_powerSeries (K : Type) [Field K] : HenselianLocalRing (PowerSeries K) := by
  have hR : HenselianRing (PowerSeries K) (Ideal.span {PowerSeries.X}) := inferInstance
  refine { toIsLocalRing := inferInstance, is_henselian := fun f hf a₀ h₁ h₂ => ?_ }
  rw [PowerSeries.maximalIdeal_eq_span_X] at h₁ ⊢
  exact hR.is_henselian f hf a₀ h₁ (h₂.map _)

private theorem coe_generalLinearGroup_map_eq_map {R S : Type} [CommRing R] [CommRing S] {m : ℕ} (f : R →+* S)
    (g : GL (Fin m) R) :
    ((GeneralLinearGroup.map f g : GL (Fin m) S) : Matrix (Fin m) (Fin m) S) =
      (g : Matrix (Fin m) (Fin m) R).map f := by
  ext i j
  exact GeneralLinearGroup.map_apply f i j g

private theorem map_transpose_mul_mul_eq {R S : Type} [CommRing R] [CommRing S] {m : ℕ} (φ : R →+* S)
    (X Y Z : Matrix (Fin m) (Fin m) R) :
    (Xᵀ * Y * Z).map φ = (X.map φ)ᵀ * Y.map φ * Z.map φ := by
  simp [Matrix.map_mul, Matrix.transpose_map]

theorem UpperTheory.V.Pa.Det.oneBlock :
    ∀ {K K' G : Type} [Field K] [Field K'] [Group G] {m : ℕ} (j₁ : PowerSeries K →+* PowerSeries K) (f₁ : FractionRing (PowerSeries K) →+* FractionRing (PowerSeries K)) (j₂ : PowerSeries K →+* PowerSeries K') (f₂ : FractionRing (PowerSeries K) →+* FractionRing (PowerSeries K')) (r : G →* GL (Fin m) (FractionRing (PowerSeries K))) (H : Matrix (Fin m) (Fin m) (FractionRing (PowerSeries K))) (σ : G → G) (u : G → PowerSeries K) (d : PowerSeries K), (2 : K) ≠ 0 → (∀ y, f₁ (algebraMap _ _ y) = algebraMap _ _ (j₁ y)) → (∀ y, f₂ (algebraMap _ _ y) = algebraMap _ _ (j₂ y)) → j₁ PowerSeries.X = PowerSeries.X ^ 2 → (∀ c : (PowerSeries K)ˣ, IsSquare (residue (PowerSeries K') (j₂ c))) → d ≠ 0 → (∀ g i i', ∃ y : PowerSeries K, algebraMap _ (FractionRing (PowerSeries K)) d * r g i i' = algebraMap _ (FractionRing (PowerSeries K)) y) → Hᵀ = H → H.det ≠ 0 → Function.Surjective σ → (∀ g, (mat r g)ᵀ * H * mat r (σ g) = algebraMap _ (FractionRing (PowerSeries K)) (u g) • H) → ∃ (Q : GL (Fin m) (FractionRing (PowerSeries K'))) (r' : G →* GL (Fin m) (PowerSeries K')), (Q : Matrix (Fin m) (Fin m) (FractionRing (PowerSeries K')))ᵀ * H.map (f₂.comp f₁) * Q = 1 ∧ (∀ g, pushRep (f₂.comp f₁) r g * Q = Q * pushRep (algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))) r' g) := by
  intro K K' G _ _ _ m j₁ f₁ j₂ f₂ r H σ u d h2 hf₁ hf₂ hj₁ hsq hd hdr hHs hdet hσ hsim
  obtain ⟨Q₀, r₀, hQ₀⟩ := Det.latInt r d hd hdr
  have hQ₀m : ∀ g, (r g).1 * Q₀.1 =
      Q₀.1 * (r₀ g).1.map (algebraMap _ _) := by
    intro g
    have := congr_arg Units.val (hQ₀ g)
    simpa only [Units.val_mul, pushRep, MonoidHom.comp_apply, coe_generalLinearGroup_map_eq_map] using this
  obtain ⟨H₁, hH₁⟩ : ∃ H₁ : Matrix (Fin m) (Fin m) (FractionRing (PowerSeries K)),
      H₁ = Q₀.1ᵀ * H * Q₀ := ⟨_, rfl⟩
  have hH₁s : H₁ᵀ = H₁ := by
    rw [hH₁, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hHs, Matrix.mul_assoc]
  have hQdet : Q₀.1.det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 Q₀.isUnit).ne_zero
  have hH₁det : H₁.det ≠ 0 := by
    rw [hH₁, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    exact mul_ne_zero (mul_ne_zero hQdet hdet) hQdet
  have hsim₀ : ∀ g, ((r₀ g).1.map
      (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))))ᵀ * H₁ *
      (r₀ (σ g)).1.map
      (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))) =
      algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) (u g) • H₁ := by
    intro g
    have key := hsim g
    simp only [mat, MonoidHom.comp_apply, Units.coeHom_apply] at key
    rw [hH₁]
    calc _ = (Q₀.1 *
            (r₀ g).1.map (algebraMap _ _))ᵀ * H *
          (Q₀.1 *
            (r₀ (σ g)).1.map (algebraMap _ _)) := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = ((r g).1 * Q₀.1)ᵀ * H *
          ((r (σ g)).1 * Q₀.1) := by
          rw [← hQ₀m, ← hQ₀m]
      _ = Q₀.1ᵀ *
          ((r g).1ᵀ * H *
            (r (σ g)).1) * Q₀.1 := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = _ := by rw [key, Matrix.mul_smul, Matrix.smul_mul]
  obtain ⟨P, H', r', hP, hr'⟩ := UpperTheory.V.AlgebraTools.selfdual_ramified (A := PowerSeries K)
    (F := FractionRing (PowerSeries K)) H₁ r₀ σ u (A' := PowerSeries K)
    (F' := FractionRing (PowerSeries K)) j₁ f₁ PowerSeries.X PowerSeries.X PowerSeries.X_irreducible
    hj₁.symm hf₁ (IsFractionRing.injective _ _) hH₁s hH₁det hσ hsim₀
  have h2u : IsUnit (2 : PowerSeries K) := by
    rw [← map_ofNat (PowerSeries.C (R := K)) 2]
    exact (isUnit_iff_ne_zero.2 h2).map _
  have hH's : H'.1ᵀ = H' := by
    have e : (H'.1.map
        (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))))ᵀ =
        H'.1.map (algebraMap _ _) := by
      rw [← hP, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
        ← Matrix.transpose_map, hH₁s, Matrix.mul_assoc]
    refine Matrix.ext fun i j => ?_
    exact IsFractionRing.injective _ (FractionRing (PowerSeries K)) (congr_fun (congr_fun e i) j)
  have hH'det : IsUnit H'.1.det :=
    (Matrix.isUnit_iff_isUnit_det _).1 H'.isUnit
  haveI := henselian_powerSeries K'
  obtain ⟨P₂, hP₂⟩ := UpperTheory.V.AlgebraTools.orthonormal_local j₂ H'.1
    h2u hH's hH'det hsq
  refine ⟨GeneralLinearGroup.map (f₂.comp f₁) Q₀ * GeneralLinearGroup.map f₂ P *
      GeneralLinearGroup.map (algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))) P₂,
    (MulAut.conj P₂⁻¹).toMonoidHom.comp (pushRep j₂ r'), ?_, ?_⟩
  · have s1 : (Q₀.1.map (f₂.comp f₁))ᵀ *
        H.map (f₂.comp f₁) * Q₀.1.map (f₂.comp f₁) =
        (H₁.map f₁).map f₂ := by
      rw [← map_transpose_mul_mul_eq, ← hH₁, Matrix.map_map]
      rfl
    have s2 : (P.1.map f₂)ᵀ * (H₁.map f₁).map f₂ *
        P.1.map f₂ =
        (H'.1.map j₂).map
          (algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))) := by
      rw [← map_transpose_mul_mul_eq, hP, Matrix.map_map, Matrix.map_map]
      congr 1
      funext a
      exact hf₂ a
    have s3 : (P₂.1.map
        (algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))))ᵀ *
        (H'.1.map j₂).map
          (algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))) *
        P₂.1.map
          (algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))) = 1 := by
      rw [← map_transpose_mul_mul_eq, hP₂, Matrix.map_one _ (map_zero _) (map_one _)]
    rw [Units.val_mul, Units.val_mul, coe_generalLinearGroup_map_eq_map, coe_generalLinearGroup_map_eq_map, coe_generalLinearGroup_map_eq_map]
    rw [← s3, ← s2, ← s1]
    simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  · intro g
    have t1 := congr_arg (GeneralLinearGroup.map (f₂.comp f₁)) (hQ₀ g)
    rw [map_mul, map_mul] at t1
    have t2 : GeneralLinearGroup.map (f₂.comp f₁) (GeneralLinearGroup.map (algebraMap (PowerSeries K)
        (FractionRing (PowerSeries K))) (r₀ g)) * GeneralLinearGroup.map f₂ P =
        GeneralLinearGroup.map f₂ P * GeneralLinearGroup.map
          (algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))) (GeneralLinearGroup.map j₂ (r' g)) := by
      apply Units.ext
      have t2m := congr_arg (fun M => Matrix.map M f₂) (hr' g)
      simp only [Matrix.map_mul, Matrix.map_map] at t2m
      simp only [Units.val_mul, pushRep, MonoidHom.comp_apply, coe_generalLinearGroup_map_eq_map, Matrix.map_map]
      have fe1 : (⇑(f₂.comp f₁) ∘ ⇑(algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))) =
          (⇑f₂ ∘ fun a => algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) (j₁ a)) :=
        funext fun a => by simp [hf₁]
      have fe2 : (⇑(algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))) ∘ ⇑j₂) =
          (⇑f₂ ∘ ⇑(algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))) :=
        funext fun a => by simp [hf₂]
      rw [fe1, fe2]
      exact t2m
    simp only [pushRep, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MulAut.conj_inv_apply, map_mul, map_inv,
      inv_inv] at t1 ⊢
    calc _ = (GeneralLinearGroup.map (f₂.comp f₁) (r g) * GeneralLinearGroup.map (f₂.comp f₁) Q₀) *
          GeneralLinearGroup.map f₂ P *
          GeneralLinearGroup.map (algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))) P₂ := by
          simp only [mul_assoc]
      _ = _ := by
          rw [t1, mul_assoc (GeneralLinearGroup.map (f₂.comp f₁) Q₀), t2]
          group
end

section
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

section Blocks

variable {R S : Type} [CommRing R] [CommRing S] {a b : ℕ}

private def bd (A : Matrix (Fin a) (Fin a) R) (D : Matrix (Fin b) (Fin b) R) :
    Matrix (Fin (a + b)) (Fin (a + b)) R :=
  (fromBlocks A 0 0 D).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

private theorem bd_mul (A A' : Matrix (Fin a) (Fin a) R) (D D' : Matrix (Fin b) (Fin b) R) :
    bd A D * bd A' D' = bd (A * A') (D * D') := by
  simp [bd, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

private theorem bd_one : bd (1 : Matrix (Fin a) (Fin a) R) (1 : Matrix (Fin b) (Fin b) R) = 1 := by
  simp [bd]

private theorem bd_transpose (A : Matrix (Fin a) (Fin a) R) (D : Matrix (Fin b) (Fin b) R) :
    (bd A D)ᵀ = bd Aᵀ Dᵀ := by
  simp [bd, Matrix.transpose_submatrix, Matrix.fromBlocks_transpose]

private theorem bd_map (f : R →+* S) (A : Matrix (Fin a) (Fin a) R) (D : Matrix (Fin b) (Fin b) R) :
    (bd A D).map f = bd (A.map f) (D.map f) := by
  unfold bd
  rw [← Matrix.submatrix_map, Matrix.fromBlocks_map]
  simp

private theorem bd_smul (c : R) (A : Matrix (Fin a) (Fin a) R) (D : Matrix (Fin b) (Fin b) R) :
    c • bd A D = bd (c • A) (c • D) := by
  unfold bd
  ext i j
  simp only [Matrix.smul_apply, Matrix.submatrix_apply]
  generalize finSumFinEquiv.symm i = x
  generalize finSumFinEquiv.symm j = y
  rcases x with x | x <;> rcases y with y | y <;> simp

private theorem bd_ll (A : Matrix (Fin a) (Fin a) R) (D : Matrix (Fin b) (Fin b) R) (i j : Fin a) :
    bd A D (Fin.castAdd b i) (Fin.castAdd b j) = A i j := by
  simp [bd]

private theorem bd_rr (A : Matrix (Fin a) (Fin a) R) (D : Matrix (Fin b) (Fin b) R) (i j : Fin b) :
    bd A D (Fin.natAdd a i) (Fin.natAdd a j) = D i j := by
  simp [bd]

private theorem bd_inj {A A' : Matrix (Fin a) (Fin a) R} {D D' : Matrix (Fin b) (Fin b) R}
    (h : bd A D = bd A' D') : A = A' ∧ D = D' := by
  constructor
  · ext i j; rw [← bd_ll A D, h, bd_ll]
  · ext i j; rw [← bd_rr A D, h, bd_rr]

private theorem bd_det (A : Matrix (Fin a) (Fin a) R) (D : Matrix (Fin b) (Fin b) R) :
    (bd A D).det = A.det * D.det := by
  simp [bd]

private theorem bd_mem (A : Matrix (Fin a) (Fin a) R) (D : Matrix (Fin b) (Fin b) R) :
    bd A D ∈ Ev R R (a + b) a := by
  intro i j
  refine ⟨fun _ => trivial, fun h => ?_⟩
  rw [Submodule.mem_bot]
  induction i using Fin.addCases <;> induction j using Fin.addCases <;> simp [bd] at h ⊢

private theorem bd_ex {M : Matrix (Fin (a + b)) (Fin (a + b)) R} (h : M ∈ Ev R R (a + b) a) :
    ∃ A D, M = bd A D := by
  refine ⟨M.submatrix (Fin.castAdd b) (Fin.castAdd b), M.submatrix (Fin.natAdd a) (Fin.natAdd a), ?_⟩
  ext i j
  have h' := (h i j).2
  rw [Submodule.mem_bot] at h'
  induction i using Fin.addCases <;> induction j using Fin.addCases <;> simp [bd] at h' ⊢ <;> exact h'

private def bdU (A : GL (Fin a) R) (D : GL (Fin b) R) : GL (Fin (a + b)) R :=
  ⟨bd A.val D.val, bd A⁻¹.val D⁻¹.val, by rw [bd_mul, Units.mul_inv, Units.mul_inv, bd_one],
    by rw [bd_mul, Units.inv_mul, Units.inv_mul, bd_one]⟩

private def bdRep {G : Type} [Group G] (r₁ : G →* GL (Fin a) R) (r₂ : G →* GL (Fin b) R) :
    G →* GL (Fin (a + b)) R where
  toFun g := bdU (r₁ g) (r₂ g)
  map_one' := Units.ext (by
    show bd (r₁ 1).val (r₂ 1).val = 1
    rw [map_one, map_one, Units.val_one, Units.val_one, bd_one])
  map_mul' g h := Units.ext (by
    show bd (r₁ (g * h)).val (r₂ (g * h)).val = bd (r₁ g).val (r₂ g).val * bd (r₁ h).val (r₂ h).val
    rw [map_mul, map_mul, Units.val_mul, Units.val_mul, bd_mul])

private theorem rep_ex {G : Type} [Group G] (r : G →* GL (Fin (a + b)) R)
    (h : ∀ g, mat r g ∈ Ev R R (a + b) a) :
    ∃ (r₁ : G →* GL (Fin a) R) (r₂ : G →* GL (Fin b) R), ∀ g, (r g).val = bd (r₁ g).val (r₂ g).val := by
  choose A D hAD using fun g => bd_ex (h g)
  have h1 : bd (A 1) (D 1) = bd 1 1 := by rw [← hAD, map_one, bd_one]
  have hm : ∀ g g', bd (A (g * g')) (D (g * g')) = bd (A g * A g') (D g * D g') := fun g g' => by
    rw [← bd_mul, ← hAD, ← hAD, ← hAD, map_mul]
  let A' : G →* Matrix (Fin a) (Fin a) R := ⟨⟨A, (bd_inj h1).1⟩, fun g g' => (bd_inj (hm g g')).1⟩
  let D' : G →* Matrix (Fin b) (Fin b) R := ⟨⟨D, (bd_inj h1).2⟩, fun g g' => (bd_inj (hm g g')).2⟩
  exact ⟨A'.toHomUnits, D'.toHomUnits, fun g => hAD g⟩

end Blocks

theorem UpperTheory.V.Pa.Det.twoBlock :
    ∀ {K K' G : Type} [Field K] [Field K'] [Group G] {n : ℕ} (a : ℕ) (j₁ : PowerSeries K →+* PowerSeries K) (f₁ : FractionRing (PowerSeries K) →+* FractionRing (PowerSeries K)) (j₂ : PowerSeries K →+* PowerSeries K') (f₂ : FractionRing (PowerSeries K) →+* FractionRing (PowerSeries K')) (r : G →* GL (Fin n) (FractionRing (PowerSeries K))) (H : Matrix (Fin n) (Fin n) (FractionRing (PowerSeries K))) (σ : G → G) (u : G → PowerSeries K) (d : PowerSeries K), (2 : K) ≠ 0 → (∀ y, f₁ (algebraMap _ _ y) = algebraMap _ _ (j₁ y)) → (∀ y, f₂ (algebraMap _ _ y) = algebraMap _ _ (j₂ y)) → j₁ PowerSeries.X = PowerSeries.X ^ 2 → (∀ c : (PowerSeries K)ˣ, IsSquare (residue (PowerSeries K') (j₂ c))) → d ≠ 0 → (∀ g i i', ∃ y : PowerSeries K, algebraMap _ (FractionRing (PowerSeries K)) d * r g i i' = algebraMap _ (FractionRing (PowerSeries K)) y) → Hᵀ = H → H.det ≠ 0 → Function.Surjective σ → (∀ g, (mat r g)ᵀ * H * mat r (σ g) = algebraMap _ (FractionRing (PowerSeries K)) (u g) • H) → a ≤ n → (∀ g, mat r g ∈ Ev (FractionRing (PowerSeries K)) (FractionRing (PowerSeries K)) n a) → H ∈ Ev (FractionRing (PowerSeries K)) (FractionRing (PowerSeries K)) n a → ∃ (Q : GL (Fin n) (FractionRing (PowerSeries K'))) (r' : G →* GL (Fin n) (PowerSeries K')), (Q : Matrix (Fin n) (Fin n) (FractionRing (PowerSeries K')))ᵀ * H.map (f₂.comp f₁) * Q = 1 ∧ (∀ g, pushRep (f₂.comp f₁) r g * Q = Q * pushRep (algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))) r' g) ∧ (Q : Matrix (Fin n) (Fin n) (FractionRing (PowerSeries K'))) ∈ Ev (FractionRing (PowerSeries K')) (FractionRing (PowerSeries K')) n a ∧ ∀ g, mat r' g ∈ Ev (PowerSeries K') (PowerSeries K') n a := by
  intro K K' G _ _ _ n a j₁ f₁ j₂ f₂ r H σ u d h2 hf₁ hf₂ hX hsq hd hb hH hdet hσ hr ha hev hHev
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le ha
  obtain ⟨H₁, H₂, rfl⟩ := bd_ex hHev
  obtain ⟨r₁, r₂, hrr⟩ := rep_ex r hev
  rw [bd_transpose] at hH
  rw [bd_det] at hdet
  have hr' : ∀ g, bd ((mat r₁ g)ᵀ * H₁ * mat r₁ (σ g)) ((mat r₂ g)ᵀ * H₂ * mat r₂ (σ g)) =
      bd (algebraMap _ (FractionRing (PowerSeries K)) (u g) • H₁)
        (algebraMap _ (FractionRing (PowerSeries K)) (u g) • H₂) := fun g => by
    rw [← bd_smul, ← hr g, ← bd_mul, ← bd_mul, ← bd_transpose]
    show _ = ((r g).val)ᵀ * _ * (r (σ g)).val
    rw [hrr, hrr]
    rfl
  obtain ⟨Q₁, s₁, hQ₁, hs₁⟩ := UpperTheory.V.Pa.Det.oneBlock j₁ f₁ j₂ f₂ r₁ H₁ σ u d h2 hf₁ hf₂ hX hsq hd
    (fun g i i' => by
      obtain ⟨y, hy⟩ := hb g (Fin.castAdd b i) (Fin.castAdd b i')
      refine ⟨y, ?_⟩
      rw [← hy]
      show _ * (r₁ g).val i i' = _ * (r g).val _ _
      rw [hrr, bd_ll])
    (bd_inj hH).1 (left_ne_zero_of_mul hdet) hσ (fun g => (bd_inj (hr' g)).1)
  obtain ⟨Q₂, s₂, hQ₂, hs₂⟩ := UpperTheory.V.Pa.Det.oneBlock j₁ f₁ j₂ f₂ r₂ H₂ σ u d h2 hf₁ hf₂ hX hsq hd
    (fun g i i' => by
      obtain ⟨y, hy⟩ := hb g (Fin.natAdd a i) (Fin.natAdd a i')
      refine ⟨y, ?_⟩
      rw [← hy]
      show _ * (r₂ g).val i i' = _ * (r g).val _ _
      rw [hrr, bd_rr])
    (bd_inj hH).2 (right_ne_zero_of_mul hdet) hσ (fun g => (bd_inj (hr' g)).2)
  refine ⟨bdU Q₁ Q₂, bdRep s₁ s₂, ?_, fun g => Units.ext ?_, bd_mem _ _, fun g => bd_mem _ _⟩
  · show (bd Q₁.val Q₂.val)ᵀ * _ * bd Q₁.val Q₂.val = 1
    rw [bd_map, bd_transpose, bd_mul, bd_mul, hQ₁, hQ₂, bd_one]
  · have e₁ : (r₁ g).val.map (f₂.comp f₁) * Q₁.val = Q₁.val * (s₁ g).val.map (algebraMap _ _) :=
      congrArg Units.val (hs₁ g)
    have e₂ : (r₂ g).val.map (f₂.comp f₁) * Q₂.val = Q₂.val * (s₂ g).val.map (algebraMap _ _) :=
      congrArg Units.val (hs₂ g)
    show (r g).val.map (f₂.comp f₁) * bd Q₁.val Q₂.val =
      bd Q₁.val Q₂.val * (bd (s₁ g).val (s₂ g).val).map (algebraMap _ (FractionRing (PowerSeries K')))
    rw [hrr, bd_map, bd_map, bd_mul, bd_mul, e₁, e₂]
end
