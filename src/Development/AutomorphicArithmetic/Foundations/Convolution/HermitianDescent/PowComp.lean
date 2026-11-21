import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.NmPoly
import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.SeparableOfMap
import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.GalBase
import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.ConjSep

section
open Matrix Polynomial NumberField IsDedekindDomain
open scoped TensorProduct

namespace UpperTheory.ConvolutionTheory.D

section

variable {k R : Type} [CommRing k] [CommRing R] [Algebra k R] {n : ℕ}

private theorem cent_sg_up (σ : R ≃ₐ[k] R) (γ : GL (Fin n) k) : sg σ (up R γ) = up R γ := by
  ext a b
  simp [sg, up, Matrix.GeneralLinearGroup.map_apply]

private theorem cent_nm_sg (σ : R ≃ₐ[k] R) (q : ℕ) (d : GL (Fin n) R) :
    nm σ q (sg σ d) = sg σ (nm σ q d) := by
  unfold nm
  rw [map_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun m _ => ?_
  ext a b
  change (σ ^ m) (σ _) = σ ((σ ^ m) _)
  rw [← AlgEquiv.mul_apply, ← AlgEquiv.mul_apply, ← pow_succ, ← pow_succ']

private theorem cent_up_inj (h : Function.Injective (algebraMap k R)) :
    Function.Injective (up R : GL (Fin n) k → GL (Fin n) R) := by
  intro s t hst
  ext a b
  exact h (congrArg (fun g : GL (Fin n) R => (g : Matrix (Fin n) (Fin n) R) a b) hst)

private theorem cent_descend {σ : R ≃ₐ[k] R} {q : ℕ} (hσ : IsGal σ q) (x : GL (Fin n) R) (hx : sg σ x = x) :
    ∃ t : GL (Fin n) k, x = up R t := by
  have key : ∀ y : GL (Fin n) R, sg σ y = y → ∃ M : Matrix (Fin n) (Fin n) k,
      M.map (algebraMap k R) = (y : Matrix (Fin n) (Fin n) R) := by
    intro y hy
    have h : ∀ a b, ∃ c, algebraMap k R c = (y : Matrix (Fin n) (Fin n) R) a b := fun a b =>
      hσ.fix _ (congrArg (fun g : GL (Fin n) R => (g : Matrix (Fin n) (Fin n) R) a b) hy)
    choose M hM using h
    exact ⟨Matrix.of M, by ext a b; exact hM a b⟩
  obtain ⟨M, hM⟩ := key x hx
  obtain ⟨N, hN⟩ := key x⁻¹ (by rw [map_inv, hx])
  have inj := Matrix.map_injective (m := Fin n) (n := Fin n) hσ.inj
  refine ⟨⟨M, N, inj ?_, inj ?_⟩, Units.ext hM.symm⟩
  · dsimp only
    rw [Matrix.map_mul, hM, hN, Matrix.map_one _ (map_zero _) (map_one _), Units.mul_inv]
  · dsimp only
    rw [Matrix.map_mul, hM, hN, Matrix.map_one _ (map_zero _) (map_one _), Units.inv_mul]

end

end UpperTheory.ConvolutionTheory.D

theorem UpperTheory.ConvolutionTheory.D.nmCent :
    UpperTheory.ConvolutionTheory.D.NmCent := by
  intro k R _ _ _ _ σ q hσ n a γ hsep ha x
  haveI : Module.Finite k R := (galBase k R k σ q hσ).1
  have hs : ((up R γ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R).charpoly.Separable := by
    have h := hsep.map (f := algebraMap k R)
    rw [cp, ← Matrix.charpoly_map] at h
    exact h
  have hc := (conjSep k R n _ hs).2.1
  have hfix : ∀ y, nm σ q (sgConj σ y a) = up R γ → y * up R γ = up R γ * y := by
    intro y hy
    rw [(nmPoly k R σ q hσ n a).2 y, ha, mul_assoc, inv_mul_eq_iff_eq_mul] at hy
    exact hy.symm
  have hag : a * up R γ = up R γ * a := by
    apply hfix
    rw [sgConj, inv_mul_cancel, one_mul, cent_nm_sg, ha, cent_sg_up]
  have hcomm : ∀ y : GL (Fin n) R, y * up R γ = up R γ * y → a * y = y * a := by
    intro y hy
    obtain ⟨p, hp⟩ := hc a.val (by simpa using congrArg Units.val hag)
    obtain ⟨p', hp'⟩ := hc y.val (by simpa using congrArg Units.val hy)
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hp, hp', ← map_mul, ← map_mul, mul_comm]
  constructor
  · intro hx
    have h1 := hfix x (by rw [hx, ha])
    have h2 := hcomm x h1
    have h3 : sg σ x = x := by
      rw [sgConj, mul_assoc, inv_mul_eq_iff_eq_mul, ← h2] at hx
      exact mul_left_cancel hx
    obtain ⟨t, rfl⟩ := cent_descend hσ x h3
    refine ⟨t, cent_up_inj hσ.inj ?_, rfl⟩
    rw [map_mul, map_mul, h1]
  · rintro ⟨t, ht, rfl⟩
    have h2 := hcomm (up R t) (by rw [← map_mul, ← map_mul, ht.eq])
    rw [sgConj, cent_sg_up, mul_assoc, h2, inv_mul_cancel_left]
end

section
open Matrix Polynomial NumberField IsDedekindDomain
open scoped TensorProduct

namespace UpperTheory.ConvolutionTheory.D

private theorem cp_map {S R : Type} [CommRing S] [CommRing R] {n : ℕ} (j : S →+* R) (g : GL (Fin n) S) :
    cp (Matrix.GeneralLinearGroup.map j g) = (cp g).map j := by
  unfold cp
  rw [← Matrix.charpoly_map]
  rfl

private theorem cp_conj {R : Type} [CommRing R] {n : ℕ} (x g : GL (Fin n) R) :
    cp (x⁻¹ * g * x) = cp g := by
  unfold cp
  rw [Units.val_mul, Matrix.charpoly_mul_comm, ← Units.val_mul, ← mul_assoc, mul_inv_cancel, one_mul]

section
variable {O S k R : Type} [CommRing O] [CommRing S] [Algebra O S] [CommRing k] [CommRing R] [Algebra k R] {n : ℕ}

private theorem map_sg (j : S →+* R) (s : S ≃ₐ[O] S) (σ : R ≃ₐ[k] R) (h : ∀ x, j (s x) = σ (j x))
    (g : GL (Fin n) S) :
    Matrix.GeneralLinearGroup.map j (sg s g) = sg σ (Matrix.GeneralLinearGroup.map j g) := by
  ext a b
  exact h _

private theorem pow_comp (j : S →+* R) (s : S ≃ₐ[O] S) (σ : R ≃ₐ[k] R) (h : ∀ x, j (s x) = σ (j x))
    (m : ℕ) : ∀ x, j ((s ^ m) x) = (σ ^ m) (j x) := by
  induction m with
  | zero => intro x; rfl
  | succ m ih => intro x; rw [pow_succ, pow_succ, AlgEquiv.mul_apply, AlgEquiv.mul_apply, ih, h]

private theorem map_nm (j : S →+* R) (s : S ≃ₐ[O] S) (σ : R ≃ₐ[k] R) (h : ∀ x, j (s x) = σ (j x))
    (q : ℕ) (g : GL (Fin n) S) :
    Matrix.GeneralLinearGroup.map j (nm s q g) = nm σ q (Matrix.GeneralLinearGroup.map j g) := by
  unfold nm
  rw [map_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun m _ => ?_
  exact map_sg j (s ^ m) (σ ^ m) (pow_comp j s σ h m) g

private theorem map_up (i : O →+* k) (j : S →+* R) (h : ∀ x, j (algebraMap O S x) = algebraMap k R (i x))
    (g : GL (Fin n) O) :
    Matrix.GeneralLinearGroup.map j (up S g) = up R (Matrix.GeneralLinearGroup.map i g) := by
  ext a b
  exact h _

end

end UpperTheory.ConvolutionTheory.D

theorem UpperTheory.ConvolutionTheory.D.nmInt :
    UpperTheory.ConvolutionTheory.D.NmInt := by
  intro O S k R _ _ _ _ _ _ _ i j s σ q hs hσ hj hjs hji n a a' γ hγ ha x hx
  have h1 : cp (nm s q a') = cp (nm s q a) := by
    apply Polynomial.map_injective j hj
    rw [← cp_map, ← cp_map, map_nm j s σ hjs, map_nm j s σ hjs, ← hx,
      (nmPoly k R σ q hσ n _).2, cp_conj]
  have h2 : (cp (nm s q a)).Separable := by
    rw [ha, up, cp_map]
    exact hγ.map
  obtain ⟨u, hu⟩ := nmInj O S s q hs n a a' h2 h1
  have h3 : (cp (Matrix.GeneralLinearGroup.map i γ)).Separable := by
    rw [cp_map]
    exact hγ.map
  have h4 : nm σ q (Matrix.GeneralLinearGroup.map j a) = up R (Matrix.GeneralLinearGroup.map i γ) := by
    rw [← map_nm j s σ hjs, ha, map_up i j hji]
  have h5 : sgConj σ (x * (Matrix.GeneralLinearGroup.map j u)⁻¹) (Matrix.GeneralLinearGroup.map j a) =
      Matrix.GeneralLinearGroup.map j a := by
    rw [hu, sgConj, sgConj, map_mul, map_mul, map_inv, map_sg j s σ hjs] at hx
    rw [sgConj, map_mul, map_inv]
    calc _ = Matrix.GeneralLinearGroup.map j u * (x⁻¹ * Matrix.GeneralLinearGroup.map j a * sg σ x) *
          (sg σ (Matrix.GeneralLinearGroup.map j u))⁻¹ := by group
      _ = _ := by rw [hx]; group
  obtain ⟨t, ht, hxt⟩ := (nmCent k R σ q hσ n _ _ h3 h4 _).1 h5
  exact ⟨t, u, ht, by rw [← hxt]; group⟩
end
