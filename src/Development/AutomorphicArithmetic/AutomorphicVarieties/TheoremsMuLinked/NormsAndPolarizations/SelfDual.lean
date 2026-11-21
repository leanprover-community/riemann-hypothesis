import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.CjApply
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.SelmerDuality.HasSmithOfOne
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.G6Decomposition
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.IntModel

section
open IsLocalRing Matrix NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th UpperTheory.V.Th.Nm GlobalTheory.GalOfCusp

private theorem UpperTheory.V.Th.Nm.smith_gen {K : Type*} [NormedField K] [IsUltrametricDist K] {n : ℕ}
    (P : GL (Fin n) K) : ∃ (U V : GL (Fin n) K) (d : Fin n → K),
      (∀ i j, ‖(U : Matrix (Fin n) (Fin n) K) i j‖ ≤ 1) ∧
      (∀ i j, ‖((U⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j‖ ≤ 1) ∧
      (∀ i j, ‖(V : Matrix (Fin n) (Fin n) K) i j‖ ≤ 1) ∧
      (∀ i j, ‖((V⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j‖ ≤ 1) ∧
      (∀ i, d i ≠ 0) ∧ (P : Matrix (Fin n) (Fin n) K) = U * diagonal d * V :=
  _root_.UpperTheory.Reformulated.B.StringRepresentationDecomposition.smith_gen P

theorem UpperTheory.V.Th.Nm.smith :
    ∀ {l : ℕ} [Fact l.Prime] {n : ℕ} (P : GL (Fin n) (Qbar l)), ∃ (U V : GL (Fin n) (Qbar l)) (d : Fin n → Qbar l), IntM (U : Matrix (Fin n) (Fin n) (Qbar l)) ∧ IntM ((U⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) ∧ IntM (V : Matrix (Fin n) (Fin n) (Qbar l)) ∧ IntM ((V⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) ∧ (∀ i, d i ≠ 0) ∧ (P : Matrix (Fin n) (Fin n) (Qbar l)) = U * diagonal d * V := by
  intro l _ n P
  exact smith_gen P
end

section
open IsLocalRing Matrix NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th UpperTheory.V.Th.Nm GlobalTheory.GalOfCusp

private theorem intM_mul' {l : ℕ} [Fact l.Prime] {n : ℕ} {A B : Matrix (Fin n) (Fin n) (Qbar l)}
    (hA : IntM A) (hB : IntM B) : IntM (A * B) := by
  intro i j
  rw [Matrix.mul_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_
  rw [norm_mul]
  exact mul_le_one₀ (hA i k) (norm_nonneg _) (hB k j)

private theorem intM_transpose' {l : ℕ} [Fact l.Prime] {n : ℕ} {A : Matrix (Fin n) (Fin n) (Qbar l)}
    (hA : IntM A) : IntM Aᵀ := fun i j => hA j i

private theorem le_one_of_mul_self {x : ℝ} (h : x * x ≤ 1) : x ≤ 1 := by nlinarith

private theorem intM_of_symm {l : ℕ} [Fact l.Prime] {n : ℕ} {A : Matrix (Fin n) (Fin n) (Qbar l)}
    (e : Fin n → Qbar l) (he : ∀ i, e i ≠ 0) (hA : IntM A)
    (hs : (diagonal (fun i => (e i)⁻¹) * A * diagonal e)ᵀ = diagonal (fun i => (e i)⁻¹) * A * diagonal e ∨
      (diagonal (fun i => (e i)⁻¹) * A * diagonal e)ᵀ = -(diagonal (fun i => (e i)⁻¹) * A * diagonal e)) :
    IntM (diagonal (fun i => (e i)⁻¹) * A * diagonal e) := by
  intro i j
  set M := diagonal (fun i => (e i)⁻¹) * A * diagonal e with hM
  have hent : ∀ a b, M a b = (e a)⁻¹ * A a b * e b := by
    intro a b
    rw [hM, Matrix.mul_diagonal, Matrix.diagonal_mul]
  have hn : ‖M j i‖ = ‖M i j‖ := by
    rcases hs with h | h
    · have := congrFun (congrFun h i) j
      rw [Matrix.transpose_apply] at this
      rw [this]
    · have := congrFun (congrFun h i) j
      rw [Matrix.transpose_apply, Matrix.neg_apply] at this
      rw [this, norm_neg]
  have hp : M i j * M j i = A i j * A j i := by
    rw [hent, hent]
    have := he i
    have := he j
    field_simp
  apply le_one_of_mul_self
  calc ‖M i j‖ * ‖M i j‖ = ‖M i j * M j i‖ := by rw [norm_mul, hn]
    _ = ‖A i j‖ * ‖A j i‖ := by rw [hp, norm_mul]
    _ ≤ 1 := mul_le_one₀ (hA i j) (norm_nonneg _) (hA j i)

private theorem intM_mid {l : ℕ} [Fact l.Prime] {n : ℕ} {A : Matrix (Fin n) (Fin n) (Qbar l)}
    (e : Fin n → Qbar l) (he : ∀ i, e i ≠ 0) (hA : IntM A)
    (hB : IntM (diagonal e * diagonal e * A * diagonal (fun i => (e i)⁻¹) * diagonal (fun i => (e i)⁻¹))) :
    IntM (diagonal e * A * diagonal (fun i => (e i)⁻¹)) := by
  intro i j
  have h1 := hB i j
  rw [Matrix.mul_assoc (diagonal e) (diagonal e), Matrix.mul_diagonal, Matrix.mul_diagonal,
    Matrix.diagonal_mul, Matrix.diagonal_mul] at h1
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  apply le_one_of_mul_self
  have hp : (e i * A i j * (e j)⁻¹) * (e i * A i j * (e j)⁻¹)
      = (e i * (e i * A i j) * (e j)⁻¹ * (e j)⁻¹) * A i j := by ring
  rw [← norm_mul, hp, norm_mul]
  exact mul_le_one₀ h1 (norm_nonneg _) (hA i j)

private theorem inv_symm {K : Type} [CommRing K] {n : ℕ} (M : GL (Fin n) K)
    (h : (M : Matrix (Fin n) (Fin n) K)ᵀ = M ∨ (M : Matrix (Fin n) (Fin n) K)ᵀ = -M) :
    ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ = (M⁻¹ : GL (Fin n) K) ∨
      ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ = -((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  have h1 : (M : Matrix (Fin n) (Fin n) K) * (M⁻¹ : GL (Fin n) K) = 1 := M.mul_inv
  generalize ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = N at h1 ⊢
  generalize (M : Matrix (Fin n) (Fin n) K) = A at h h1
  have h2 : Nᵀ * Aᵀ = 1 := by rw [← Matrix.transpose_mul, h1, Matrix.transpose_one]
  rcases h with h | h
  · left
    rw [h] at h2
    calc Nᵀ = Nᵀ * (A * N) := by rw [h1, Matrix.mul_one]
      _ = N := by rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
  · right
    rw [h, Matrix.mul_neg, neg_eq_iff_eq_neg] at h2
    calc Nᵀ = Nᵀ * (A * N) := by rw [h1, Matrix.mul_one]
      _ = -N := by rw [← Matrix.mul_assoc, h2, Matrix.neg_mul, Matrix.one_mul]

theorem UpperTheory.V.Th.Nm.midpoint :
    ∀ {l : ℕ} [Fact l.Prime] {n : ℕ} (S : Set (GL (Fin n) (Qbar l))) (P : GL (Fin n) (Qbar l)), ((P : Matrix (Fin n) (Fin n) (Qbar l))ᵀ = P ∨ (P : Matrix (Fin n) (Fin n) (Qbar l))ᵀ = -P) → (∀ g ∈ S, IntM (g : Matrix (Fin n) (Fin n) (Qbar l)) ∧ IntM ((P * g * P⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l))) → ∃ Q P' : GL (Fin n) (Qbar l), (P' : Matrix (Fin n) (Fin n) (Qbar l)) = (Q : Matrix (Fin n) (Fin n) (Qbar l))ᵀ * P * Q ∧ IntM (P' : Matrix (Fin n) (Fin n) (Qbar l)) ∧ IntM ((P'⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) ∧ ∀ g ∈ S, IntM ((Q⁻¹ * g * Q : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) := by
  intro l _ n S P hP hS
  obtain ⟨U, V, d, hU, hU', hV, hV', hd, hPe⟩ := smith P
  have hsq : ∀ i, ∃ z : Qbar l, d i = z * z := fun i => IsAlgClosed.exists_eq_mul_self (d i)
  choose e hee using hsq
  have he : ∀ i, e i ≠ 0 := fun i h => hd i (by rw [hee i, h, mul_zero])
  obtain ⟨E, hE, hE'⟩ : ∃ E : GL (Fin n) (Qbar l), (E : Matrix (Fin n) (Fin n) (Qbar l)) = diagonal e ∧
      ((E⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) = diagonal (fun i => (e i)⁻¹) := by
    refine ⟨⟨diagonal e, diagonal (fun i => (e i)⁻¹), ?_, ?_⟩, rfl, rfl⟩
    · rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1; funext i; exact mul_inv_cancel₀ (he i)
    · rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1; funext i; exact inv_mul_cancel₀ (he i)
  obtain ⟨T, hT, hT'⟩ : ∃ T : GL (Fin n) (Qbar l),
      (T : Matrix (Fin n) (Fin n) (Qbar l)) = (V : Matrix (Fin n) (Fin n) (Qbar l))ᵀ ∧
      ((T⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) =
        ((V⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l))ᵀ := by
    refine ⟨⟨(V : Matrix (Fin n) (Fin n) (Qbar l))ᵀ,
      ((V⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l))ᵀ, ?_, ?_⟩, rfl, rfl⟩
    · rw [← Matrix.transpose_mul, V.inv_mul, Matrix.transpose_one]
    · rw [← Matrix.transpose_mul, V.mul_inv, Matrix.transpose_one]
  have hPG : P = U * (E * E) * V := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Units.val_mul, hE, Matrix.diagonal_mul_diagonal, hPe]
    congr 3; funext i; exact hee i
  have hQt : ((V⁻¹ * E⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l))ᵀ
      = ((E⁻¹ * T⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) := by
    rw [Units.val_mul, Units.val_mul, Matrix.transpose_mul, hT', hE', Matrix.diagonal_transpose]
  have hP' : ((E⁻¹ * (T⁻¹ * U) * E : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) =
      ((V⁻¹ * E⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l))ᵀ * P *
        ((V⁻¹ * E⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) := by
    rw [hQt, ← Units.val_mul, ← Units.val_mul, hPG]
    congr 1
    group
  have hsym : ((E⁻¹ * (T⁻¹ * U) * E : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l))ᵀ =
        ((E⁻¹ * (T⁻¹ * U) * E : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) ∨
      ((E⁻¹ * (T⁻¹ * U) * E : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l))ᵀ =
        -((E⁻¹ * (T⁻¹ * U) * E : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) := by
    rw [hP', Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc]
    rcases hP with h | h
    · left; rw [h]
    · right; rw [h, Matrix.mul_neg, Matrix.neg_mul]
  refine ⟨V⁻¹ * E⁻¹, E⁻¹ * (T⁻¹ * U) * E, hP', ?_, ?_, ?_⟩
  · rw [Units.val_mul, Units.val_mul, hE, hE'] at hsym ⊢
    refine intM_of_symm e he ?_ hsym
    rw [Units.val_mul, hT']
    exact intM_mul' (intM_transpose' hV') hU
  · have hi := inv_symm _ hsym
    have hinv : (E⁻¹ * (T⁻¹ * U) * E)⁻¹ = E⁻¹ * (U⁻¹ * T) * E := by group
    rw [hinv, Units.val_mul, Units.val_mul, hE, hE'] at hi ⊢
    refine intM_of_symm e he ?_ hi
    rw [Units.val_mul, hT]
    exact intM_mul' hU' (intM_transpose' hV)
  · intro g hg
    obtain ⟨h1, h2⟩ := hS g hg
    have e1 : (V⁻¹ * E⁻¹)⁻¹ * g * (V⁻¹ * E⁻¹) = E * (V * g * V⁻¹) * E⁻¹ := by group
    have e2 : E * E * (V * g * V⁻¹) * E⁻¹ * E⁻¹ = U⁻¹ * (P * g * P⁻¹) * U := by
      rw [hPG]; group
    rw [e1, Units.val_mul, Units.val_mul, hE, hE']
    refine intM_mid e he ?_ ?_
    · rw [Units.val_mul, Units.val_mul]
      exact intM_mul' (intM_mul' hV h1) hV'
    · rw [← hE, ← hE', ← Units.val_mul, ← Units.val_mul, ← Units.val_mul, ← Units.val_mul, e2,
        Units.val_mul, Units.val_mul]
      exact intM_mul' (intM_mul' hU' h2) hU
end

section
open IsLocalRing Matrix NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th UpperTheory.V.Th.Nm GlobalTheory.GalOfCusp

namespace UpperTheory.V.Th.Nm

section
variable {l : ℕ} [Fact l.Prime] (F : GFrame l)

private theorem sg_conj_conj (g : F.G₀) : F.conj (F.conj g) = g := by
  apply Subtype.ext
  change F.c * (F.c * g * F.c⁻¹) * F.c⁻¹ = g
  have h : F.c⁻¹ = F.c := inv_eq_of_mul_eq_one_right F.c_sq
  rw [h, ← mul_assoc, ← mul_assoc, F.c_sq, one_mul, mul_assoc, F.c_sq, mul_one]

private theorem sg_eps_conj (O : Type) [CommRing O] [Algebra ℤ_[l] O] (R : Type) [CommRing R] [Algebra O R] (g : F.G₀) :
    F.eps O R (F.conj g) = F.eps O R g := by
  have h : F.ε (F.c * g * F.c⁻¹) = F.ε g := by
    rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm]
  exact congrArg (Units.map (((algebraMap O R).comp (algebraMap ℤ_[l] O) : ℤ_[l] →+* R) : ℤ_[l] →* R)) h

end

private theorem sg_comm {K : Type} [Field K] {n : ℕ} (A B P Q : Matrix (Fin n) (Fin n) K) (e : K) (hA : IsUnit A)
    (hP : IsUnit P) (hQ : P * Q = 1) (h1 : Aᵀ * P * B = e • P) (h2 : Bᵀ * P * A = e • P) :
    B * (Q * Pᵀ) = (Q * Pᵀ) * B := by
  have h3 : Aᵀ * Pᵀ * B = e • Pᵀ := by
    have := congrArg transpose h2
    rwa [transpose_mul, transpose_mul, transpose_transpose, transpose_smul, ← mul_assoc] at this
  have hu : IsUnit (Aᵀ * P) := ((isUnit_transpose A).2 hA).mul hP
  apply hu.mul_left_cancel
  calc Aᵀ * P * (B * (Q * Pᵀ)) = (Aᵀ * P * B) * Q * Pᵀ := by simp only [mul_assoc]
    _ = e • Pᵀ := by rw [h1, smul_mul_assoc, hQ, smul_mul_assoc, one_mul]
    _ = Aᵀ * (P * Q) * Pᵀ * B := by rw [hQ, mul_one, h3]
    _ = Aᵀ * P * (Q * Pᵀ * B) := by simp only [mul_assoc]

private theorem sg_end {K : Type} [Field K] {n : ℕ} (P Q : Matrix (Fin n) (Fin n) K) (hQ : P * Q = 1)
    (h : ∀ Z : Matrix (Fin n) (Fin n) K, Z * (Q * Pᵀ) = (Q * Pᵀ) * Z) : Pᵀ = P ∨ Pᵀ = -P := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Or.inl (Subsingleton.elim _ _)
  obtain ⟨s, hs⟩ := Matrix.mem_range_scalar_of_commute_single (M := Q * Pᵀ) (fun i j _ => h _)
  have h1 : Pᵀ = s • P := by
    calc Pᵀ = P * (Q * Pᵀ) := by rw [← mul_assoc, hQ, one_mul]
      _ = s • P := by rw [← hs, scalar_apply, ← smul_eq_mul_diagonal]
  have h2 : P = (s * s) • P := by
    have := congrArg transpose h1
    rwa [transpose_transpose, transpose_smul, h1, smul_smul] at this
  have h3 : s * s = 1 := by
    have h4 : (1 : Matrix (Fin n) (Fin n) K) = (s * s) • 1 := by
      calc (1 : Matrix (Fin n) (Fin n) K) = P * Q := hQ.symm
        _ = ((s * s) • P) * Q := by rw [← h2]
        _ = (s * s) • 1 := by rw [smul_mul_assoc, hQ]
    have h5 := congrFun (congrFun h4 ⟨0, hn⟩) ⟨0, hn⟩
    simpa using h5.symm
  rcases mul_self_eq_one_iff.1 h3 with rfl | rfl
  · exact Or.inl (by rw [h1, one_smul])
  · exact Or.inr (by rw [h1, neg_smul, one_smul])

end UpperTheory.V.Th.Nm

theorem UpperTheory.V.Th.Nm.sign :
    ∀ {l : ℕ} [Fact l.Prime] {n : ℕ} (F : GFrame l) (c : Coef l) (ρ : F.G₀ →* GL (Fin n) (Qbar l)) (P : GL (Fin n) (Qbar l)), Submodule.span (Qbar l) (Set.range (mat ρ)) = ⊤ → F.IsForm c.O n ρ P → (P : Matrix (Fin n) (Fin n) (Qbar l))ᵀ = P ∨ (P : Matrix (Fin n) (Fin n) (Qbar l))ᵀ = -P := by
  intro l _ n F c ρ P hsp hf
  have hQ : (P : Matrix (Fin n) (Fin n) (Qbar l)) * ((P⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) = 1 :=
    Units.mul_inv P
  refine sg_end _ _ hQ fun Z => ?_
  have hZ : Z ∈ Submodule.span (Qbar l) (Set.range (mat ρ)) := hsp ▸ Submodule.mem_top
  induction hZ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    have h1 := hf (F.conj g)
    rw [sg_conj_conj, sg_eps_conj] at h1
    exact sg_comm _ _ _ _ _ (ρ (F.conj g)).isUnit P.isUnit hQ h1 (hf g)
  | zero => rw [zero_mul, mul_zero]
  | add x y _ _ hx hy => rw [add_mul, mul_add, hx, hy]
  | smul a x _ hx => rw [smul_mul_assoc, mul_smul_comm, hx]
end

section
open IsLocalRing Matrix NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th UpperTheory.V.Th.Nm GlobalTheory.GalOfCusp

namespace UpperTheory.V.Th.Nm

private theorem sd_norm {l : ℕ} [Fact l.Prime] (c : Coef l) (x : c.O) : ‖(x : PadicAlgCl l)‖ ≤ 1 := by
  haveI := c.fin
  have hx : IsIntegral ℤ_[l] (x : PadicAlgCl l) := (Algebra.IsIntegral.isIntegral x).map c.O.val
  rw [← PadicAlgCl.spectralNorm_eq, spectralNorm, minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] hx,
    spectralValue_le_one_iff ((minpoly.monic hx).map _)]
  intro n
  rw [Polynomial.coeff_map]
  exact ((minpoly ℤ_[l] (x : PadicAlgCl l)).coeff n).2

private theorem sd_eps {l : ℕ} [Fact l.Prime] (F : GFrame l) (c : Coef l) (g : F.G₀) (z : ℤ) :
    ‖((F.eps c.O (Qbar l) g ^ z : (Qbar l)ˣ) : Qbar l)‖ ≤ 1 := by
  have h1 : ‖((F.eps c.O (Qbar l) g : (Qbar l)ˣ) : Qbar l)‖ = 1 := by
    simp only [GFrame.eps, pushCh, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe, RingHom.coe_comp,
      Function.comp_apply]
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l)]
    exact (PadicAlgCl.norm_extends l _).trans (PadicInt.norm_units _)
  rw [Units.val_zpow_eq_zpow_val, norm_zpow, h1, _root_.one_zpow]

private theorem sd_conj_conj {l : ℕ} [Fact l.Prime] (F : GFrame l) (g : F.G₀) : F.conj (F.conj g) = g := by
  apply Subtype.ext
  show F.c * (F.c * (g : F.Γ) * F.c⁻¹) * F.c⁻¹ = g
  rw [inv_eq_of_mul_eq_one_right F.c_sq, mul_assoc, mul_assoc, mul_assoc, F.c_sq, mul_one, ← mul_assoc, F.c_sq, one_mul]

private theorem sd_sgn {K : Type} [CommRing K] {n : ℕ} (P Q : Matrix (Fin n) (Fin n) K) (h : Pᵀ = P ∨ Pᵀ = -P) :
    (Qᵀ * P * Q)ᵀ = Qᵀ * P * Q ∨ (Qᵀ * P * Q)ᵀ = -(Qᵀ * P * Q) := by
  have e : (Qᵀ * P * Q)ᵀ = Qᵀ * Pᵀ * Q := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  rcases h with h | h
  · left
    rw [e, h]
  · right
    rw [e, h, Matrix.mul_neg, Matrix.neg_mul]

private theorem sd_form {K : Type} [CommRing K] {n : ℕ} (A B P Q P₀ : GL (Fin n) K) (e : K)
    (hP : (P₀ : Matrix (Fin n) (Fin n) K) = (Q : Matrix (Fin n) (Fin n) K)ᵀ * P * Q)
    (h : (A : Matrix (Fin n) (Fin n) K)ᵀ * P * B = e • (P : Matrix (Fin n) (Fin n) K)) :
    ((P₀ * (Q⁻¹ * B * Q) * P₀⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      e • ((Q⁻¹ * A⁻¹ * Q : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ := by
  have hPB : (P : Matrix (Fin n) (Fin n) K) * B = e • ((↑A⁻¹ : Matrix (Fin n) (Fin n) K)ᵀ * P) := by
    calc (P : Matrix (Fin n) (Fin n) K) * B
        = ((↑A⁻¹ : Matrix (Fin n) (Fin n) K)ᵀ * (A : Matrix (Fin n) (Fin n) K)ᵀ) * P * B := by
          rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one, Matrix.one_mul]
      _ = (↑A⁻¹ : Matrix (Fin n) (Fin n) K)ᵀ * ((A : Matrix (Fin n) (Fin n) K)ᵀ * P * B) := by
          simp only [Matrix.mul_assoc]
      _ = e • ((↑A⁻¹ : Matrix (Fin n) (Fin n) K)ᵀ * P) := by
          rw [h, Matrix.mul_smul]
  have hQ : ∀ X : Matrix (Fin n) (Fin n) K,
      (↑Q⁻¹ : Matrix (Fin n) (Fin n) K)ᵀ * ((Q : Matrix (Fin n) (Fin n) K)ᵀ * X) = X := by
    intro X
    rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one, Matrix.one_mul]
  have key : (P₀ : Matrix (Fin n) (Fin n) K) *
      ((↑Q⁻¹ : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K) * (Q : Matrix (Fin n) (Fin n) K)) =
      (e • ((↑Q⁻¹ : Matrix (Fin n) (Fin n) K) * (↑A⁻¹ : Matrix (Fin n) (Fin n) K) *
        (Q : Matrix (Fin n) (Fin n) K))ᵀ) * (P₀ : Matrix (Fin n) (Fin n) K) := by
    rw [hP, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.smul_mul]
    simp only [Matrix.mul_assoc, Units.mul_inv_cancel_left, hQ]
    rw [← Matrix.mul_assoc (P : Matrix (Fin n) (Fin n) K) (B : Matrix (Fin n) (Fin n) K), hPB]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
  simp only [Units.val_mul]
  rw [key, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

end UpperTheory.V.Th.Nm

theorem UpperTheory.V.Th.Nm.selfDual :
    ∀ {l : ℕ} [Fact l.Prime] {n : ℕ} (F : GFrame l) (c : Coef l) (ρ : F.G₀ →* GL (Fin n) (Qbar l)) (P : GL (Fin n) (Qbar l)), Continuous ρ → Submodule.span (Qbar l) (Set.range (mat ρ)) = ⊤ → F.IsForm c.O n ρ P → ∃ Q P' : GL (Fin n) (Qbar l), (P' : Matrix (Fin n) (Fin n) (Qbar l)) = (Q : Matrix (Fin n) (Fin n) (Qbar l))ᵀ * P * Q ∧ ((P' : Matrix (Fin n) (Fin n) (Qbar l))ᵀ = P' ∨ (P' : Matrix (Fin n) (Fin n) (Qbar l))ᵀ = -P') ∧ IntM (P' : Matrix (Fin n) (Fin n) (Qbar l)) ∧ IntM ((P'⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) ∧ ∀ g, IntM (mat (cj Q ρ) g) := by
  intro l hl n F c ρ P hρ hspan hform
  haveI : CompactSpace F.G₀ :=
    isCompact_iff_compactSpace.mp (Subgroup.isClosed_of_isOpen _ F.η_open).isCompact
  obtain ⟨c', Q₀, ρ₀, -, hQ₀, -⟩ := Ws.Eb.intModel c ρ hρ
  have hint : ∀ g, IntM ((cj Q₀ ρ g : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) := by
    intro g i j
    rw [cj_apply, mul_assoc, hQ₀ g, inv_mul_cancel_left]
    exact sd_norm c' ((ρ₀ g : Matrix (Fin n) (Fin n) c'.O) i j)
  let Qt : GL (Fin n) (Qbar l) :=
    ⟨(Q₀ : Matrix (Fin n) (Fin n) (Qbar l))ᵀ, (↑Q₀⁻¹ : Matrix (Fin n) (Fin n) (Qbar l))ᵀ,
      by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one],
      by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]⟩
  obtain ⟨P₁, hP₁⟩ : ∃ P₁ : GL (Fin n) (Qbar l),
      (P₁ : Matrix (Fin n) (Fin n) (Qbar l)) = (Q₀ : Matrix (Fin n) (Fin n) (Qbar l))ᵀ * P * Q₀ :=
    ⟨Qt * P * Q₀, rfl⟩
  have hsP₁ : (P₁ : Matrix (Fin n) (Fin n) (Qbar l))ᵀ = P₁ ∨
      (P₁ : Matrix (Fin n) (Fin n) (Qbar l))ᵀ = -(P₁ : Matrix (Fin n) (Fin n) (Qbar l)) := by
    rw [hP₁]
    exact sd_sgn _ _ (sign F c ρ P hspan hform)
  have hconj : ∀ g, IntM ((P₁ * cj Q₀ ρ (F.conj g) * P₁⁻¹ : GL (Fin n) (Qbar l)) :
      Matrix (Fin n) (Fin n) (Qbar l)) := by
    intro g
    have key := sd_form (ρ g) (ρ (F.conj g)) P Q₀ P₁ _ hP₁ (hform g)
    rw [cj_apply, key]
    intro i j
    have hinv : (Q₀⁻¹ * (ρ g)⁻¹ * Q₀ : GL (Fin n) (Qbar l)) = cj Q₀ ρ g⁻¹ := by
      rw [cj_apply, map_inv]
    rw [hinv, Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul, norm_mul]
    exact mul_le_one₀ (sd_eps F c g _) (norm_nonneg _) (hint _ j i)
  obtain ⟨Q₂, P', hP', hP'int, hP'inv, hQ₂⟩ := midpoint (Set.range (cj Q₀ ρ)) P₁ hsP₁ (by
    rintro _ ⟨h, rfl⟩
    refine ⟨hint h, ?_⟩
    have := hconj (F.conj h)
    rwa [sd_conj_conj] at this)
  refine ⟨Q₀ * Q₂, P', ?_, ?_, hP'int, hP'inv, ?_⟩
  · rw [hP', hP₁]
    simp only [Units.val_mul, Matrix.transpose_mul, Matrix.mul_assoc]
  · rw [hP']
    exact sd_sgn _ _ hsP₁
  · intro g
    have := hQ₂ _ ⟨g, rfl⟩
    rw [cj_apply] at this
    show IntM ((cj (Q₀ * Q₂) ρ g : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l))
    rw [cj_apply, _root_.mul_inv_rev]
    simpa only [mul_assoc] using this
end
