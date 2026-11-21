import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsAutStableSLMatrixGroupImageBlockDiagPartStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.BlockDiagPartOfRatIdempotentOneAndMulOfTriangulaStatement
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.GaloisStableSubmoduleLeSpanRational
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RatComponentMemRatPolysVanishingOnMatrixSet
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EvalComplexPolyEqZeroOnRatZariskiClosure
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RatZariskiClosurePointsIsGroup
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsAutStableSLMatrixGroupImageBlockDiagPart
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.BlockDiagPartOfRatIdempotentOneAndMulOfTriangula

section
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem exists_poly_ev_line {ι : Type} [Fintype ι] [DecidableEq ι] (f : MvPolynomial (ι × ι) ℚ)
    (A B : Matrix ι ι ℂ) : ∃ p : Polynomial ℂ, ∀ t : ℂ, p.eval t = ev f (A + t • B) := by
  induction f using MvPolynomial.induction_on with
  | C a => exact ⟨Polynomial.C (algebraMap ℚ ℂ a), fun t => by simp [ev]⟩
  | add f g hf hg =>
    obtain ⟨p, hp⟩ := hf
    obtain ⟨q, hq⟩ := hg
    refine ⟨p + q, fun t => ?_⟩
    rw [Polynomial.eval_add, hp, hq]
    simp [ev]
  | mul_X f ij hf =>
    obtain ⟨p, hp⟩ := hf
    refine ⟨p * (Polynomial.C (A ij.1 ij.2) + Polynomial.X * Polynomial.C (B ij.1 ij.2)), fun t => ?_⟩
    rw [Polynomial.eval_mul, hp, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_C, Polynomial.eval_X]
    simp [ev]

theorem one_add_smul_mem_of_sq_zero :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), IsQGroup Γ →
      ∀ ε : Matrix ι ι ℂ, ε * ε = 0 → 1 + ε ∈ Γ → ∀ t : ℂ, 1 + t • ε ∈ Γ := by
  intro ι _ _ Γ hΓ ε hε h1 t
  have hn : ∀ n : ℕ, 1 + (n : ℂ) • ε ∈ Γ := by
    intro n
    induction n with
    | zero => simpa using hΓ.one_mem
    | succ n ih =>
      have h := hΓ.mul_mem _ ih _ h1
      have e : (1 + (n : ℂ) • ε) * (1 + ε) = 1 + ((n + 1 : ℕ) : ℂ) • ε := by
        rw [mul_add, mul_one, add_mul, one_mul, smul_mul_assoc, hε, smul_zero, add_zero, Nat.cast_succ,
          add_smul, one_smul, add_assoc]
      rwa [e] at h
  apply hΓ.closed
  intro f hf
  obtain ⟨p, hp⟩ := exists_poly_ev_line f 1 ε
  have hp0 : p = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ => (n : ℂ)) Nat.cast_injective ?_
    intro n
    show p.eval (n : ℂ) = 0
    rw [hp]
    exact hf _ (hn n)
  rw [← hp, hp0, Polynomial.eval_zero]

end GlobalTheory.ClassFin
end

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.one_add_smul_mem_of_sq_zero' : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), IsQGroup Γ → ∀ ε : Matrix ι ι ℂ, ε * ε = 0 → 1 + ε ∈ Γ → ∀ t : ℂ, 1 + t • ε ∈ Γ := by
  atlas_forward_decl GlobalTheory.ClassFin.one_add_smul_mem_of_sq_zero
end

section
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.RatProj

variable {ι : Type} [Fintype ι] [DecidableEq ι]

noncomputable def entryEquiv (ι : Type) : Matrix ι ι ℂ ≃ₗ[ℂ] (ι × ι → ℂ) where
  toFun X := fun kl => X kl.1 kl.2
  invFun f := Matrix.of fun i j => f (i, j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem repr_entry (w : Matrix ι ι ℂ) (k : ι × ι) :
    (Module.Basis.ofEquivFun (entryEquiv ι)).repr w k = w k.1 k.2 := by
  rw [Module.Basis.ofEquivFun_repr_apply]; rfl

noncomputable def castLin (ι : Type) : Matrix ι ι ℚ →ₗ[ℚ] Matrix ι ι ℂ where
  toFun X := X.map (algebraMap ℚ ℂ)
  map_add' X Y := by ext i j; simp
  map_smul' q X := by ext i j; simp [Rat.smul_def]

noncomputable def linExtLin (c : ι × ι → ι × ι → ℚ) : Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ where
  toFun X := linExt c X
  map_add' X Y := by ext i j; simp [linExt, mul_add, Finset.sum_add_distrib]
  map_smul' a X := by ext i j; simp [linExt, Finset.mul_sum, mul_left_comm]

theorem linExt_eq_sum (p : Matrix ι ι ℚ →ₗ[ℚ] Matrix ι ι ℚ) (X : Matrix ι ι ℂ) :
    linExt (fun ij kl => p (single kl.1 kl.2 1) ij.1 ij.2) X =
      ∑ kl : ι × ι, X kl.1 kl.2 • castLin ι (p (single kl.1 kl.2 1)) := by
  ext i j
  simp [linExt, castLin, Matrix.sum_apply, mul_comm]

theorem linExt_cast (p : Matrix ι ι ℚ →ₗ[ℚ] Matrix ι ι ℚ) (Y : Matrix ι ι ℚ) :
    linExt (fun ij kl => p (single kl.1 kl.2 1) ij.1 ij.2) (castLin ι Y) = castLin ι (p Y) := by
  rw [linExt_eq_sum]
  have hY : Y = ∑ kl : ι × ι, Y kl.1 kl.2 • single kl.1 kl.2 (1 : ℚ) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single Y]
    rw [Fintype.sum_prod_type]
    simp [Matrix.smul_single]
  conv_rhs => rw [hY]
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun kl _ => ?_
  rw [map_smul, map_smul]
  ext i j
  simp [castLin, Rat.smul_def]

theorem exists_rat_projector : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (E : Submodule ℂ (Matrix ι ι ℂ)), (∀ σ : ℂ ≃+* ℂ, ∀ x ∈ E, x.map σ ∈ E) → ∃ c : ι × ι → ι × ι → ℚ, (∀ X : Matrix ι ι ℂ, linExt c X ∈ E) ∧ ∀ x ∈ E, linExt c x = x := by
  intro ι _ _ E hE
  let E₀ : Submodule ℚ (Matrix ι ι ℚ) := (E.restrictScalars ℚ).comap (castLin ι)
  obtain ⟨π, hπ⟩ : ∃ π : Matrix ι ι ℚ →ₗ[ℚ] E₀, ∀ x : E₀, π x = x := by
    obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective E₀.subtype E₀.ker_subtype
    exact ⟨g, fun x => LinearMap.congr_fun hg x⟩
  let p : Matrix ι ι ℚ →ₗ[ℚ] Matrix ι ι ℚ := E₀.subtype ∘ₗ π
  refine ⟨fun ij kl => p (single kl.1 kl.2 1) ij.1 ij.2, fun X => ?_, fun x hx => ?_⟩
  · rw [linExt_eq_sum]
    exact E.sum_mem fun kl _ => E.smul_mem _ (π (single kl.1 kl.2 1)).2
  · have hd := GlobalTheory.T.galoisStable_submodule_le_span_rational (Matrix ι ι ℂ) (ι × ι) (Module.Basis.ofEquivFun (entryEquiv ι)) E
      (fun σ w hw => ⟨w.map σ, hE σ w hw, fun k => by
        rw [repr_entry, repr_entry]; rfl⟩) hx
    have key : Set.EqOn (linExtLin fun ij kl => p (single kl.1 kl.2 1) ij.1 ij.2) (LinearMap.id (R := ℂ))
        {w | w ∈ E ∧ ∀ k, ∃ q : ℚ, (Module.Basis.ofEquivFun (entryEquiv ι)).repr w k = q} := by
      rintro w ⟨hw, hq⟩
      choose q hq using hq
      have hwq : w = castLin ι (Matrix.of fun i j => q (i, j)) := by
        ext i j
        have := hq (i, j)
        rw [repr_entry] at this
        simpa [castLin] using this
      have hmem : (Matrix.of fun i j => q (i, j)) ∈ E₀ := by
        change castLin ι _ ∈ E
        rw [← hwq]; exact hw
      have h1 : p (Matrix.of fun i j => q (i, j)) = Matrix.of fun i j => q (i, j) :=
        congrArg Subtype.val (hπ ⟨_, hmem⟩)
      have h2 := linExt_cast p (Matrix.of fun i j => q (i, j))
      rw [h1, ← hwq] at h2
      exact h2
    exact LinearMap.eqOn_span key hd

end GlobalTheory.ClassFin.RatProj
end

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rat_projector_of_autStable_matrices : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (E : Submodule ℂ (Matrix ι ι ℂ)), (∀ σ : ℂ ≃+* ℂ, ∀ x ∈ E, x.map σ ∈ E) → ∃ c : ι × ι → ι × ι → ℚ, (∀ X : Matrix ι ι ℂ, linExt c X ∈ E) ∧ ∀ x ∈ E, linExt c x = x := by
  atlas_forward_decl GlobalTheory.ClassFin.RatProj.exists_rat_projector
end

section
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem corner_mul_corner {A : Type} [Ring A] (E x y : A) (hE : E * E = E)
    (hx : E * x * (1 - E) = x) (hy : E * y * (1 - E) = y) : x * y = 0 := by
  have h : (1 - E) * E = 0 := by rw [sub_mul, one_mul, hE, sub_self]
  calc x * y = (E * x * (1 - E)) * (E * y * (1 - E)) := by rw [hx, hy]
    _ = E * x * ((1 - E) * E) * y * (1 - E) := by simp only [mul_assoc]
    _ = 0 := by rw [h]; simp

theorem exists_linExt_corner_proj : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (e : Matrix ι ι ℚ), IsQGroup Γ → e * e = e → ∃ c : ι × ι → ι × ι → ℚ, (∀ X : Matrix ι ι ℂ, 1 + linExt c X ∈ Γ ∧ e.map (algebraMap ℚ ℂ) * linExt c X * (1 - e.map (algebraMap ℚ ℂ)) = linExt c X) ∧ ∀ ε : Matrix ι ι ℂ, 1 + ε ∈ Γ → e.map (algebraMap ℚ ℂ) * ε * (1 - e.map (algebraMap ℚ ℂ)) = ε → linExt c ε = ε := by
  intro ι _ _ Γ e hΓ he
  set E : Matrix ι ι ℂ := e.map (algebraMap ℚ ℂ) with hEdef
  have hE : E * E = E := by
    rw [hEdef, ← Matrix.map_mul, he]
  let S : Submodule ℂ (Matrix ι ι ℂ) :=
    { carrier := {ε | 1 + ε ∈ Γ ∧ E * ε * (1 - E) = ε}
      zero_mem' := ⟨by simpa using hΓ.one_mem, by simp⟩
      add_mem' := by
        rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
        refine ⟨?_, by rw [mul_add, add_mul, hx2, hy2]⟩
        have h0 := corner_mul_corner E x y hE hx2 hy2
        have h1 := hΓ.mul_mem _ hx1 _ hy1
        have h2 : (1 + x) * (1 + y) = 1 + (x + y) := by
          rw [mul_add, add_mul, add_mul, h0]; simp [add_assoc]
        rwa [h2] at h1
      smul_mem' := by
        rintro t x ⟨hx1, hx2⟩
        refine ⟨GlobalTheory.T.one_add_smul_mem_of_sq_zero' ι Γ hΓ x (corner_mul_corner E x x hE hx2 hx2) hx1 t, ?_⟩
        rw [Matrix.mul_smul, Matrix.smul_mul, hx2] }
  have hS : ∀ σ : ℂ ≃+* ℂ, ∀ x ∈ S, x.map σ ∈ S := by
    rintro σ x ⟨hx1, hx2⟩
    have hEσ : (σ : ℂ →+* ℂ).mapMatrix E = E := by
      ext i j
      simp [hEdef]
    have hx : x.map σ = (σ : ℂ →+* ℂ).mapMatrix x := rfl
    refine ⟨?_, ?_⟩
    · have h1 := hΓ.aut_mem σ _ hx1
      have h2 : (1 + x).map σ = (σ : ℂ →+* ℂ).mapMatrix (1 + x) := rfl
      rw [h2, map_add, map_one] at h1
      exact h1
    · have h3 := congrArg (σ : ℂ →+* ℂ).mapMatrix hx2
      rw [map_mul, map_mul, map_sub, map_one, hEσ] at h3
      exact h3
  obtain ⟨c, hc1, hc2⟩ := GlobalTheory.T.exists_rat_projector_of_autStable_matrices ι S hS
  exact ⟨c, fun X => hc1 X, fun ε h1 h2 => hc2 ε ⟨h1, h2⟩⟩

end GlobalTheory.ClassFin
end

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rat_linear_param_blockDiag_kernel : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (e : Matrix ι ι ℚ), IsQGroup Γ → e * e = e → ∃ c : ι × ι → ι × ι → ℚ, (∀ X : Matrix ι ι ℂ, 1 + linExt c X ∈ Γ ∧ e.map (algebraMap ℚ ℂ) * linExt c X * (1 - e.map (algebraMap ℚ ℂ)) = linExt c X) ∧ ∀ ε : Matrix ι ι ℂ, 1 + ε ∈ Γ → e.map (algebraMap ℚ ℂ) * ε * (1 - e.map (algebraMap ℚ ℂ)) = ε → linExt c ε = ε := by
  atlas_forward_decl GlobalTheory.ClassFin.exists_linExt_corner_proj
end

section
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem isNilpotent_of_forall_algHom_eq_zero (T : Type) [CommRing T] [Algebra ℂ T]
    [Algebra.FiniteType ℂ T] (x : T) (h : ∀ ω : T →ₐ[ℂ] ℂ, ω x = 0) : IsNilpotent x := by
  have hJ : IsJacobsonRing T := isJacobsonRing_of_finiteType (A := ℂ)
  have h1 : x ∈ Ideal.jacobson (⊥ : Ideal T) := by
    rw [Ideal.jacobson, Ideal.mem_sInf]
    rintro m ⟨-, hm⟩
    let := Ideal.Quotient.field m
    have hfin : Module.Finite ℂ (T ⧸ m) := finite_of_finite_type_of_isJacobsonRing ℂ (T ⧸ m)
    have hb : Function.Bijective (algebraMap ℂ (T ⧸ m)) :=
      IsAlgClosed.algebraMap_bijective_of_isIntegral
    let e : ℂ ≃ₐ[ℂ] (T ⧸ m) := AlgEquiv.ofBijective (Algebra.ofId ℂ (T ⧸ m)) hb
    have := h ((e.symm : (T ⧸ m) →ₐ[ℂ] ℂ).comp (Ideal.Quotient.mkₐ ℂ m))
    have h0 : e.symm (Ideal.Quotient.mk m x) = 0 := this
    exact Ideal.Quotient.eq_zero_iff_mem.mp ((map_eq_zero_iff _ e.symm.injective).mp h0)
  have h2 : x ∈ Ideal.radical (⊥ : Ideal T) := by
    have := IsJacobsonRing.out hJ (Ideal.radical_isRadical (⊥ : Ideal T))
    rw [← this]
    exact Ideal.jacobson_mono Ideal.le_radical h1
  exact h2

theorem isNilpotent_tmul_sub_tmul_of_const_on_fibres :
    ∀ (B A : Type) [CommRing B] [CommRing A] [Algebra ℂ B] [Algebra ℂ A] [Algebra B A] [IsScalarTower ℂ B A] [Algebra.FiniteType ℂ A] (f : A), (∀ χ χ' : A →ₐ[ℂ] ℂ, (∀ b : B, χ (algebraMap B A b) = χ' (algebraMap B A b)) → χ f = χ' f) → IsNilpotent (f ⊗ₜ[B] (1 : A) - (1 : A) ⊗ₜ[B] f) := by
  intro B A _ _ _ _ _ _ _ f h
  have : Algebra.FiniteType B A := Algebra.FiniteType.of_restrictScalars_finiteType ℂ B A
  have : Algebra.FiniteType A (A ⊗[B] A) := inferInstance
  have : Algebra.FiniteType ℂ (A ⊗[B] A) := Algebra.FiniteType.trans (S := A) inferInstance inferInstance
  apply isNilpotent_of_forall_algHom_eq_zero
  intro ω
  let l : A →ₐ[ℂ] A ⊗[B] A := Algebra.TensorProduct.includeLeft
  let r : A →ₐ[ℂ] A ⊗[B] A :=
    (Algebra.TensorProduct.includeRight : A →ₐ[B] A ⊗[B] A).restrictScalars ℂ
  have := h (ω.comp l) (ω.comp r) (fun b => by
    simp only [AlgHom.comp_apply, l, r, Algebra.TensorProduct.includeLeft_apply,
      AlgHom.restrictScalars_apply, Algebra.TensorProduct.includeRight_apply]
    congr 1
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul])
  rw [map_sub, sub_eq_zero]
  exact this

end GlobalTheory.ClassFin
end

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isNilpotent_tmul_sub_tmul_of_const_on_fibres' : ∀ (B A : Type) [CommRing B] [CommRing A] [Algebra ℂ B] [Algebra ℂ A] [Algebra B A] [IsScalarTower ℂ B A] [Algebra.FiniteType ℂ A] (f : A), (∀ χ χ' : A →ₐ[ℂ] ℂ, (∀ b : B, χ (algebraMap B A b) = χ' (algebraMap B A b)) → χ f = χ' f) → IsNilpotent (f ⊗ₜ[B] (1 : A) - (1 : A) ⊗ₜ[B] f) := by
  atlas_forward_decl GlobalTheory.ClassFin.isNilpotent_tmul_sub_tmul_of_const_on_fibres
end

section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem exists_algHom_algebraicClosure_ker_le (K A : Type) [Field K] [CommRing A] [Algebra K A]
    [Algebra.FiniteType K A] (m : Ideal A) [m.IsMaximal] :
    ∃ φ : A →ₐ[K] AlgebraicClosure K, ∀ x, φ x = 0 → x ∈ m := by
  letI : Field (A ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite K (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing K (A ⧸ m)
  let ι : (A ⧸ m) →ₐ[K] AlgebraicClosure K := IsAlgClosed.lift
  refine ⟨ι.comp (Ideal.Quotient.mkₐ K m), fun x hx => ?_⟩
  have h : ι (Ideal.Quotient.mk m x) = 0 := hx
  have h2 : Ideal.Quotient.mk m x = 0 := ι.toRingHom.injective (by simpa using h)
  exact Ideal.Quotient.eq_zero_iff_mem.mp h2

theorem mem_range_algebraMap_of_isNilpotent_tmul_sub (K A : Type) [Field K] [CharZero K]
    [CommRing A] [Algebra K A] [Algebra.FiniteType K A] [IsReduced A] (f : A)
    (hf : IsNilpotent (f ⊗ₜ[K] (1 : A) - (1 : A) ⊗ₜ[K] f)) : f ∈ (algebraMap K A).range := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · exact ⟨0, Subsingleton.elim _ _⟩
  have h1 : ∀ φ ψ : A →ₐ[K] AlgebraicClosure K, φ f = ψ f := by
    intro φ ψ
    have h := (hf.map (Algebra.TensorProduct.productMap φ ψ)).eq_zero
    simpa [sub_eq_zero] using h
  obtain ⟨m₀, hm₀⟩ := Ideal.exists_maximal A
  obtain ⟨φ₀, -⟩ := exists_algHom_algebraicClosure_ker_le K A m₀
  have h2 : φ₀ f ∈ Set.range (algebraMap K (AlgebraicClosure K)) := by
    rw [InfiniteGalois.mem_range_algebraMap_iff_fixed]
    intro σ
    exact h1 (σ.toAlgHom.comp φ₀) φ₀
  obtain ⟨c, hc⟩ := h2
  haveI : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := K)
  refine ⟨c, ?_⟩
  have h3 : f - algebraMap K A c ∈ (⊥ : Ideal A).jacobson := by
    rw [Ideal.jacobson, Submodule.mem_sInf]
    rintro m ⟨-, hm⟩
    obtain ⟨φ, hφ⟩ := exists_algHom_algebraicClosure_ker_le K A m
    apply hφ
    rw [map_sub, AlgHom.commutes, hc, h1 φ φ₀, sub_self]
  have h4 : (⊥ : Ideal A).jacobson = ⊥ :=
    IsJacobsonRing.out inferInstance (Ideal.isRadical_bot)
  rw [h4, Ideal.mem_bot, sub_eq_zero] at h3
  exact h3.symm

end GlobalTheory.ClassFin
end

section
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory

theorem exists_denominator_of_isField_localization (B A : Type) [CommRing B] [CommRing A]
    [Algebra ℚ B] [Algebra B A] [Algebra.FiniteType B A] [IsReduced A] (M : Submonoid B)
    (hF : IsField (Localization M)) (f : A)
    (hf : IsNilpotent (f ⊗ₜ[B] (1 : A) - (1 : A) ⊗ₜ[B] f)) :
    ∃ m ∈ M, ∃ b' : B, algebraMap B A m * f = algebraMap B A b' := by
  letI : Field (Localization M) := hF.toField
  haveI : CharZero (Localization M) := algebraRat.charZero _
  let K := Localization M
  let A' := Localization (Algebra.algebraMapSubmonoid A M)
  haveI : IsReduced A' := inferInstance
  haveI : Algebra.FiniteType K A' := by
    haveI : IsLocalization (Submonoid.map (algebraMap B A) M) A' :=
      inferInstanceAs (IsLocalization (Algebra.algebraMapSubmonoid A M) A')
    have h := RingHom.finiteType_localizationPreserves (algebraMap B A) M K A'
      (RingHom.finiteType_algebraMap.mpr inferInstance)
    exact h
  let g : A →ₐ[B] A' := IsScalarTower.toAlgHom B A A'
  let φ : A ⊗[B] A →ₐ[B] A' ⊗[K] A' :=
    Algebra.TensorProduct.lift
      (((Algebra.TensorProduct.includeLeft : A' →ₐ[K] A' ⊗[K] A').restrictScalars B).comp g)
      (((Algebra.TensorProduct.includeRight : A' →ₐ[K] A' ⊗[K] A').restrictScalars B).comp g)
      (fun _ _ => Commute.all _ _)
  have hn : IsNilpotent (g f ⊗ₜ[K] (1 : A') - (1 : A') ⊗ₜ[K] g f) := by
    have := hf.map φ
    simpa [φ] using this
  obtain ⟨k, hk⟩ := GlobalTheory.ClassFin.mem_range_algebraMap_of_isNilpotent_tmul_sub K A' (g f) hn
  obtain ⟨⟨β, t⟩, ht⟩ := IsLocalization.surj M k
  have h1 : algebraMap A A' (algebraMap B A t * f) = algebraMap A A' (algebraMap B A β) := by
    have := congrArg (algebraMap K A') ht
    rw [map_mul, hk, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at this
    rw [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, ← this,
      mul_comm]
    rfl
  obtain ⟨⟨_, u, hu, rfl⟩, hc⟩ :=
    (IsLocalization.eq_iff_exists (Algebra.algebraMapSubmonoid A M) A').1 h1
  refine ⟨u * t, M.mul_mem hu t.2, u * β, ?_⟩
  simpa [map_mul, mul_assoc] using hc

theorem exists_common_denominator_of_isNilpotent :
    ∀ (B A : Type) [CommRing B] [CommRing A] [Algebra ℚ B] [Algebra B A] [Algebra.FiniteType B A] [IsReduced A] [Nontrivial B], Function.Injective (algebraMap B A) → ∀ s : Finset A, (∀ f ∈ s, IsNilpotent (f ⊗ₜ[B] (1 : A) - (1 : A) ⊗ₜ[B] f)) → ∃ b : B, b ≠ 0 ∧ ∀ f ∈ s, ∃ b' : B, algebraMap B A b * f = algebraMap B A b' := by
  intro B A _ _ _ _ _ _ _ hinj s hs
  classical
  haveI : IsReduced B := isReduced_of_injective (algebraMap B A) hinj
  obtain ⟨m, hm⟩ := Ideal.exists_maximal B
  obtain ⟨p, hp, -⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal B)) (J := m) bot_le
  haveI : p.IsPrime := hp.1.1
  haveI : Ring.KrullDimLE 0 (Localization.AtPrime p) :=
    Ring.KrullDimLE.of_isLocalization p hp _
  have hF : IsField (Localization.AtPrime p) := Ring.KrullDimLE.isField_of_isReduced
  have key : ∃ b ∈ p.primeCompl, ∀ f ∈ s, ∃ b' : B, algebraMap B A b * f = algebraMap B A b' := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1, one_mem _, by simp⟩
    | insert a s _ ih =>
      obtain ⟨b, hb, h⟩ := ih (fun f hf => hs f (Finset.mem_insert_of_mem hf))
      obtain ⟨c, hc, c', hc'⟩ := exists_denominator_of_isField_localization B A p.primeCompl hF a
        (hs a (Finset.mem_insert_self _ _))
      refine ⟨b * c, mul_mem hb hc, fun f hf => ?_⟩
      rcases Finset.mem_insert.1 hf with rfl | hf
      · exact ⟨b * c', by rw [map_mul, map_mul, mul_assoc, hc']⟩
      · obtain ⟨b', hb'⟩ := h f hf
        exact ⟨c * b', by rw [map_mul, map_mul, ← hb']; ring⟩
  obtain ⟨b, hb, h⟩ := key
  exact ⟨b, fun h0 => hb (h0 ▸ p.zero_mem), h⟩

end GlobalTheory
end

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_common_denominator_nilpotent_coboundary : ∀ (B A : Type) [CommRing B] [CommRing A] [Algebra ℚ B] [Algebra B A] [Algebra.FiniteType B A] [IsReduced A] [Nontrivial B], Function.Injective (algebraMap B A) → ∀ s : Finset A, (∀ f ∈ s, IsNilpotent (f ⊗ₜ[B] (1 : A) - (1 : A) ⊗ₜ[B] f)) → ∃ b : B, b ≠ 0 ∧ ∀ f ∈ s, ∃ b' : B, algebraMap B A b * f = algebraMap B A b' := by
  atlas_forward_decl GlobalTheory.exists_common_denominator_of_isNilpotent
end

section
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem exists_multiplier_descend_of_closed {σ X : Type} [Fintype σ] [Nonempty X] (p : X → σ → ℂ)
    (hcl : ∀ y : σ → ℂ, (∀ f : MvPolynomial σ ℂ, (∀ x, MvPolynomial.aeval (p x) f = 0) →
      MvPolynomial.aeval y f = 0) → ∃ x, p x = y)
    (q : σ → MvPolynomial σ ℂ) (s : Finset (MvPolynomial σ ℂ))
    (hs : ∀ f ∈ s, ∀ x x', (∀ i, MvPolynomial.aeval (p x) (q i) = MvPolynomial.aeval (p x') (q i)) →
      MvPolynomial.aeval (p x) f = MvPolynomial.aeval (p x') f) :
    ∃ b : MvPolynomial σ ℂ, (∃ x, MvPolynomial.aeval (p x) (MvPolynomial.aeval q b) ≠ 0) ∧
      ∀ f ∈ s, ∃ b' : MvPolynomial σ ℂ, ∀ x,
        MvPolynomial.aeval (p x) (MvPolynomial.aeval q b) * MvPolynomial.aeval (p x) f =
          MvPolynomial.aeval (p x) (MvPolynomial.aeval q b') := by
  classical
  let φ : MvPolynomial σ ℂ →ₐ[ℂ] (X → ℂ) := Pi.algHom ℂ (fun _ => ℂ) fun x => MvPolynomial.aeval (p x)
  have hφ : ∀ f x, φ f x = MvPolynomial.aeval (p x) f := fun _ _ => rfl
  let A : Subalgebra ℂ (X → ℂ) := φ.range
  let π : MvPolynomial σ ℂ →ₐ[ℂ] A := φ.rangeRestrict
  have hπ : Function.Surjective π := φ.rangeRestrict_surjective
  have hπv : ∀ f x, ((π f : A) : X → ℂ) x = MvPolynomial.aeval (p x) f := fun _ _ => rfl
  let B : Subalgebra ℂ A := (π.comp (MvPolynomial.aeval q)).range
  haveI : Algebra.FiniteType ℂ A := Algebra.FiniteType.of_surjective π hπ
  haveI : Algebra.FiniteType B A := Algebra.FiniteType.of_restrictScalars_finiteType ℂ B A
  haveI : IsReduced A := isReduced_of_injective A.val Subtype.val_injective
  letI : Algebra ℚ B := ((algebraMap ℂ B).comp (algebraMap ℚ ℂ)).toAlgebra
  have hpt : ∀ χ : A →ₐ[ℂ] ℂ, ∃ x, ∀ f, χ (π f) = MvPolynomial.aeval (p x) f := by
    intro χ
    have h1 : χ.comp π = MvPolynomial.aeval (fun i => χ (π (MvPolynomial.X i))) := by
      ext i
      simp
    have h2 : ∀ f, χ (π f) = MvPolynomial.aeval (fun i => χ (π (MvPolynomial.X i))) f :=
      fun f => DFunLike.congr_fun h1 f
    obtain ⟨x, hx⟩ := hcl (fun i => χ (π (MvPolynomial.X i))) (by
      intro f hf
      have h0 : π f = 0 := Subtype.ext (funext fun x => hf x)
      rw [← h2, h0, map_zero])
    exact ⟨x, fun f => by rw [h2, hx]⟩
  have hnil : ∀ g ∈ s.image π, IsNilpotent (g ⊗ₜ[B] (1 : A) - (1 : A) ⊗ₜ[B] g) := by
    intro g hg
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hg
    refine GlobalTheory.T.isNilpotent_tmul_sub_tmul_of_const_on_fibres' B A (π f) ?_
    intro χ χ' h
    obtain ⟨x, hx⟩ := hpt χ
    obtain ⟨x', hx'⟩ := hpt χ'
    rw [hx, hx']
    refine hs f hf x x' fun i => ?_
    rw [← hx, ← hx']
    exact h ⟨π (q i), MvPolynomial.X i, by simp⟩
  obtain ⟨b, hb, hbs⟩ := GlobalTheory.T.exists_common_denominator_nilpotent_coboundary B A Subtype.val_injective (s.image π) hnil
  obtain ⟨b, c, rfl⟩ := b
  refine ⟨c, ?_, fun f hf => ?_⟩
  · by_contra hc
    push_neg at hc
    exact hb (Subtype.ext (Subtype.ext (funext fun x => hc x)))
  · obtain ⟨⟨b', c', rfl⟩, hb'⟩ := hbs (π f) (Finset.mem_image_of_mem _ hf)
    exact ⟨c', fun x => congrFun (congrArg Subtype.val hb') x⟩

theorem exists_poly_blk_entries {ι : Type} [Fintype ι] [DecidableEq ι] (e : Matrix ι ι ℚ) :
    ∃ q : ι × ι → MvPolynomial (ι × ι) ℂ, ∀ (x : Matrix ι ι ℂ) (ij : ι × ι),
      MvPolynomial.aeval (fun kl : ι × ι => x kl.1 kl.2) (q ij) = blk e x ij.1 ij.2 := by
  let E : Matrix ι ι (MvPolynomial (ι × ι) ℂ) := (e.map (algebraMap ℚ ℂ)).map MvPolynomial.C
  let Y : Matrix ι ι (MvPolynomial (ι × ι) ℂ) := Matrix.of fun i j => MvPolynomial.X (i, j)
  refine ⟨fun ij => (E * Y * E + (1 - E) * Y * (1 - E)) ij.1 ij.2, fun x ij => ?_⟩
  let ψ : MvPolynomial (ι × ι) ℂ →ₐ[ℂ] ℂ := MvPolynomial.aeval (fun kl : ι × ι => x kl.1 kl.2)
  have hE : ψ.mapMatrix E = e.map (algebraMap ℚ ℂ) := by
    ext i j
    simp [E, ψ]
  have hY : ψ.mapMatrix Y = x := by
    ext i j
    simp [Y, ψ]
  have h : ψ.mapMatrix (E * Y * E + (1 - E) * Y * (1 - E)) = blk e x := by
    simp only [map_add, map_mul, map_sub, map_one, hE, hY, blk]
  rw [← h]
  rfl

theorem exists_multiplier_descend_blk :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (e : Matrix ι ι ℚ), pts Γ ℂ ⊆ Γ → Γ.Nonempty → ∀ s : Finset (MvPolynomial (ι × ι) ℂ), (∀ f ∈ s, ∀ x ∈ Γ, ∀ x' ∈ Γ, blk e x = blk e x' → evC f x = evC f x') → ∃ b : MvPolynomial (ι × ι) ℂ, (∃ x ∈ Γ, evC b (blk e x) ≠ 0) ∧ ∀ f ∈ s, ∃ b' : MvPolynomial (ι × ι) ℂ, ∀ x ∈ Γ, evC b (blk e x) * evC f x = evC b' (blk e x) := by
  intro ι _ _ Γ e hΓ hne s hs
  obtain ⟨q, hq⟩ := exists_poly_blk_entries e
  haveI : Nonempty Γ := hne.to_subtype
  have hev : ∀ (f : MvPolynomial (ι × ι) ℂ) (x : Matrix ι ι ℂ),
      evC f x = MvPolynomial.aeval (fun kl : ι × ι => x kl.1 kl.2) f := fun f x => rfl
  have hcomp : ∀ (b : MvPolynomial (ι × ι) ℂ) (x : Matrix ι ι ℂ),
      MvPolynomial.aeval (fun kl : ι × ι => x kl.1 kl.2) (MvPolynomial.aeval q b) = evC b (blk e x) := by
    intro b x
    rw [hev, ← AlgHom.comp_apply, MvPolynomial.comp_aeval]
    simp only [hq]
  obtain ⟨b, ⟨x₀, hx₀⟩, hb⟩ := exists_multiplier_descend_of_closed
    (fun (x : Γ) (kl : ι × ι) => x.1 kl.1 kl.2) (by
      intro y hy
      refine ⟨⟨Matrix.of fun i j => y (i, j), hΓ fun f hf => ?_⟩, rfl⟩
      have := hy (MvPolynomial.map (algebraMap ℚ ℂ) f) (fun x => by
        rw [MvPolynomial.aeval_map_algebraMap]
        exact hf x.1 x.2)
      rw [MvPolynomial.aeval_map_algebraMap] at this
      exact this) q s (by
      intro f hf x x' h
      refine hs f hf x.1 x.2 x'.1 x'.2 ?_
      ext i j
      have := h (i, j)
      rwa [hq, hq] at this)
  refine ⟨b, ⟨x₀.1, x₀.2, by rwa [hcomp] at hx₀⟩, fun f hf => ?_⟩
  obtain ⟨b', hb'⟩ := hb f hf
  refine ⟨b', fun x hx => ?_⟩
  have := hb' ⟨x, hx⟩
  rw [hcomp, hcomp] at this
  exact this

end GlobalTheory.ClassFin
end

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_multiplier_descend_blockDiagPartOfRatIdempotent : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (e : Matrix ι ι ℚ), pts Γ ℂ ⊆ Γ → Γ.Nonempty → ∀ s : Finset (MvPolynomial (ι × ι) ℂ), (∀ f ∈ s, ∀ x ∈ Γ, ∀ x' ∈ Γ, blk e x = blk e x' → evC f x = evC f x') → ∃ b : MvPolynomial (ι × ι) ℂ, (∃ x ∈ Γ, evC b (blk e x) ≠ 0) ∧ ∀ f ∈ s, ∃ b' : MvPolynomial (ι × ι) ℂ, ∀ x ∈ Γ, evC b (blk e x) * evC f x = evC b' (blk e x) := by
  atlas_forward_decl GlobalTheory.ClassFin.exists_multiplier_descend_blk
end

section
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.FibreDescent

variable {ι : Type} [Fintype ι] [DecidableEq ι]

noncomputable def rtr (g : Matrix ι ι ℂ) : MvPolynomial (ι × ι) ℂ →ₐ[ℂ] MvPolynomial (ι × ι) ℂ :=
  MvPolynomial.aeval fun ij : ι × ι => ∑ k, g k ij.2 • MvPolynomial.X (ij.1, k)

omit [Fintype ι] [DecidableEq ι] in
lemma evC_add (p q : MvPolynomial (ι × ι) ℂ) (y : Matrix ι ι ℂ) : evC (p + q) y = evC p y + evC q y := by
  simp [evC]

omit [Fintype ι] [DecidableEq ι] in
lemma evC_mul (p q : MvPolynomial (ι × ι) ℂ) (y : Matrix ι ι ℂ) : evC (p * q) y = evC p y * evC q y := by
  simp [evC]

omit [Fintype ι] [DecidableEq ι] in
lemma evC_smul (c : ℂ) (p : MvPolynomial (ι × ι) ℂ) (y : Matrix ι ι ℂ) : evC (c • p) y = c * evC p y := by
  simp [evC, MvPolynomial.smul_eval]

omit [DecidableEq ι] in
lemma evC_rtr (g y : Matrix ι ι ℂ) (f : MvPolynomial (ι × ι) ℂ) : evC (rtr g f) y = evC f (y * g) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [evC, rtr]
  | add p q hp hq => rw [map_add, evC_add, evC_add, hp, hq]
  | mul_X p ij hp =>
    rw [map_mul, evC_mul, evC_mul, hp]
    congr 1
    simp [evC, rtr, Matrix.mul_apply, MvPolynomial.smul_eval, mul_comm]

omit [DecidableEq ι] in
lemma evC_ltr (g y : Matrix ι ι ℂ) (f : MvPolynomial (ι × ι) ℂ) : evC (ltr g f) y = evC f (g * y) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [evC, ltr]
  | add p q hp hq => rw [map_add, evC_add, evC_add, hp, hq]
  | mul_X p ij hp =>
    rw [map_mul, evC_mul, evC_mul, hp]
    congr 1
    simp [evC, ltr, Matrix.mul_apply]

omit [Fintype ι] [DecidableEq ι] in
lemma evC_map (p : MvPolynomial (ι × ι) ℚ) (y : Matrix ι ι ℂ) :
    evC (MvPolynomial.map (algebraMap ℚ ℂ) p) y = ev p y := by
  rw [evC, ev, MvPolynomial.eval_map, MvPolynomial.aeval_def]

omit [DecidableEq ι] in

lemma exists_fg_rtr (f : MvPolynomial (ι × ι) ℂ) :
    ∃ V : Submodule ℂ (MvPolynomial (ι × ι) ℂ), V.FG ∧ ∀ g, rtr g f ∈ V := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    refine ⟨Submodule.span ℂ {MvPolynomial.C a}, Submodule.fg_span (Set.finite_singleton _), fun g => ?_⟩
    apply Submodule.subset_span
    simp [rtr]
  | add p q hp hq =>
    obtain ⟨V, hV, h⟩ := hp
    obtain ⟨V', hV', h'⟩ := hq
    refine ⟨V ⊔ V', hV.sup hV', fun g => ?_⟩
    rw [map_add]
    exact Submodule.add_mem_sup (h g) (h' g)
  | mul_X p ij hp =>
    obtain ⟨V, hV, h⟩ := hp
    refine ⟨V * Submodule.span ℂ (Set.range MvPolynomial.X),
      hV.mul (Submodule.fg_span (Set.finite_range _)), fun g => ?_⟩
    rw [map_mul]
    refine Submodule.mul_mem_mul (h g) ?_
    rw [rtr, MvPolynomial.aeval_X]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

omit [DecidableEq ι] in

lemma exists_finset_rtr (Γ : Set (Matrix ι ι ℂ)) (f : MvPolynomial (ι × ι) ℂ) :
    ∃ s : Finset (MvPolynomial (ι × ι) ℂ), (∀ p ∈ s, ∃ g ∈ Γ, p = rtr g f) ∧
      ∀ g ∈ Γ, rtr g f ∈ Submodule.span ℂ (s : Set (MvPolynomial (ι × ι) ℂ)) := by
  obtain ⟨V, hV, h⟩ := exists_fg_rtr f
  have hle : Submodule.span ℂ ((fun g => rtr g f) '' Γ) ≤ V := by
    rw [Submodule.span_le]
    rintro _ ⟨g, -, rfl⟩
    exact h g
  have hfg : (Submodule.span ℂ ((fun g => rtr g f) '' Γ)).FG := by
    have : Module.Finite ℂ V := Module.Finite.iff_fg.2 hV
    exact Module.Finite.iff_fg.1 (Submodule.finiteDimensional_of_le hle)
  obtain ⟨s, hs, hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).1 hfg
  refine ⟨s, fun p hp => ?_, fun g hg => ?_⟩
  · obtain ⟨g, hg, rfl⟩ := hs hp
    exact ⟨g, hg, rfl⟩
  · rw [← hspan]
    exact Submodule.subset_span ⟨g, hg, rfl⟩

def multIdeal (Γ : Set (Matrix ι ι ℂ)) (π : Matrix ι ι ℂ → Matrix ι ι ℂ) (f : MvPolynomial (ι × ι) ℂ) :
    Ideal (MvPolynomial (ι × ι) ℂ) where
  carrier := {b | ∀ g ∈ Γ, ∃ b' : MvPolynomial (ι × ι) ℂ, ∀ x ∈ Γ,
    evC b (π x) * evC f (x * g) = evC b' (π x)}
  zero_mem' := fun g _ => ⟨0, fun x _ => by simp [evC]⟩
  add_mem' := by
    intro a b ha hb g hg
    obtain ⟨a', ha'⟩ := ha g hg
    obtain ⟨b', hb'⟩ := hb g hg
    exact ⟨a' + b', fun x hx => by rw [evC_add, evC_add, add_mul, ha' x hx, hb' x hx]⟩
  smul_mem' := by
    intro c b hb g hg
    obtain ⟨b', hb'⟩ := hb g hg
    exact ⟨c * b', fun x hx => by rw [smul_eq_mul, evC_mul, evC_mul, mul_assoc, hb' x hx]⟩

omit [DecidableEq ι] in
lemma exists_common_zero (D : Ideal (MvPolynomial (ι × ι) ℂ)) (hD : D ≠ ⊤) :
    ∃ z : Matrix ι ι ℂ, ∀ b ∈ D, evC b z = 0 := by
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal D hD
  obtain ⟨x, rfl⟩ := MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton.1 hM
  refine ⟨Matrix.of fun i j => x (i, j), fun b hb => ?_⟩
  have := (MvPolynomial.mem_vanishingIdeal_singleton_iff _ _).1 (hle hb)
  simpa [evC, MvPolynomial.aeval_eq_eval] using this

end GlobalTheory.ClassFin.FibreDescent

open GlobalTheory.ClassFin.FibreDescent in

theorem GlobalTheory.ClassFin.exists_evC_blk_of_fibre_const : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (e : Matrix ι ι ℚ), IsQGroup Γ → e * e = e → (∀ g ∈ Γ, (1 - e.map (algebraMap ℚ ℂ)) * g * e.map (algebraMap ℚ ℂ) = 0) → ∀ f : MvPolynomial (ι × ι) ℂ, (∀ x ∈ Γ, ∀ x' ∈ Γ, blk e x = blk e x' → evC f x = evC f x') → ∃ b : MvPolynomial (ι × ι) ℂ, ∀ x ∈ Γ, evC f x = evC b (blk e x) := by
  intro ι _ _ Γ e hΓ he htri f hf
  have hmul : ∀ x ∈ Γ, ∀ y ∈ Γ, blk e (x * y) = blk e x * blk e y := fun x hx y hy =>
    ((GlobalTheory.ClassFin.blk_mul_of_triangular ι e ℂ he).2.1 x y (htri x hx) (htri y hy)).1
  have hpre : IsPre (blk e '' Γ) := GlobalTheory.ClassFin.isPre_blk_image ι Γ e hΓ.toIsPre he htri
  obtain ⟨-, hm, hadj, hdet⟩ := GlobalTheory.T.ratZariskiClosurePoints_isGroup ι _ hpre ℂ
  obtain ⟨s, hs, hspan⟩ := exists_finset_rtr Γ f
  obtain ⟨b₀, ⟨x₀, hx₀, hb₀⟩, hb⟩ := GlobalTheory.T.exists_multiplier_descend_blockDiagPartOfRatIdempotent ι Γ e hΓ.closed ⟨1, hΓ.one_mem⟩ s (by
    intro p hp x hx x' hx' hxx
    obtain ⟨g, hg, rfl⟩ := hs p hp
    rw [evC_rtr, evC_rtr]
    exact hf _ (hΓ.mul_mem _ hx _ hg) _ (hΓ.mul_mem _ hx' _ hg)
      (by rw [hmul _ hx _ hg, hmul _ hx' _ hg, hxx]))
  have hb₀D : b₀ ∈ multIdeal Γ (blk e) f := by
    intro g hg
    have key : ∀ p ∈ Submodule.span ℂ (s : Set (MvPolynomial (ι × ι) ℂ)),
        ∃ b' : MvPolynomial (ι × ι) ℂ, ∀ x ∈ Γ, evC b₀ (blk e x) * evC p x = evC b' (blk e x) := by
      intro p hp
      induction hp using Submodule.span_induction with
      | mem p hp => exact hb p hp
      | zero => exact ⟨0, fun x _ => by simp [evC]⟩
      | add p q _ _ hp hq =>
        obtain ⟨a', ha'⟩ := hp
        obtain ⟨b', hb'⟩ := hq
        exact ⟨a' + b', fun x hx => by rw [evC_add, evC_add, mul_add, ha' x hx, hb' x hx]⟩
      | smul c p _ hp =>
        obtain ⟨a', ha'⟩ := hp
        exact ⟨c • a', fun x hx => by rw [evC_smul, evC_smul, ← ha' x hx]; ring⟩
    obtain ⟨b', hb'⟩ := key _ (hspan g hg)
    exact ⟨b', fun x hx => by rw [← hb' x hx, evC_rtr]⟩
  have hstab : ∀ h ∈ Γ, rtr (blk e h) b₀ ∈ multIdeal Γ (blk e) f := by
    intro h hh g hg
    obtain ⟨b', hb'⟩ := hb₀D (h.adjugate * g) (hΓ.mul_mem _ (hΓ.adj_mem _ hh) _ hg)
    refine ⟨rtr (blk e h) b', fun x hx => ?_⟩
    rw [evC_rtr, evC_rtr, ← hmul _ hx _ hh, ← hb' _ (hΓ.mul_mem _ hx _ hh), Matrix.mul_assoc,
      ← Matrix.mul_assoc h, Matrix.mul_adjugate, hΓ.det_eq _ hh, one_smul, Matrix.one_mul]
  have htop : multIdeal Γ (blk e) f = ⊤ := by
    by_contra hD
    obtain ⟨z, hz⟩ := exists_common_zero _ hD
    have hzp : z ∈ pts (blk e '' Γ) ℂ := by
      intro p hp
      rw [← evC_map]
      refine hz _ fun g _ => ⟨0, fun x hx => ?_⟩
      rw [evC_map, hp _ ⟨x, hx, rfl⟩]
      simp [evC]
    have hx₀p : blk e x₀ ∈ pts (blk e '' Γ) ℂ := fun p hp => hp _ ⟨x₀, hx₀, rfl⟩
    have := GlobalTheory.T.evalComplexPoly_eq_zero_on_ratZariskiClosure ι _ hpre.aut_mem (ltr z b₀) (by
      rintro _ ⟨h, hh, rfl⟩
      rw [evC_ltr, ← evC_rtr]
      exact hz _ (hstab h hh)) _ (hm _ (hadj z hzp) _ hx₀p)
    rw [evC_ltr, ← Matrix.mul_assoc, Matrix.mul_adjugate, hdet z hzp, one_smul, Matrix.one_mul] at this
    exact hb₀ this
  have h1 : (1 : MvPolynomial (ι × ι) ℂ) ∈ multIdeal Γ (blk e) f := htop ▸ Submodule.mem_top
  obtain ⟨b, hb⟩ := h1 1 hΓ.one_mem
  refine ⟨b, fun x hx => ?_⟩
  rw [← hb x hx, Matrix.mul_one]
  simp [evC]
end

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_complexPoly_blockDiagPart_of_fibre_const : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (e : Matrix ι ι ℚ), IsQGroup Γ → e * e = e → (∀ g ∈ Γ, (1 - e.map (algebraMap ℚ ℂ)) * g * e.map (algebraMap ℚ ℂ) = 0) → ∀ f : MvPolynomial (ι × ι) ℂ, (∀ x ∈ Γ, ∀ x' ∈ Γ, blk e x = blk e x' → evC f x = evC f x') → ∃ b : MvPolynomial (ι × ι) ℂ, ∀ x ∈ Γ, evC f x = evC b (blk e x) := by
  atlas_forward_decl GlobalTheory.ClassFin.exists_evC_blk_of_fibre_const
end

section
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem exists_component_subst {σ : Type} (s : σ → MvPolynomial σ ℚ) (l : ℂ →ₗ[ℚ] ℚ)
    (b : MvPolynomial σ ℂ) :
    ∃ b' : MvPolynomial σ ℚ, ∀ m, MvPolynomial.coeff m (MvPolynomial.aeval s b') =
      l (MvPolynomial.coeff m
        (MvPolynomial.aeval (fun i => MvPolynomial.map (algebraMap ℚ ℂ) (s i)) b)) := by
  induction b using MvPolynomial.induction_on' with
  | monomial u a =>
    refine ⟨MvPolynomial.monomial u (l a), fun m => ?_⟩
    rw [MvPolynomial.aeval_monomial, MvPolynomial.aeval_monomial]
    have h : (u.prod fun i k => (MvPolynomial.map (algebraMap ℚ ℂ) (s i)) ^ k) =
        MvPolynomial.map (algebraMap ℚ ℂ) (u.prod fun i k => s i ^ k) := by
      simp [Finsupp.prod, map_prod, map_pow]
    rw [h, MvPolynomial.algebraMap_eq, MvPolynomial.algebraMap_eq, MvPolynomial.coeff_C_mul,
      MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map, mul_comm a, ← Algebra.smul_def, map_smul,
      smul_eq_mul, mul_comm]
  | add p q hp hq =>
    obtain ⟨p', hp'⟩ := hp
    obtain ⟨q', hq'⟩ := hq
    refine ⟨p' + q', fun m => ?_⟩
    rw [map_add, map_add, MvPolynomial.coeff_add, MvPolynomial.coeff_add, map_add, hp', hq']

theorem exists_poly_blk {ι : Type} [Fintype ι] [DecidableEq ι] (e : Matrix ι ι ℚ) :
    ∃ s : ι × ι → MvPolynomial (ι × ι) ℚ, ∀ (x : Matrix ι ι ℂ) (ij : ι × ι),
      ev (s ij) x = blk e x ij.1 ij.2 := by
  refine ⟨fun ij => blk e (Matrix.of fun i j => (MvPolynomial.X (i, j) : MvPolynomial (ι × ι) ℚ)) ij.1 ij.2,
    fun x ij => ?_⟩
  set φ : MvPolynomial (ι × ι) ℚ →ₐ[ℚ] ℂ := MvPolynomial.aeval (fun ij : ι × ι => x ij.1 ij.2) with hφ
  have h1 : φ.mapMatrix (e.map (algebraMap ℚ (MvPolynomial (ι × ι) ℚ))) = e.map (algebraMap ℚ ℂ) := by
    ext i j
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, AlgHom.commutes]
  have h2 : φ.mapMatrix (Matrix.of fun i j => (MvPolynomial.X (i, j) : MvPolynomial (ι × ι) ℚ)) = x := by
    ext i j
    simp [hφ]
  have h3 : φ.mapMatrix (blk e (Matrix.of fun i j => (MvPolynomial.X (i, j) : MvPolynomial (ι × ι) ℚ)))
      = blk e x := by
    unfold blk
    simp only [map_add, map_mul, map_sub, map_one, h1, h2]
  rw [← h3]
  rfl

theorem descend_blk_rat : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (e : Matrix ι ι ℚ), IsQGroup Γ → e * e = e → (∀ g ∈ Γ, (1 - e.map (algebraMap ℚ ℂ)) * g * e.map (algebraMap ℚ ℂ) = 0) → ∀ f : MvPolynomial (ι × ι) ℚ, (∀ x ∈ Γ, ∀ x' ∈ Γ, blk e x = blk e x' → ev f x = ev f x') → ∃ b : MvPolynomial (ι × ι) ℚ, ∀ x ∈ Γ, ev f x = ev b (blk e x) := by
  intro ι _ _ Γ e hΓ he hpar f hf
  have hmap : ∀ (p : MvPolynomial (ι × ι) ℚ) (x : Matrix ι ι ℂ),
      evC (MvPolynomial.map (algebraMap ℚ ℂ) p) x = ev p x := by
    intro p x
    unfold evC ev
    rw [MvPolynomial.eval_map, MvPolynomial.aeval_def]
  obtain ⟨b, hb⟩ := GlobalTheory.T.exists_complexPoly_blockDiagPart_of_fibre_const ι Γ e hΓ he hpar (MvPolynomial.map (algebraMap ℚ ℂ) f)
    (fun x hx x' hx' h => by rw [hmap, hmap]; exact hf x hx x' hx' h)
  obtain ⟨s, hs⟩ := exists_poly_blk e
  obtain ⟨l, hl⟩ : ∃ l : ℂ →ₗ[ℚ] ℚ, l 1 = 1 := by
    obtain ⟨l, hl⟩ := (Algebra.linearMap ℚ ℂ).exists_leftInverse_of_injective
      (LinearMap.ker_eq_bot.mpr (algebraMap ℚ ℂ).injective)
    refine ⟨l, ?_⟩
    have := LinearMap.congr_fun hl 1
    simpa using this
  obtain ⟨b', hb'⟩ := exists_component_subst s l b
  have hsubC : ∀ x : Matrix ι ι ℂ,
      evC (MvPolynomial.aeval (fun i => MvPolynomial.map (algebraMap ℚ ℂ) (s i)) b) x = evC b (blk e x) := by
    intro x
    have h : (fun ij : ι × ι => blk e x ij.1 ij.2) =
        fun ij => MvPolynomial.aeval (fun ij : ι × ι => x ij.1 ij.2) (MvPolynomial.map (algebraMap ℚ ℂ) (s ij)) := by
      funext ij
      rw [← hs, ← hmap]
      rfl
    unfold evC
    rw [h, ← MvPolynomial.coe_aeval_eq_eval, ← MvPolynomial.coe_aeval_eq_eval, RingHom.coe_coe, RingHom.coe_coe,
      ← MvPolynomial.comp_aeval]
    rfl
  have hsub : ∀ x : Matrix ι ι ℂ, ev (MvPolynomial.aeval s b') x = ev b' (blk e x) := by
    intro x
    have h : (fun ij : ι × ι => blk e x ij.1 ij.2) =
        fun ij => MvPolynomial.aeval (fun ij : ι × ι => x ij.1 ij.2) (s ij) := by
      funext ij
      rw [← hs]
      rfl
    unfold ev
    rw [h, ← MvPolynomial.comp_aeval]
    rfl
  have hvan := GlobalTheory.T.rat_component_mem_ratPolysVanishingOnMatrixSet ι Γ hΓ.aut_mem
    (MvPolynomial.map (algebraMap ℚ ℂ) f -
      MvPolynomial.aeval (fun i => MvPolynomial.map (algebraMap ℚ ℂ) (s i)) b)
    (fun g hg => by
      have h1 := hb g hg
      rw [← hsubC] at h1
      unfold evC at h1 ⊢
      rw [map_sub, h1, sub_self])
    l (f - MvPolynomial.aeval s b')
    (fun m => by
      rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_sub, map_sub, hb', MvPolynomial.coeff_map,
        Algebra.algebraMap_eq_smul_one, map_smul, hl, smul_eq_mul, mul_one])
  refine ⟨b', fun x hx => ?_⟩
  have h1 := hvan x hx
  rw [← hsub]
  unfold ev at h1 ⊢
  rw [map_sub] at h1
  exact sub_eq_zero.mp h1

end GlobalTheory.ClassFin
end

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.descend_blockDiagPart_ratPoly_of_fibre_const : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (e : Matrix ι ι ℚ), IsQGroup Γ → e * e = e → (∀ g ∈ Γ, (1 - e.map (algebraMap ℚ ℂ)) * g * e.map (algebraMap ℚ ℂ) = 0) → ∀ f : MvPolynomial (ι × ι) ℚ, (∀ x ∈ Γ, ∀ x' ∈ Γ, blk e x = blk e x' → ev f x = ev f x') → ∃ b : MvPolynomial (ι × ι) ℚ, ∀ x ∈ Γ, ev f x = ev b (blk e x) := by
  atlas_forward_decl GlobalTheory.ClassFin.descend_blk_rat
end

section
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.IdempotentCornerSection

section ring
variable {A : Type} [Ring A] {E : A}

lemma corner_mul (hE : E * E = E) {x y : A} (hx : E * x * (1 - E) = x) (hy : E * y * (1 - E) = y) :
    x * y = 0 := by
  have h : (1 - E) * E = 0 := by rw [sub_mul, one_mul, hE, sub_self]
  calc x * y = (E * x * (1 - E)) * (E * y * (1 - E)) := by rw [hx, hy]
    _ = E * x * ((1 - E) * E) * y * (1 - E) := by noncomm_ring
    _ = 0 := by rw [h]; simp

lemma diag_comm (hE : E * E = E) (g : A) :
    E * (E * g * E + (1 - E) * g * (1 - E)) = (E * g * E + (1 - E) * g * (1 - E)) * E := by
  have h : (1 - E) * E = 0 := by rw [sub_mul, one_mul, hE, sub_self]
  have h' : E * (1 - E) = 0 := by rw [mul_sub, mul_one, hE, sub_self]
  calc E * (E * g * E + (1 - E) * g * (1 - E))
      = (E * E) * g * E + (E * (1 - E)) * g * (1 - E) := by simp only [mul_add, mul_assoc]
    _ = E * g * (E * E) + (1 - E) * g * ((1 - E) * E) := by rw [hE, h, h']; simp
    _ = _ := by simp only [add_mul, mul_assoc]

lemma corner_mul_comm {x D : A} (hD : E * D = D * E) (hx : E * x * (1 - E) = x) :
    E * (x * D) * (1 - E) = x * D := by
  have h : D * (1 - E) = (1 - E) * D := by rw [mul_sub, sub_mul, hD, mul_one, one_mul]
  calc E * (x * D) * (1 - E) = E * x * (D * (1 - E)) := by simp only [mul_assoc]
    _ = E * x * (1 - E) * D := by rw [h]; simp only [mul_assoc]
    _ = x * D := by rw [hx]

lemma corner_idem (hE : E * E = E) (g : A) : E * (E * g * (1 - E)) * (1 - E) = E * g * (1 - E) := by
  have h : (1 - E) * (1 - E) = 1 - E := by
    rw [sub_mul, one_mul, mul_sub, mul_one, hE, sub_self, sub_zero]
  calc E * (E * g * (1 - E)) * (1 - E) = (E * E) * g * ((1 - E) * (1 - E)) := by simp only [mul_assoc]
    _ = _ := by rw [hE, h]

lemma corner_diag (hE : E * E = E) {x : A} (hx : E * x * (1 - E) = x) :
    E * x * E + (1 - E) * x * (1 - E) = 0 := by
  have h : (1 - E) * E = 0 := by rw [sub_mul, one_mul, hE, sub_self]
  calc E * x * E + (1 - E) * x * (1 - E)
      = E * (E * x * (1 - E)) * E + (1 - E) * (E * x * (1 - E)) * (1 - E) := by rw [hx]
    _ = E * E * x * ((1 - E) * E) + ((1 - E) * E) * x * (1 - E) * (1 - E) := by simp only [mul_assoc]
    _ = 0 := by rw [h]; simp

lemma inv_comm {D D' : A} (hD : E * D = D * E) (h1 : D * D' = 1) (h2 : D' * D = 1) :
    E * D' = D' * E := by
  calc E * D' = (D' * D) * E * D' := by rw [h2, one_mul]
    _ = D' * (D * E) * D' := by simp only [mul_assoc]
    _ = D' * E * (D * D') := by rw [← hD]; simp only [mul_assoc]
    _ = D' * E := by rw [h1, mul_one]

end ring

variable {ι : Type} [Fintype ι] [DecidableEq ι]

noncomputable def beta {R : Type} [CommRing R] [Algebra ℚ R] (e : Matrix ι ι ℚ) (g : Matrix ι ι R) :
    Matrix ι ι R :=
  e.map (algebraMap ℚ R) * g * (1 - e.map (algebraMap ℚ R)) * (blk e g).adjugate

noncomputable def sec {R : Type} [CommRing R] [Algebra ℚ R] (e : Matrix ι ι ℚ) (c : ι × ι → ι × ι → ℚ)
    (g : Matrix ι ι R) : Matrix ι ι R :=
  (1 - linExt c (beta e g)) * g

section natural
variable {R S : Type} [CommRing R] [Algebra ℚ R] [CommRing S] [Algebra ℚ S] (φ : R →ₐ[ℚ] S)

lemma map_rat (e : Matrix ι ι ℚ) :
    φ.mapMatrix (e.map (algebraMap ℚ R)) = e.map (algebraMap ℚ S) := by
  ext i j; simp [AlgHom.mapMatrix_apply, -eq_ratCast]

lemma map_blk (e : Matrix ι ι ℚ) (g : Matrix ι ι R) :
    φ.mapMatrix (blk e g) = blk e (φ.mapMatrix g) := by
  simp only [blk, map_add, map_mul, map_sub, map_one, map_rat]

lemma map_linExt (c : ι × ι → ι × ι → ℚ) (g : Matrix ι ι R) :
    φ.mapMatrix (linExt c g) = linExt c (φ.mapMatrix g) := by
  ext i j; simp [linExt, AlgHom.mapMatrix_apply, map_sum, -eq_ratCast]

lemma map_sec (e : Matrix ι ι ℚ) (c : ι × ι → ι × ι → ℚ) (g : Matrix ι ι R) :
    φ.mapMatrix (sec e c g) = sec e c (φ.mapMatrix g) := by
  simp only [sec, beta, map_mul, map_sub, map_one, map_rat, map_linExt, AlgHom.map_adjugate, map_blk]

end natural

lemma exists_poly (e : Matrix ι ι ℚ) (c : ι × ι → ι × ι → ℚ) :
    ∃ f : ι → ι → MvPolynomial (ι × ι) ℚ, ∀ (g : Matrix ι ι ℂ) i j, ev (f i j) g = sec e c g i j := by
  refine ⟨fun i j => sec e c (Matrix.of fun k l => (MvPolynomial.X (k, l) : MvPolynomial (ι × ι) ℚ)) i j,
    fun g i j => ?_⟩
  have h := map_sec (MvPolynomial.aeval (R := ℚ) (fun ij : ι × ι => g ij.1 ij.2)) e c
    (Matrix.of fun k l => (MvPolynomial.X (k, l) : MvPolynomial (ι × ι) ℚ))
  have h2 : (MvPolynomial.aeval (R := ℚ) (fun ij : ι × ι => g ij.1 ij.2)).mapMatrix
      (Matrix.of fun k l => (MvPolynomial.X (k, l) : MvPolynomial (ι × ι) ℚ)) = g := by
    ext k l; simp [AlgHom.mapMatrix_apply]
  rw [h2] at h
  rw [← h]; rfl

lemma linExt_sub (c : ι × ι → ι × ι → ℚ) (x y : Matrix ι ι ℂ) :
    linExt c (x - y) = linExt c x - linExt c y := by
  ext i j; simp [linExt, mul_sub, Finset.sum_sub_distrib]

lemma linExt_zero (c : ι × ι → ι × ι → ℚ) : linExt c (0 : Matrix ι ι ℂ) = 0 := by
  ext i j; simp [linExt]

end GlobalTheory.ClassFin.IdempotentCornerSection

open GlobalTheory.ClassFin.IdempotentCornerSection in

theorem GlobalTheory.ClassFin.exists_blk_section : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (e : Matrix ι ι ℚ), IsQGroup Γ → e * e = e → (∀ g ∈ Γ, (1 - e.map (algebraMap ℚ ℂ)) * g * e.map (algebraMap ℚ ℂ) = 0) → ∃ (c : ι × ι → ι × ι → ℚ) (b : ι → ι → MvPolynomial (ι × ι) ℚ), (∀ X : Matrix ι ι ℂ, 1 + linExt c X ∈ Γ ∧ e.map (algebraMap ℚ ℂ) * linExt c X * (1 - e.map (algebraMap ℚ ℂ)) = linExt c X) ∧ (Matrix.of fun i j => ev (b i j) (1 : Matrix ι ι ℂ)) = 1 ∧ ∀ g ∈ Γ, (Matrix.of fun i j => ev (b i j) (blk e g)) ∈ Γ ∧ blk e (Matrix.of fun i j => ev (b i j) (blk e g)) = blk e g ∧ g = (1 + linExt c (e.map (algebraMap ℚ ℂ) * g * (1 - e.map (algebraMap ℚ ℂ)) * (blk e g).adjugate)) * (Matrix.of fun i j => ev (b i j) (blk e g)) := by
  intro ι _ _ Γ e hΓ he htri
  obtain ⟨c, hc, hfix⟩ := GlobalTheory.T.exists_rat_linear_param_blockDiag_kernel ι Γ e hΓ he
  have hpre := GlobalTheory.T.isAutStableSLMatrixGroup_image_blockDiagPart ι Γ e hΓ.toIsPre he htri
  obtain ⟨hb1, -, hdec, hbb, -⟩ := GlobalTheory.T.blockDiagPartOfRatIdempotent_one_and_mul_of_triangular ι e ℂ he
  obtain ⟨f, hf⟩ := exists_poly e c
  have hE : e.map (algebraMap ℚ ℂ) * e.map (algebraMap ℚ ℂ) = e.map (algebraMap ℚ ℂ) := by
    rw [← Matrix.map_mul, he]
  have hcomm : ∀ g : Matrix ι ι ℂ, e.map (algebraMap ℚ ℂ) * blk e g = blk e g * e.map (algebraMap ℚ ℂ) :=
    fun g => diag_comm hE g
  have hdet : ∀ g ∈ Γ, (blk e g).det = 1 := fun g hg => hpre.det_eq _ ⟨g, hg, rfl⟩
  have h1 : ∀ g ∈ Γ, blk e g * (blk e g).adjugate = 1 := fun g hg => by
    rw [Matrix.mul_adjugate, hdet g hg, one_smul]
  have h2 : ∀ g ∈ Γ, (blk e g).adjugate * blk e g = 1 := fun g hg => by
    rw [Matrix.adjugate_mul, hdet g hg, one_smul]
  have hβ : ∀ g ∈ Γ, e.map (algebraMap ℚ ℂ) * beta e g * (1 - e.map (algebraMap ℚ ℂ)) = beta e g :=
    fun g hg => corner_mul_comm (inv_comm (hcomm g) (h1 g hg) (h2 g hg)) (corner_idem hE g)
  have hg1 : ∀ g ∈ Γ, g = (1 + beta e g) * blk e g := fun g hg => by
    rw [add_mul, one_mul, beta, mul_assoc _ _ (blk e g), h2 g hg, mul_one]
    exact hdec g (htri g hg)
  have hs : ∀ g ∈ Γ, sec e c g = (1 + (beta e g - linExt c (beta e g))) * blk e g := fun g hg => by
    have h0 := corner_mul hE (hc (beta e g)).2 (hβ g hg)
    have : sec e c g = (1 - linExt c (beta e g)) * ((1 + beta e g) * blk e g) := by
      rw [← hg1 g hg]; rfl
    rw [this, ← mul_assoc]
    congr 1
    rw [mul_add, sub_mul, sub_mul, h0]
    simp only [mul_one, one_mul, sub_zero]
    abel
  have hsub : ∀ x y : Matrix ι ι ℂ, e.map (algebraMap ℚ ℂ) * x * (1 - e.map (algebraMap ℚ ℂ)) = x →
      e.map (algebraMap ℚ ℂ) * y * (1 - e.map (algebraMap ℚ ℂ)) = y →
      e.map (algebraMap ℚ ℂ) * (x - y) * (1 - e.map (algebraMap ℚ ℂ)) = x - y := fun x y hx hy => by
    rw [mul_sub (e.map (algebraMap ℚ ℂ)) x y, sub_mul, hx, hy]
  have hconst : ∀ x ∈ Γ, ∀ x' ∈ Γ, blk e x = blk e x' → sec e c x = sec e c x' := by
    intro x hx x' hx' hxx
    have hε := hsub _ _ (hβ x hx) (hβ x' hx')
    have h0 := corner_mul hE hε (hβ x' hx')
    have hxe : x = (1 + (beta e x - beta e x')) * x' := by
      have : (1 + (beta e x - beta e x')) * x'
          = (1 + (beta e x - beta e x')) * ((1 + beta e x') * blk e x') := by rw [← hg1 x' hx']
      rw [this, ← mul_assoc, ← hxx]
      have h3 : (1 + (beta e x - beta e x')) * (1 + beta e x') = 1 + beta e x := by
        rw [mul_add, add_mul _ _ (beta e x'), h0]
        simp only [mul_one, one_mul, add_zero]
        abel
      rw [h3]; exact hg1 x hx
    have hmem : 1 + (beta e x - beta e x') ∈ Γ := by
      have h4 : x * x'.adjugate = 1 + (beta e x - beta e x') := by
        have : x * x'.adjugate = ((1 + (beta e x - beta e x')) * x') * x'.adjugate := by rw [← hxe]
        rw [this, mul_assoc, Matrix.mul_adjugate, hΓ.det_eq x' hx', one_smul, mul_one]
      rw [← h4]
      exact hΓ.mul_mem _ hx _ (hΓ.adj_mem _ hx')
    have h5 := hfix _ hmem hε
    rw [linExt_sub] at h5
    rw [hs x hx, hs x' hx', hxx]
    congr 2
    rw [sub_eq_iff_eq_add.mp h5]
    abel
  have hb : ∀ i j, ∃ b : MvPolynomial (ι × ι) ℚ, ∀ x ∈ Γ, ev (f i j) x = ev b (blk e x) := fun i j =>
    GlobalTheory.T.descend_blockDiagPart_ratPoly_of_fibre_const ι Γ e hΓ he htri (f i j) fun x hx x' hx' hxx => by
      rw [hf, hf, hconst x hx x' hx' hxx]
  choose b hb using hb
  have hbs : ∀ g ∈ Γ, (Matrix.of fun i j => ev (b i j) (blk e g)) = sec e c g := fun g hg => by
    ext i j; rw [Matrix.of_apply, ← hb i j g hg, hf]
  refine ⟨c, b, hc, ?_, fun g hg => ?_⟩
  · have h := hbs 1 hΓ.one_mem
    rw [hb1] at h
    rw [h]
    have h0 : beta e (1 : Matrix ι ι ℂ) = 0 := by
      rw [beta, mul_one, mul_sub, mul_one, hE, sub_self, zero_mul]
    rw [sec, h0, linExt_zero, sub_zero, mul_one]
  · rw [hbs g hg]
    refine ⟨?_, ?_, ?_⟩
    · have h := (hc (0 - beta e g)).1
      rw [linExt_sub, linExt_zero, ← add_sub_assoc, add_zero] at h
      exact hΓ.mul_mem _ h _ hg
    · have h := corner_diag hE (corner_mul_comm (hcomm g) (hsub _ _ (hβ g hg) (hc (beta e g)).2))
      have h' := hbb g
      rw [hs g hg, add_mul, one_mul]
      generalize (beta e g - linExt c (beta e g)) * blk e g = y at h
      generalize blk e g = D at h' ⊢
      have : blk e (D + y) = blk e D + (e.map (algebraMap ℚ ℂ) * y * e.map (algebraMap ℚ ℂ) +
          (1 - e.map (algebraMap ℚ ℂ)) * y * (1 - e.map (algebraMap ℚ ℂ))) := by
        simp only [blk, mul_add, add_mul]; abel
      rw [this, h, h', add_zero]
    · have h0 := corner_mul hE (hc (beta e g)).2 (hc (beta e g)).2
      change g = (1 + linExt c (beta e g)) * ((1 - linExt c (beta e g)) * g)
      rw [← mul_assoc, mul_sub, add_mul _ _ (linExt c (beta e g)), h0]
      simp
end

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_polynomial_section_blockDiagonal_map : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (e : Matrix ι ι ℚ), IsQGroup Γ → e * e = e → (∀ g ∈ Γ, (1 - e.map (algebraMap ℚ ℂ)) * g * e.map (algebraMap ℚ ℂ) = 0) → ∃ (c : ι × ι → ι × ι → ℚ) (b : ι → ι → MvPolynomial (ι × ι) ℚ), (∀ X : Matrix ι ι ℂ, 1 + linExt c X ∈ Γ ∧ e.map (algebraMap ℚ ℂ) * linExt c X * (1 - e.map (algebraMap ℚ ℂ)) = linExt c X) ∧ (Matrix.of fun i j => ev (b i j) (1 : Matrix ι ι ℂ)) = 1 ∧ ∀ g ∈ Γ, (Matrix.of fun i j => ev (b i j) (blk e g)) ∈ Γ ∧ blk e (Matrix.of fun i j => ev (b i j) (blk e g)) = blk e g ∧ g = (1 + linExt c (e.map (algebraMap ℚ ℂ) * g * (1 - e.map (algebraMap ℚ ℂ)) * (blk e g).adjugate)) * (Matrix.of fun i j => ev (b i j) (blk e g)) := by
  atlas_forward_decl GlobalTheory.ClassFin.exists_blk_section
end

section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.PolySection

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def IsNatural (F : ∀ (R : Type) [CommRing R] [Algebra ℚ R], Matrix ι ι R → Matrix ι ι R) : Prop :=
  ∀ (R S : Type) [CommRing R] [Algebra ℚ R] [CommRing S] [Algebra ℚ S] (φ : R →ₐ[ℚ] S) (x : Matrix ι ι R),
    φ.mapMatrix (F R x) = F S (φ.mapMatrix x)

noncomputable def evHom {R : Type} [CommRing R] [Algebra ℚ R] (y : Matrix ι ι R) :
    MvPolynomial (ι × ι) ℚ →ₐ[ℚ] R :=
  MvPolynomial.aeval (fun ij : ι × ι => y ij.1 ij.2)

theorem evHom_generic {R : Type} [CommRing R] [Algebra ℚ R] (y : Matrix ι ι R) :
    (evHom y).mapMatrix (Matrix.mvPolynomialX ι ι ℚ) = y := by
  ext i j
  simp [evHom, Matrix.mvPolynomialX]

theorem map_ev {R S : Type} [CommRing R] [Algebra ℚ R] [CommRing S] [Algebra ℚ S] (φ : R →ₐ[ℚ] S)
    (f : MvPolynomial (ι × ι) ℚ) (x : Matrix ι ι R) : φ (ev f x) = ev f (φ.mapMatrix x) := by
  unfold ev
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  rfl

theorem map_rat {R S : Type} [CommRing R] [Algebra ℚ R] [CommRing S] [Algebra ℚ S] (φ : R →ₐ[ℚ] S)
    (e : Matrix ι ι ℚ) : φ.mapMatrix (e.map (algebraMap ℚ R)) = e.map (algebraMap ℚ S) := by
  ext i j
  exact φ.commutes _

theorem map_blk {R S : Type} [CommRing R] [Algebra ℚ R] [CommRing S] [Algebra ℚ S] (φ : R →ₐ[ℚ] S)
    (e : Matrix ι ι ℚ) (x : Matrix ι ι R) : φ.mapMatrix (blk e x) = blk e (φ.mapMatrix x) := by
  simp only [blk, map_add, map_mul, map_sub, map_one, map_rat]

theorem map_linExt {R S : Type} [CommRing R] [Algebra ℚ R] [CommRing S] [Algebra ℚ S] (φ : R →ₐ[ℚ] S)
    (c : ι × ι → ι × ι → ℚ) (x : Matrix ι ι R) : φ.mapMatrix (linExt c x) = linExt c (φ.mapMatrix x) := by
  ext i j
  show φ (∑ kl : ι × ι, algebraMap ℚ R (c (i, j) kl) * x kl.1 kl.2) =
    ∑ kl : ι × ι, algebraMap ℚ S (c (i, j) kl) * φ (x kl.1 kl.2)
  simp only [map_sum, map_mul, AlgHom.commutes]

theorem map_poly {R S : Type} [CommRing R] [Algebra ℚ R] [CommRing S] [Algebra ℚ S] (φ : R →ₐ[ℚ] S)
    (b : ι → ι → MvPolynomial (ι × ι) ℚ) (x : Matrix ι ι R) :
    φ.mapMatrix (Matrix.of fun i j => ev (b i j) x) = Matrix.of fun i j => ev (b i j) (φ.mapMatrix x) := by
  ext i j
  exact map_ev φ _ _

theorem transfer_mem {F : ∀ (R : Type) [CommRing R] [Algebra ℚ R], Matrix ι ι R → Matrix ι ι R}
    (hF : IsNatural F) {Γ Γ' : Set (Matrix ι ι ℂ)} (h : ∀ g ∈ Γ, F ℂ g ∈ Γ')
    {R : Type} [CommRing R] [Algebra ℚ R] {y : Matrix ι ι R} (hy : y ∈ pts Γ R) : F R y ∈ pts Γ' R := by
  intro f hf
  have key : ∀ (S : Type) [CommRing S] [Algebra ℚ S] (z : Matrix ι ι S),
      ev (ev f (F _ (Matrix.mvPolynomialX ι ι ℚ))) z = ev f (F S z) := by
    intro S _ _ z
    have := map_ev (evHom z) f (F _ (Matrix.mvPolynomialX ι ι ℚ))
    rw [hF, evHom_generic] at this
    exact this
  rw [← key]
  apply hy
  intro g hg
  rw [key]
  exact hf _ (h g hg)

theorem transfer_eq {F G : ∀ (R : Type) [CommRing R] [Algebra ℚ R], Matrix ι ι R → Matrix ι ι R}
    (hF : IsNatural F) (hG : IsNatural G) {Γ : Set (Matrix ι ι ℂ)} (h : ∀ g ∈ Γ, F ℂ g = G ℂ g)
    {R : Type} [CommRing R] [Algebra ℚ R] {y : Matrix ι ι R} (hy : y ∈ pts Γ R) : F R y = G R y := by
  ext i j
  have key : ∀ (S : Type) [CommRing S] [Algebra ℚ S] (z : Matrix ι ι S),
      ev (F _ (Matrix.mvPolynomialX ι ι ℚ) i j - G _ (Matrix.mvPolynomialX ι ι ℚ) i j) z
        = F S z i j - G S z i j := by
    intro S _ _ z
    have h1 := hF _ _ (evHom z) (Matrix.mvPolynomialX ι ι ℚ)
    have h2 := hG _ _ (evHom z) (Matrix.mvPolynomialX ι ι ℚ)
    rw [evHom_generic] at h1 h2
    rw [← h1, ← h2]
    exact map_sub (evHom z) _ _
  rw [← sub_eq_zero, ← key]
  apply hy
  intro g hg
  rw [key, h g hg, sub_self]

theorem mem_pts_univ {R : Type} [CommRing R] [Algebra ℚ R] (y : Matrix ι ι R) :
    y ∈ pts (Set.univ : Set (Matrix ι ι ℂ)) R := by
  intro f hf
  have h0 : MvPolynomial.map (algebraMap ℚ ℂ) f = 0 := by
    apply MvPolynomial.funext
    intro x
    have := hf (Matrix.of fun i j => x (i, j)) (Set.mem_univ _)
    rw [map_zero, MvPolynomial.eval_map, ← MvPolynomial.aeval_def]
    exact this
  have : f = 0 := MvPolynomial.map_injective _ (algebraMap ℚ ℂ).injective (by rw [h0, map_zero])
  subst this
  simp [ev]

theorem exists_section : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (e : Matrix ι ι ℚ), IsQGroup Γ → e * e = e → (∀ g ∈ Γ, (1 - e.map (algebraMap ℚ ℂ)) * g * e.map (algebraMap ℚ ℂ) = 0) → ∃ (c : ι × ι → ι × ι → ℚ) (b : ι → ι → MvPolynomial (ι × ι) ℚ), ∀ (R : Type) [CommRing R] [Algebra ℚ R], (∀ X : Matrix ι ι R, 1 + linExt c X ∈ pts Γ R) ∧ (∀ X Y : Matrix ι ι R, linExt c X * linExt c Y = 0) ∧ (∀ y ∈ pts Γ R, blk e y = 1 → ∃ X : Matrix ι ι R, y = 1 + linExt c X) ∧ (∀ x ∈ pts Γ R, (1 - e.map (algebraMap ℚ R)) * x * e.map (algebraMap ℚ R) = 0 ∧ blk e x ∈ pts (blk e '' Γ) R) ∧ ∀ y ∈ pts (blk e '' Γ) R, (Matrix.of fun i j => ev (b i j) (y)) ∈ pts Γ R ∧ blk e (Matrix.of fun i j => ev (b i j) (y)) = y := by
  intro ι _ _ Γ e hΓ he htri
  obtain ⟨c, b, hc, h1, hb⟩ := GlobalTheory.T.exists_polynomial_section_blockDiagonal_map ι Γ e hΓ he htri
  refine ⟨c, b, fun R _ _ => ⟨fun X => ?_, fun X Y => ?_, fun y hy hy1 => ?_, fun x hx => ⟨?_, ?_⟩,
    fun y hy => ⟨?_, ?_⟩⟩⟩
  · have h := transfer_mem (F := fun R _ _ X => 1 + linExt c X)
      (fun R S _ _ _ _ φ x => by simp only [map_add, map_one, map_linExt])
      (fun g _ => (hc g).1) (mem_pts_univ X)
    exact h
  · have hp : ∀ X : Matrix ι ι R,
        e.map (algebraMap ℚ R) * linExt c X * (1 - e.map (algebraMap ℚ R)) = linExt c X := fun X => by
      have h := transfer_eq (F := fun R _ _ X => e.map (algebraMap ℚ R) * linExt c X * (1 - e.map (algebraMap ℚ R)))
        (G := fun R _ _ X => linExt c X)
        (fun R S _ _ _ _ φ x => by simp only [map_mul, map_sub, map_one, map_linExt, map_rat])
        (fun R S _ _ _ _ φ x => by simp only [map_linExt])
        (by intro g _; beta_reduce; exact (hc g).2) (mem_pts_univ X)
      exact h
    have hE : (1 - e.map (algebraMap ℚ R)) * e.map (algebraMap ℚ R) = 0 := by
      rw [sub_mul, one_mul, ← Matrix.map_mul, he, sub_self]
    rw [← hp X, ← hp Y]
    calc _ = e.map (algebraMap ℚ R) * linExt c X * ((1 - e.map (algebraMap ℚ R)) * e.map (algebraMap ℚ R)) *
          linExt c Y * (1 - e.map (algebraMap ℚ R)) := by simp only [mul_assoc]
      _ = 0 := by rw [hE]; simp
  · have hone : (Matrix.of fun i j => ev (b i j) (1 : Matrix ι ι R)) = 1 := by
      have hq : (Matrix.of fun i j => ev (b i j) (1 : Matrix ι ι ℚ)) = 1 := by
        have := map_poly (Algebra.ofId ℚ ℂ) b 1
        rw [map_one, h1] at this
        ext i j
        apply (algebraMap ℚ ℂ).injective
        have h2 := congrFun (congrFun this i) j
        rw [← map_one (Algebra.ofId ℚ ℂ).mapMatrix] at h2
        exact h2
      have := map_poly (Algebra.ofId ℚ R) b 1
      rw [hq, map_one] at this
      exact this.symm
    have h := transfer_eq (F := fun R _ _ g => g)
      (G := fun R _ _ g => (1 + linExt c (e.map (algebraMap ℚ R) * g * (1 - e.map (algebraMap ℚ R)) *
        (blk e g).adjugate)) * (Matrix.of fun i j => ev (b i j) (blk e g)))
      (fun R S _ _ _ _ φ x => rfl)
      (fun R S _ _ _ _ φ x => by
        simp only [map_mul, map_add, map_sub, map_one, map_linExt, map_rat, map_poly, map_blk,
          AlgHom.map_adjugate])
      (Γ := Γ) (by intro g hg; beta_reduce; exact (hb g hg).2.2) hy
    simp only [hy1, hone, mul_one] at h
    exact ⟨_, h⟩
  · have h := transfer_eq (F := fun R _ _ x => (1 - e.map (algebraMap ℚ R)) * x * e.map (algebraMap ℚ R))
      (G := fun R _ _ _ => 0)
      (fun R S _ _ _ _ φ x => by simp only [map_mul, map_sub, map_one, map_rat])
      (fun R S _ _ _ _ φ x => by simp only [map_zero])
      (by intro g hg; beta_reduce; exact htri g hg) hx
    exact h
  · have h := transfer_mem (F := fun R _ _ x => blk e x) (fun R S _ _ _ _ φ x => map_blk φ e x)
      (Γ' := blk e '' Γ) (fun g hg => ⟨g, hg, rfl⟩) hx
    exact h
  · have h := transfer_mem (F := fun R _ _ x => Matrix.of fun i j => ev (b i j) x)
      (fun R S _ _ _ _ φ x => map_poly φ b x)
      (Γ' := Γ) (by rintro _ ⟨g, hg, rfl⟩; beta_reduce; exact (hb g hg).1) hy
    exact h
  · have h := transfer_eq (F := fun R _ _ x => blk e (Matrix.of fun i j => ev (b i j) x))
      (G := fun R _ _ x => x)
      (fun R S _ _ _ _ φ x => by simp only [map_blk, map_poly])
      (fun R S _ _ _ _ φ x => rfl)
      (by rintro _ ⟨g, hg, rfl⟩; beta_reduce; exact (hb g hg).2.1) hy
    exact h

end GlobalTheory.ClassFin.PolySection
end
