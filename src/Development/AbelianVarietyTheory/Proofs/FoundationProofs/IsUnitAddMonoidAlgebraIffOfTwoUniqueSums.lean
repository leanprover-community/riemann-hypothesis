import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.Torus2GammaBijective
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLeftCoactionIffIsCoactionComm

section
open Finsupp

namespace GlobalTheory

variable {X : Type*}

def tupleCoface (a b : X) {n : ℕ} (i : Fin (n + 2)) (x : Fin n → X) : Fin (n + 1) → X :=
  fun j => (Fin.cons a (Fin.snoc x b) : Fin (n + 2) → X)
    (if i ≤ j.castSucc then j.castSucc else j.succ)

@[simp] theorem tupleCoface_zero (a b : X) {n : ℕ} (x : Fin n → X) :
    tupleCoface a b 0 x = Fin.cons a x := by
  funext j
  simp only [tupleCoface, Fin.zero_le, if_true]
  induction j using Fin.cases with
  | zero => simp
  | succ j => simp [← Fin.succ_castSucc]

@[simp] theorem tupleCoface_last (a b : X) {n : ℕ} (x : Fin n → X) :
    tupleCoface a b (Fin.last (n + 1)) x = Fin.snoc x b := by
  funext j
  simp [tupleCoface, (Fin.castSucc_lt_last j).not_ge]

variable (R : Type*) [Ring R] (N : Type*) [AddCommGroup N] [Module R N]

noncomputable def tupleDifferential (a b : X) (n : ℕ) :
    ((Fin n → X) →₀ N) →ₗ[R] ((Fin (n + 1) → X) →₀ N) :=
  ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • lmapDomain N R (tupleCoface a b i)

noncomputable def tupleContraction (a : X) (n : ℕ) :
    ((Fin (n + 1) → X) →₀ N) →ₗ[R] ((Fin n → X) →₀ N) :=
  lcomapDomain (fun x => Fin.cons a x) (Fin.cons_right_injective (α := fun _ => X) a)

variable {R N}

@[simp] theorem tupleContraction_apply (a : X) (n : ℕ) (f : (Fin (n + 1) → X) →₀ N)
    (x : Fin n → X) : tupleContraction R N a n f x = f (Fin.cons a x) := rfl

end GlobalTheory
end

section
open TensorProduct Coalgebra AddMonoidAlgebra DirectSum

namespace GlobalTheory

variable {R : Type*} [CommSemiring R] {X : Type*}
variable {M : Type*} [AddCommMonoid M] [Module R M] {M' : Type*} [AddCommMonoid M'] [Module R M']

variable (R M) in

noncomputable def tensorCoeff (x : X) : M ⊗[R] R[X] →ₗ[R] M :=
  (TensorProduct.rid R M).toLinearMap ∘ₗ
    (Finsupp.lapply x ∘ₗ (coeffLinearEquiv R : R[X] ≃ₗ[R] X →₀ R).toLinearMap).lTensor M

@[simp] theorem tensorCoeff_tmul (x : X) (m : M) (p : R[X]) :
    tensorCoeff R M x (m ⊗ₜ p) = p.coeff x • m := by
  simp [tensorCoeff]

theorem tensorCoeff_tmul_single_one [DecidableEq X] (x y : X) (m : M) :
    tensorCoeff R M x (m ⊗ₜ single y 1) = if y = x then m else 0 := by
  simp [Finsupp.single_apply]

theorem exists_eq_sum_tensorCoeff (t : M ⊗[R] R[X]) :
    ∃ s : Finset X, (∀ x ∉ s, tensorCoeff R M x t = 0) ∧
      t = ∑ x ∈ s, tensorCoeff R M x t ⊗ₜ[R] single x (1 : R) := by
  classical
  let E : M ⊗[R] R[X] ≃ₗ[R] X →₀ M :=
    (coeffLinearEquiv R : R[X] ≃ₗ[R] X →₀ R).lTensor M ≪≫ₗ finsuppScalarRight R R M X
  have hE : ∀ t x, E t x = tensorCoeff R M x t := by
    intro t x
    induction t with
    | zero => simp
    | add a b ha hb => simp [ha, hb]
    | tmul m p => simp [E, finsuppScalarRight_apply_tmul_apply]
  refine ⟨(E t).support, fun x hx => by rw [← hE]; simpa using hx, E.injective ?_⟩
  ext y
  rw [map_sum, Finsupp.finsetSum_apply]
  simp only [hE, tensorCoeff_tmul_single_one]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [← hE]; simpa using h

theorem tensorCoeff_ext {t t' : M ⊗[R] R[X]}
    (h : ∀ x, tensorCoeff R M x t = tensorCoeff R M x t') : t = t' := by
  classical
  obtain ⟨s, hs, e⟩ := exists_eq_sum_tensorCoeff t
  obtain ⟨s', hs', e'⟩ := exists_eq_sum_tensorCoeff t'
  refine e.trans (Eq.trans ?_ e'.symm)
  rw [Finset.sum_subset (Finset.subset_union_left (s₁ := s) (s₂ := s'))
      (fun x _ hx => by simp [hs x hx]),
    Finset.sum_subset (Finset.subset_union_right (s₁ := s) (s₂ := s'))
      (fun x _ hx => by simp [hs' x hx])]
  simp only [h]

noncomputable abbrev torusWeightSpace (ρ : M →ₗ[R] M ⊗[R] R[X]) (x : X) : Submodule R M :=
  coactionWeightSpace ρ (single x 1)

theorem IsCoaction.tensorCoeff_mem {ρ : M →ₗ[R] M ⊗[R] R[X]} (h : IsCoaction ρ) (x : X) (m : M) :
    tensorCoeff R M x (ρ m) ∈ torusWeightSpace ρ x := by
  classical
  have h1 : ∀ t : M ⊗[R] R[X], tensorCoeff R (M ⊗[R] R[X]) x (ρ.rTensor _ t) =
      ρ (tensorCoeff R M x t) := by
    intro t
    induction t with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul m p => simp
  have h2 : ∀ t : M ⊗[R] R[X], tensorCoeff R (M ⊗[R] R[X]) x
      ((TensorProduct.assoc R M R[X] R[X]).symm ((comul (R := R)).lTensor M t)) =
      tensorCoeff R M x t ⊗ₜ single x 1 := by
    intro t
    induction t with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb, add_tmul]
    | tmul m p =>
      induction p using AddMonoidAlgebra.induction_linear with
      | zero => simp
      | add a b ha hb => simp only [tmul_add, map_add, ha, hb, add_tmul]
      | single y r =>
        by_cases hy : y = x
        · subst hy; simp [smul_tmul']
        · simp [hy]
  rw [mem_coactionWeightSpace, ← h1, ← h2, ← h.coassoc, LinearEquiv.symm_apply_apply]

theorem IsCoaction.exists_eq_sum {ρ : M →ₗ[R] M ⊗[R] R[X]} (h : IsCoaction ρ) (m : M) :
    ∃ s : Finset X, m = ∑ x ∈ s, tensorCoeff R M x (ρ m) := by
  obtain ⟨s, -, e⟩ := exists_eq_sum_tensorCoeff (ρ m)
  refine ⟨s, ?_⟩
  conv_lhs => rw [← h.rid_counit m, e]
  simp

variable [DecidableEq X]

theorem tensorCoeff_of_mem_torusWeightSpace {ρ : M →ₗ[R] M ⊗[R] R[X]} {y : X} {m : M}
    (hm : m ∈ torusWeightSpace ρ y) (x : X) :
    tensorCoeff R M x (ρ m) = if y = x then m else 0 := by
  rw [mem_coactionWeightSpace.1 hm, tensorCoeff_tmul_single_one]

theorem IsCoaction.isInternal_torusWeightSpace {ρ : M →ₗ[R] M ⊗[R] R[X]} (h : IsCoaction ρ) :
    IsInternal (torusWeightSpace ρ) := by
  have key : ∀ (z : ⨁ x, torusWeightSpace ρ x) (x : X),
      tensorCoeff R M x (ρ (DirectSum.coeAddMonoidHom _ z)) = z x := by
    intro z x
    induction z using DirectSum.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb, DirectSum.add_apply, Submodule.coe_add]
    | of y m =>
      rw [coeAddMonoidHom_of, tensorCoeff_of_mem_torusWeightSpace m.2]
      split_ifs with hy
      · subst hy; simp
      · rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm hy)]; rfl
  refine ⟨fun z z' e => ?_, fun m => ?_⟩
  · ext x
    rw [← key, e, key]
  · obtain ⟨s, e⟩ := h.exists_eq_sum m
    refine ⟨∑ x ∈ s, DirectSum.of (fun x => torusWeightSpace ρ x) x ⟨_, h.tensorCoeff_mem x m⟩, ?_⟩
    rw [map_sum]
    simp only [coeAddMonoidHom_of]
    exact e.symm

@[instance_reducible]
noncomputable def IsCoaction.decomposition {ρ : M →ₗ[R] M ⊗[R] R[X]} (h : IsCoaction ρ) :
    Decomposition (torusWeightSpace ρ) :=
  h.isInternal_torusWeightSpace.chooseDecomposition

theorem coe_decompose_torusWeightSpace (ρ : M →ₗ[R] M ⊗[R] R[X])
    [Decomposition (torusWeightSpace ρ)] (m : M) (x : X) :
    (decompose (torusWeightSpace ρ) m x : M) = tensorCoeff R M x (ρ m) := by
  induction m using Decomposition.inductionOn (torusWeightSpace ρ) with
  | zero => simp
  | add a b ha hb =>
    simp only [decompose_add, map_add, ← ha, ← hb, DirectSum.add_apply, Submodule.coe_add]
  | @homogeneous y m =>
    rw [tensorCoeff_of_mem_torusWeightSpace m.2]
    split_ifs with hy
    · subst hy; exact decompose_of_mem_same _ m.2
    · exact decompose_of_mem_ne _ m.2 hy

noncomputable def gradingCoaction (ℳ : X → Submodule R M) [Decomposition ℳ] :
    M →ₗ[R] M ⊗[R] R[X] :=
  DirectSum.toModule R X _
      (fun x => (TensorProduct.mk R M R[X]).flip (single x 1) ∘ₗ (ℳ x).subtype) ∘ₗ
    (decomposeLinearEquiv ℳ).toLinearMap

theorem gradingCoaction_of_mem (ℳ : X → Submodule R M) [Decomposition ℳ] {x : X} {m : M}
    (hm : m ∈ ℳ x) : gradingCoaction ℳ m = m ⊗ₜ single x 1 := by
  lift m to ℳ x using hm
  simp [gradingCoaction]

theorem tensorCoeff_gradingCoaction (ℳ : X → Submodule R M) [Decomposition ℳ] (m : M) (x : X) :
    tensorCoeff R M x (gradingCoaction ℳ m) = decompose ℳ m x := by
  induction m using Decomposition.inductionOn ℳ with
  | zero => simp
  | add a b ha hb =>
    simp only [decompose_add, map_add, ha, hb, DirectSum.add_apply, Submodule.coe_add]
  | @homogeneous y m =>
    rw [gradingCoaction_of_mem ℳ m.2, tensorCoeff_tmul_single_one]
    split_ifs with hy
    · subst hy; exact (decompose_of_mem_same _ m.2).symm
    · exact (decompose_of_mem_ne _ m.2 hy).symm

theorem isCoaction_gradingCoaction (ℳ : X → Submodule R M) [Decomposition ℳ] :
    IsCoaction (gradingCoaction ℳ) where
  coassoc m := by
    induction m using Decomposition.inductionOn ℳ with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | homogeneous m => simp [gradingCoaction_of_mem ℳ m.2]
  counit m := by
    induction m using Decomposition.inductionOn ℳ with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb, add_tmul]
    | homogeneous m => simp [gradingCoaction_of_mem ℳ m.2]

@[simp] theorem torusWeightSpace_gradingCoaction (ℳ : X → Submodule R M) [Decomposition ℳ] :
    torusWeightSpace (gradingCoaction ℳ) = ℳ := by
  ext x m
  refine ⟨fun hm => ?_, fun hm => gradingCoaction_of_mem ℳ hm⟩
  have := tensorCoeff_of_mem_torusWeightSpace hm x
  rw [if_pos rfl, tensorCoeff_gradingCoaction] at this
  exact this ▸ (decompose ℳ m x).2

@[simp] theorem gradingCoaction_torusWeightSpace (ρ : M →ₗ[R] M ⊗[R] R[X])
    [Decomposition (torusWeightSpace ρ)] : gradingCoaction (torusWeightSpace ρ) = ρ := by
  refine LinearMap.ext fun m => tensorCoeff_ext fun x => ?_
  rw [tensorCoeff_gradingCoaction, coe_decompose_torusWeightSpace]

variable (R X M) in

noncomputable def coactionEquivGrading :
    {ρ : M →ₗ[R] M ⊗[R] R[X] // IsCoaction ρ} ≃ {ℳ : X → Submodule R M // IsInternal ℳ} where
  toFun ρ := ⟨torusWeightSpace ρ.1, ρ.2.isInternal_torusWeightSpace⟩
  invFun ℳ := letI := ℳ.2.chooseDecomposition; ⟨gradingCoaction ℳ.1, isCoaction_gradingCoaction _⟩
  left_inv ρ := Subtype.ext (by
    letI := ρ.2.decomposition
    exact gradingCoaction_torusWeightSpace ρ.1)
  right_inv ℳ := Subtype.ext (by
    letI := ℳ.2.chooseDecomposition
    exact torusWeightSpace_gradingCoaction ℳ.1)

omit [DecidableEq X] in

theorem IsCoaction.comm_iff_mapsTo_torusWeightSpace {ρ : M →ₗ[R] M ⊗[R] R[X]} (h : IsCoaction ρ)
    (ρ' : M' →ₗ[R] M' ⊗[R] R[X]) (f : M →ₗ[R] M') :
    (∀ m, ρ' (f m) = f.rTensor R[X] (ρ m)) ↔
      ∀ x, ∀ m ∈ torusWeightSpace ρ x, f m ∈ torusWeightSpace ρ' x := by
  classical
  refine ⟨fun hf x m hm => map_mem_coactionWeightSpace hf hm, fun hf m => ?_⟩
  letI := h.decomposition
  induction m using Decomposition.inductionOn (torusWeightSpace ρ) with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | homogeneous m =>
    rw [mem_coactionWeightSpace.1 (hf _ _ m.2), mem_coactionWeightSpace.1 m.2,
      LinearMap.rTensor_tmul]

theorem IsLeftCoaction.isInternal {ρ : M →ₗ[R] R[X] ⊗[R] M} (h : IsLeftCoaction ρ) :
    IsInternal fun x : X => LinearMap.eqLocus ρ (TensorProduct.mk R R[X] M (single x 1)) := by
  have := ((isLeftCoaction_iff_isCoaction_comm ρ).1 h).isInternal_torusWeightSpace
  convert this using 2 with x
  ext m
  rw [mem_coactionWeightSpace, ← (TensorProduct.comm R M R[X]).apply_eq_iff_eq]
  simp

section Algebra

variable [AddMonoid X] {A : Type*} [Semiring A] [Algebra R A]

omit [DecidableEq X] in

instance gradedMonoid_torusWeightSpace (ρ : A →ₐ[R] A ⊗[R] R[X]) :
    SetLike.GradedMonoid (torusWeightSpace ρ.toLinearMap) where
  one_mem := by
    rw [mem_coactionWeightSpace, AlgHom.toLinearMap_apply, map_one]; rfl
  mul_mem x y a b ha hb := by
    rw [mem_coactionWeightSpace, AlgHom.toLinearMap_apply] at ha hb ⊢
    rw [map_mul, ha, hb, Algebra.TensorProduct.tmul_mul_tmul, single_mul_single, _root_.mul_one]

@[instance_reducible]
noncomputable def IsCoaction.gradedAlgebra {ρ : A →ₐ[R] A ⊗[R] R[X]}
    (h : IsCoaction ρ.toLinearMap) : GradedAlgebra (torusWeightSpace ρ.toLinearMap) :=
  { gradedMonoid_torusWeightSpace ρ, h.decomposition with }

noncomputable def gradingCoactionAlgHom (𝒜 : X → Submodule R A) [GradedAlgebra 𝒜] :
    A →ₐ[R] A ⊗[R] R[X] :=
  AlgHom.ofLinearMap (gradingCoaction 𝒜)
    (gradingCoaction_of_mem 𝒜 (SetLike.one_mem_graded 𝒜))
    (fun a b => by
      induction a using Decomposition.inductionOn 𝒜 with
      | zero => simp
      | add a a' ha ha' => simp only [add_mul, map_add, ha, ha']
      | homogeneous a =>
        induction b using Decomposition.inductionOn 𝒜 with
        | zero => simp
        | add b b' hb hb' => simp only [mul_add, map_add, hb, hb']
        | homogeneous b =>
          rw [gradingCoaction_of_mem 𝒜 a.2, gradingCoaction_of_mem 𝒜 b.2,
            gradingCoaction_of_mem 𝒜 (SetLike.mul_mem_graded a.2 b.2),
            Algebra.TensorProduct.tmul_mul_tmul, single_mul_single, _root_.mul_one])

@[simp] theorem gradingCoactionAlgHom_toLinearMap (𝒜 : X → Submodule R A) [GradedAlgebra 𝒜] :
    (gradingCoactionAlgHom 𝒜).toLinearMap = gradingCoaction 𝒜 := rfl

variable (R X A) in

noncomputable def algCoactionEquivGrading :
    {ρ : A →ₐ[R] A ⊗[R] R[X] // IsCoaction ρ.toLinearMap} ≃
      {𝒜 : X → Submodule R A // Nonempty (GradedAlgebra 𝒜)} where
  toFun ρ := ⟨torusWeightSpace ρ.1.toLinearMap, ⟨ρ.2.gradedAlgebra⟩⟩
  invFun 𝒜 := letI := 𝒜.2.some; ⟨gradingCoactionAlgHom 𝒜.1, isCoaction_gradingCoaction _⟩
  left_inv ρ := Subtype.ext (AlgHom.toLinearMap_injective (by
    letI := (⟨ρ.2.gradedAlgebra⟩ : Nonempty _).some
    exact gradingCoaction_torusWeightSpace ρ.1.toLinearMap))
  right_inv 𝒜 := Subtype.ext (by
    letI := 𝒜.2.some
    exact torusWeightSpace_gradingCoaction 𝒜.1)

end Algebra

end GlobalTheory
end

section
open TensorProduct Coalgebra AddMonoidAlgebra

namespace GlobalTheory

section Units

variable {A : Type*} [CommRing A] {X : Type*} [AddCommGroup X]

noncomputable def monomialUnitHom (A : Type*) [CommRing A] (X : Type*) [AddCommGroup X] :
    Aˣ × Multiplicative X →* (A[X])ˣ :=
  MonoidHom.toHomUnits
    { toFun := fun p => single p.2.toAdd (p.1 : A)
      map_one' := rfl
      map_mul' := fun p q => by simp [single_mul_single] }

@[simp] theorem coe_monomialUnitHom (p : Aˣ × Multiplicative X) :
    (monomialUnitHom A X p : A[X]) = single p.2.toAdd (p.1 : A) := rfl

theorem monomialUnitHom_injective [Nontrivial A] : Function.Injective (monomialUnitHom A X) := by
  classical
  refine (injective_iff_map_eq_one _).2 fun p hp => ?_
  have h : (Finsupp.single p.2.toAdd (p.1 : A)) = Finsupp.single 0 1 :=
    congrArg (fun u : (A[X])ˣ => (u : A[X]).coeff) hp
  rcases (Finsupp.single_eq_single_iff _ _ _ _).1 h with ⟨h1, h2⟩ | ⟨-, h2⟩
  · exact Prod.ext (Units.ext h2) h1
  · exact absurd h2 one_ne_zero

variable [IsDomain A]

theorem isUnit_addMonoidAlgebra_iff_of_twoUniqueSums [TwoUniqueSums X] (f : A[X]) :
    IsUnit f ↔ ∃ (x : X) (a : Aˣ), f = single x (a : A) := by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨x, c, ⟨a, rfl⟩, e⟩ := ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht.isUnit_eq_single h
    exact ⟨x, a, e⟩
  · rintro ⟨x, a, rfl⟩
    exact (monomialUnitHom A X (a, .ofAdd x)).isUnit

variable [Module.Free ℤ X]

theorem isUnit_addMonoidAlgebra_iff (f : A[X]) :
    IsUnit f ↔ ∃ (x : X) (a : Aˣ), f = single x (a : A) :=
  isUnit_addMonoidAlgebra_iff_of_twoUniqueSums f

theorem monomialUnitHom_bijective : Function.Bijective (monomialUnitHom A X) := by
  refine ⟨monomialUnitHom_injective, fun u => ?_⟩
  obtain ⟨x, a, e⟩ := (isUnit_addMonoidAlgebra_iff (u : A[X])).1 u.isUnit
  exact ⟨(a, .ofAdd x), Units.ext e.symm⟩

variable (A X) in

noncomputable def unitsAddMonoidAlgebraEquiv : Aˣ × Multiplicative X ≃* (A[X])ˣ :=
  MulEquiv.ofBijective (monomialUnitHom A X) monomialUnitHom_bijective

@[simp] theorem coe_unitsAddMonoidAlgebraEquiv (p : Aˣ × Multiplicative X) :
    (unitsAddMonoidAlgebraEquiv A X p : A[X]) = single p.2.toAdd (p.1 : A) := rfl

end Units

section Coordinates

variable {X : Type*} [Zero X] {N : Type*} [AddCommGroup N]

theorem coboundary_apply_zero_left (g : X →₀ N) (x : X) :
    (g.mapDomain (fun y => ((0 : X), y)) - g.mapDomain (fun y => (y, y)) +
      g.mapDomain (fun y => (y, (0 : X))) : X × X →₀ N) (0, x) = g x := by
  classical
  induction g using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    simp only [Finsupp.mapDomain_add, Finsupp.add_apply, Finsupp.sub_apply] at hf hg ⊢
    rw [← hf, ← hg]; abel
  | single y m =>
    simp only [Finsupp.mapDomain_single, Finsupp.add_apply, Finsupp.sub_apply,
      Finsupp.single_apply, Prod.mk.injEq]
    by_cases h : y = 0
    · subst h; simp
    · simp [h]

theorem finsupp_two_cocycle_eq_coboundary (f : X × X →₀ N)
    (hf : f.mapDomain (fun p => ((0 : X), p.1, p.2)) - f.mapDomain (fun p => (p.1, p.1, p.2)) +
      f.mapDomain (fun p => (p.1, p.2, p.2)) - f.mapDomain (fun p => (p.1, p.2, (0 : X))) = 0)
    (g : X →₀ N) (hg : ∀ x, g x = f (0, x)) :
    g.mapDomain (fun y => ((0 : X), y)) - g.mapDomain (fun y => (y, y)) +
      g.mapDomain (fun y => (y, (0 : X))) = f := by
  classical
  let s : (X × X →₀ N) →+ (X →₀ N) :=
    Finsupp.comapDomain.addMonoidHom (f := fun x => ((0 : X), x)) (Prod.mk_right_injective 0)
  have hs : ∀ f x, s f x = f (0, x) := fun _ _ => rfl
  have key : ∀ (f : X × X →₀ N) (q : X × X),
      (f.mapDomain (fun p => ((0 : X), p.1, p.2)) - f.mapDomain (fun p => (p.1, p.1, p.2)) +
        f.mapDomain (fun p => (p.1, p.2, p.2)) - f.mapDomain (fun p => (p.1, p.2, (0 : X))) :
          X × X × X →₀ N) (0, q) +
      ((s f).mapDomain (fun y => ((0 : X), y)) - (s f).mapDomain (fun y => (y, y)) +
        (s f).mapDomain (fun y => (y, (0 : X))) : X × X →₀ N) q = f q := by
    intro f q
    induction f using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg =>
      simp only [map_add, Finsupp.mapDomain_add, Finsupp.add_apply, Finsupp.sub_apply] at hf hg ⊢
      rw [← hf, ← hg]; abel
    | single p m =>
      obtain ⟨y, z⟩ := p
      by_cases h : y = 0
      · subst h
        have : s (Finsupp.single (0, z) m) = Finsupp.single z m := by
          ext x; simp [hs, Finsupp.single_apply]
        simp [this, Finsupp.single_apply]
      · have : s (Finsupp.single (y, z) m) = 0 := by
          ext x; simp [hs, h]
        simp [this, Finsupp.single_apply, h]
  have e : g = s f := Finsupp.ext hg
  ext q
  rw [← key f q, hf, e]
  simp

end Coordinates

section Ring

variable {X : Type*} [Zero X] {A : Type*} [Ring A]

theorem addMonoidAlgebra_coboundary_eq_iff (f : A[X × X])
    (hf : mapDomain (fun p => ((0 : X), p.1, p.2)) f - mapDomain (fun p => (p.1, p.1, p.2)) f +
      mapDomain (fun p => (p.1, p.2, p.2)) f - mapDomain (fun p => (p.1, p.2, (0 : X))) f = 0)
    (g : A[X]) :
    mapDomain (fun y => ((0 : X), y)) g - mapDomain (fun y => (y, y)) g +
      mapDomain (fun y => (y, (0 : X))) g = f ↔ ∀ x, g.coeff x = f.coeff (0, x) := by
  refine ⟨fun h x => ?_, fun h => coeff_injective
    (finsupp_two_cocycle_eq_coboundary f.coeff (congrArg coeff hf) g.coeff h)⟩
  rw [← h]
  exact (coboundary_apply_zero_left g.coeff x).symm

theorem addMonoidAlgebra_existsUnique_coboundary (f : A[X × X])
    (hf : mapDomain (fun p => ((0 : X), p.1, p.2)) f - mapDomain (fun p => (p.1, p.1, p.2)) f +
      mapDomain (fun p => (p.1, p.2, p.2)) f - mapDomain (fun p => (p.1, p.2, (0 : X))) f = 0) :
    ∃! g : A[X], mapDomain (fun y => ((0 : X), y)) g - mapDomain (fun y => (y, y)) g +
      mapDomain (fun y => (y, (0 : X))) g = f := by
  simp only [addMonoidAlgebra_coboundary_eq_iff f hf]
  exact ⟨ofCoeff (f.coeff.comapDomain (fun x => ((0 : X), x)) (Prod.mk_right_injective 0).injOn),
    fun _ => rfl, fun g hg => coeff_injective (Finsupp.ext hg)⟩

end Ring

section Tensor

variable {R : Type*} [CommRing R] {H : Type*} [Ring H] [Bialgebra R H]
variable {M : Type*} [AddCommGroup M] [Module R M]

noncomputable def hochschildD₀ (ρ : M →ₗ[R] M ⊗[R] H) : M →ₗ[R] M ⊗[R] H :=
  ρ - (TensorProduct.mk R M H).flip 1

noncomputable def hochschildD₁ (ρ : M →ₗ[R] M ⊗[R] H) : M ⊗[R] H →ₗ[R] M ⊗[R] (H ⊗[R] H) :=
  (TensorProduct.assoc R M H H).toLinearMap ∘ₗ ρ.rTensor H - (comul (R := R)).lTensor M +
    ((TensorProduct.mk R H H).flip 1).lTensor M

noncomputable def hochschildD₂ (ρ : M →ₗ[R] M ⊗[R] H) :
    M ⊗[R] (H ⊗[R] H) →ₗ[R] M ⊗[R] (H ⊗[R] (H ⊗[R] H)) :=
  (TensorProduct.assoc R M H (H ⊗[R] H)).toLinearMap ∘ₗ ρ.rTensor (H ⊗[R] H) -
    ((TensorProduct.assoc R H H H).toLinearMap ∘ₗ (comul (R := R)).rTensor H).lTensor M +
    ((comul (R := R)).lTensor H).lTensor M -
    (((TensorProduct.mk R H H).flip 1).lTensor H).lTensor M

variable (R H M) in

noncomputable def trivialCoaction : M →ₗ[R] M ⊗[R] H := (TensorProduct.mk R M H).flip 1

@[simp] theorem trivialCoaction_apply (m : M) : trivialCoaction R H M m = m ⊗ₜ 1 := rfl

@[simp] theorem hochschildD₀_trivialCoaction : hochschildD₀ (trivialCoaction R H M) = 0 :=
  sub_self _

theorem hochschildD₁_trivialCoaction : hochschildD₁ (trivialCoaction R H M) =
    (TensorProduct.mk R H H 1).lTensor M - (comul (R := R)).lTensor M +
      ((TensorProduct.mk R H H).flip 1).lTensor M := by
  ext m h; simp [hochschildD₁]

theorem hochschildD₂_trivialCoaction : hochschildD₂ (trivialCoaction R H M) =
    (TensorProduct.mk R H (H ⊗[R] H) 1).lTensor M -
      ((TensorProduct.assoc R H H H).toLinearMap ∘ₗ (comul (R := R)).rTensor H).lTensor M +
      ((comul (R := R)).lTensor H).lTensor M -
      (((TensorProduct.mk R H H).flip 1).lTensor H).lTensor M := by
  ext m h k; simp [hochschildD₂]

variable {X : Type*} [AddMonoid X]

theorem hochschild_homotopy_one (ρ : M →ₗ[R] M ⊗[R] R[X]) (f : M ⊗[R] R[X]) :
    (tensorCoeff R R[X] (0 : X)).lTensor M (hochschildD₁ ρ f) -
      hochschildD₀ ρ (tensorCoeff R M 0 f) = f := by
  classical
  induction f with
  | zero => simp
  | add a b ha hb => simp only [map_add]; rw [add_sub_add_comm, ha, hb]
  | tmul m p =>
    have h : ∀ (t : M ⊗[R] R[X]) (p : R[X]), (tensorCoeff R R[X] (0 : X)).lTensor M
        (TensorProduct.assoc R M R[X] R[X] (t ⊗ₜ p)) = p.coeff 0 • t := by
      intro t p
      induction t with
      | zero => simp
      | add a b ha hb => simp only [add_tmul, map_add, ha, hb, smul_add]
      | tmul m q => simp
    induction p using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [tmul_add, map_add]; rw [add_sub_add_comm, ha, hb]
    | single y r =>
      simp only [hochschildD₁, hochschildD₀, LinearMap.add_apply, LinearMap.sub_apply,
        LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.rTensor_tmul, map_add, map_sub, h]
      by_cases hy : y = 0
      · subst hy; simp [one_def, ← tmul_smul]
      · simp [one_def, hy]

theorem hochschild_homotopy_two (ρ : M →ₗ[R] M ⊗[R] R[X]) (f : M ⊗[R] (R[X] ⊗[R] R[X])) :
    hochschildD₁ ρ ((tensorCoeff R R[X] (0 : X)).lTensor M f) -
      ((tensorCoeff R R[X] (0 : X)).lTensor R[X]).lTensor M (hochschildD₂ ρ f) = f := by
  classical
  induction f with
  | zero => simp
  | add a b ha hb => simp only [map_add]; rw [add_sub_add_comm, ha, hb]
  | tmul m u =>
    have h : ∀ (t : M ⊗[R] R[X]) (u : R[X] ⊗[R] R[X]),
        ((tensorCoeff R R[X] (0 : X)).lTensor R[X]).lTensor M
        (TensorProduct.assoc R M R[X] (R[X] ⊗[R] R[X]) (t ⊗ₜ u)) =
        TensorProduct.assoc R M R[X] R[X] (t ⊗ₜ tensorCoeff R R[X] (0 : X) u) := by
      intro t u
      induction t with
      | zero => simp
      | add a b ha hb => simp only [add_tmul, map_add, ha, hb]
      | tmul m q => simp
    induction u with
    | zero => simp
    | add a b ha hb => simp only [tmul_add, map_add]; rw [add_sub_add_comm, ha, hb]
    | tmul p q =>
      induction p using AddMonoidAlgebra.induction_linear with
      | zero => simp
      | add a b ha hb => simp only [add_tmul, tmul_add, map_add]; rw [add_sub_add_comm, ha, hb]
      | single x c =>
        induction q using AddMonoidAlgebra.induction_linear with
        | zero => simp
        | add a b ha hb => simp only [tmul_add, map_add]; rw [add_sub_add_comm, ha, hb]
        | single y r =>
          simp only [hochschildD₁, hochschildD₂, LinearMap.add_apply, LinearMap.sub_apply,
            LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.rTensor_tmul,
            LinearMap.lTensor_tmul, map_add, map_sub, h]
          by_cases hy : y = 0
          · subst hy
            have e : (single x (r * c) : R[X]) ⊗ₜ[R] (single 0 1 : R[X]) =
                single x c ⊗ₜ[R] single 0 r := by
              rw [← smul_eq_mul, ← smul_single, smul_tmul, smul_single, smul_eq_mul, _root_.mul_one]
            simp [one_def, e]
          · simp [one_def, hy]

theorem IsCoaction.exact_hochschildD₀_hochschildD₁ {ρ : M →ₗ[R] M ⊗[R] R[X]} (h : IsCoaction ρ) :
    Function.Exact (hochschildD₀ ρ) (hochschildD₁ ρ) := by
  classical
  intro f
  refine ⟨fun hf => ⟨-tensorCoeff R M 0 f, ?_⟩, ?_⟩
  · simpa [hf] using hochschild_homotopy_one ρ f
  · rintro ⟨m, rfl⟩
    let := h.decomposition
    induction m using DirectSum.Decomposition.inductionOn (torusWeightSpace ρ) with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb, add_zero]
    | homogeneous m =>
      simp [hochschildD₀, hochschildD₁, mem_coactionWeightSpace.1 m.2, one_def]

theorem IsCoaction.exact_hochschildD₁_hochschildD₂ {ρ : M →ₗ[R] M ⊗[R] R[X]} (h : IsCoaction ρ) :
    Function.Exact (hochschildD₁ ρ) (hochschildD₂ ρ) := by
  classical
  intro f
  refine ⟨fun hf => ⟨(tensorCoeff R R[X] (0 : X)).lTensor M f, ?_⟩, ?_⟩
  · simpa [hf] using hochschild_homotopy_two ρ f
  · rintro ⟨g, rfl⟩
    let := h.decomposition
    induction g with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb, add_zero]
    | tmul m p =>
      induction m using DirectSum.Decomposition.inductionOn (torusWeightSpace ρ) with
      | zero => simp
      | add a b ha hb => simp only [add_tmul, map_add, ha, hb, add_zero]
      | homogeneous m =>
        induction p using AddMonoidAlgebra.induction_linear with
        | zero => simp
        | add a b ha hb => simp only [tmul_add, map_add, ha, hb, add_zero]
        | single y r =>
          rw [← _root_.mul_one r, ← smul_eq_mul, ← smul_single, tmul_smul, map_smul, map_smul]
          refine smul_eq_zero_of_right _ ?_
          simp [hochschildD₂, hochschildD₁, mem_coactionWeightSpace.1 m.2, one_def]
          abel

variable (R M X) in

theorem hochschildD₁_trivialCoaction_injective :
    Function.Injective (hochschildD₁ (trivialCoaction R R[X] M)) := by
  refine (injective_iff_map_eq_zero _).2 fun f hf => ?_
  simpa [hf] using (hochschild_homotopy_one (trivialCoaction R R[X] M) f).symm

end Tensor

universe u v w

end GlobalTheory
end
