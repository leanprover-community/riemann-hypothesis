import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsEquivalenceFiniteEtaleBaseChangeResidueField
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CyclicVectorOfSeparableCharpolyField
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CyclicVectorSemilocalOfCyclicVectorField
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CyclicVectorGeneratedAlgebraStructure
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RegularSemisimpleTensorCommutant
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EtaleTensorQuadraticSplitAlgClosed
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitFactorIdempotentsExist
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitSubtorusOfIdempotentFamily
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitSubtorusLaurentPolynomialPoints
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateFactorPointsSeparate
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CentralizerSplitRankUpperBound
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryGroupCommutantScalars
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ReducedFreeAlgebraTraceFormPerfect
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianTraceFormOfTraceFormPerfect
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormOneSmallMultiplesByCocompactSubgroup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteAlgebraAdelicLatticeProof
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FieldAdelicUnitTranslateBoundedOfSmallMultiples
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormOneBoundedOfUnitBoundedOfAdelicLattice
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicUnitTranslateBoundedOfFactors
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CentraliserPointsBoundedOfNormOneBounded
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicQuotientCompactOfBoundedMatrices
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetRestrictRangeIdempotentMatrix
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicQuotientNotCompactOfSplitIdempotent

section
open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cyclicVector_of_separable_charpoly_field : GlobalTheory.RegSS.CyclicField := by
  first | exact @GlobalTheory.RegSS.cyclicField | exact GlobalTheory.RegSS.cyclicField | (intros; apply GlobalTheory.RegSS.cyclicField <;> assumption)
end

section
open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cyclicVector_semilocal_of_cyclicVector_field : GlobalTheory.RegSS.CyclicField → GlobalTheory.RegSS.CyclicSemilocal := by
  first | exact @GlobalTheory.RegSS.Semilocal.cyclicSemilocal_of_cyclicField | exact GlobalTheory.RegSS.Semilocal.cyclicSemilocal_of_cyclicField | (intros; apply GlobalTheory.RegSS.Semilocal.cyclicSemilocal_of_cyclicField <;> assumption)
end

section
open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cyclicVector_generatedAlgebra_structure : GlobalTheory.RegSS.CyclicAlgebra := by
  first | exact @GlobalTheory.RegSS.CycAlg.cyclicAlgebra | exact GlobalTheory.RegSS.CycAlg.cyclicAlgebra | (intros; apply GlobalTheory.RegSS.CycAlg.cyclicAlgebra <;> assumption)
end

section
section
open GlobalTheory.RegSS GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct

namespace GlobalTheory.RegSS

theorem productMap_bijective_of_involution {F E L : Type} [Field F] [CharZero F] [CommRing E]
    [Algebra F E] [CommRing L] [Algebra F L] (f : E →ₐ[F] L) (τ : L ≃ₐ[F] L)
    (hτ : ∀ l, τ (τ l) = l) (P : Subalgebra F L) (hP : ∀ l, l ∈ P ↔ τ l = l)
    (b : Module.Basis (Fin 2) F E) (d : F) (h0 : b 0 = 1) (h1 : τ (f (b 1)) = - f (b 1))
    (hd : d ≠ 0) (hsq : b 1 * b 1 = algebraMap F E d) :
    Function.Bijective (Algebra.TensorProduct.productMap P.val f) := by
  have hδ : f (b 1) * f (b 1) = algebraMap F L d := by rw [← map_mul, hsq, AlgHom.commutes]
  have hinv : algebraMap F L d⁻¹ * (f (b 1) * f (b 1)) = 1 := by
    rw [hδ, ← map_mul, inv_mul_cancel₀ hd, map_one]
  have h2 : algebraMap F L 2⁻¹ * 2 = 1 := by
    rw [← map_ofNat (algebraMap F L) 2, ← map_mul, inv_mul_cancel₀ two_ne_zero, map_one]
  have hval : ∀ a c : P, Algebra.TensorProduct.productMap P.val f (a ⊗ₜ[F] 1 + c ⊗ₜ[F] b 1) =
      (a : L) + (c : L) * f (b 1) := fun a c => by
    simp [Algebra.TensorProduct.productMap_apply_tmul]
  constructor
  · have hrep : ∀ x : P ⊗[F] E, ∃ a c : P, x = a ⊗ₜ[F] 1 + c ⊗ₜ[F] b 1 := by
      intro x
      induction x with
      | zero => exact ⟨0, 0, by simp⟩
      | tmul p e =>
        refine ⟨b.repr e 0 • p, b.repr e 1 • p, ?_⟩
        conv_lhs => rw [← b.sum_repr e, Fin.sum_univ_two, h0]
        rw [TensorProduct.tmul_add, TensorProduct.smul_tmul, TensorProduct.smul_tmul]
      | add x y hx hy =>
        obtain ⟨a, c, rfl⟩ := hx
        obtain ⟨a', c', rfl⟩ := hy
        exact ⟨a + a', c + c', by rw [TensorProduct.add_tmul, TensorProduct.add_tmul]; abel⟩
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨a, c, rfl⟩ := hrep x
    rw [hval] at hx
    have hx' := congrArg τ hx
    rw [map_add, map_mul, map_zero, (hP _).1 a.2, (hP _).1 c.2, h1] at hx'
    have ha : (a : L) = 0 := by
      linear_combination (algebraMap F L 2⁻¹) * (hx + hx') - (a : L) * h2
    have hc : (c : L) = 0 := by
      linear_combination (algebraMap F L d⁻¹ * f (b 1)) * (hx - ha) - (c : L) * hinv
    rw [show a = 0 from Subtype.ext ha, show c = 0 from Subtype.ext hc]
    simp
  · intro l
    refine ⟨(⟨algebraMap F L 2⁻¹ * (l + τ l), (hP _).2 ?_⟩ : P) ⊗ₜ[F] 1 +
      (⟨algebraMap F L 2⁻¹ * algebraMap F L d⁻¹ * f (b 1) * (l - τ l), (hP _).2 ?_⟩ : P) ⊗ₜ[F] b 1,
      ?_⟩
    · rw [map_mul, map_add, hτ, AlgEquiv.commutes, add_comm]
    · rw [map_mul, map_mul, map_mul, map_sub, hτ, AlgEquiv.commutes, AlgEquiv.commutes, h1]
      ring
    · rw [hval]
      dsimp only
      linear_combination l * h2 + algebraMap F L 2⁻¹ * (l - τ l) * hinv

theorem plusTensorBijective : PlusTensorBijective := by
  intro F E _ _ _ _ n _ _ σ J γ h hA
  obtain ⟨τ, -, hτ, hE, hP⟩ := exists_adjEquiv h hA
  obtain ⟨b, d, h0, h1, hd, hsq⟩ := quad_exists_basis h.quad
  refine productMap_bijective_of_involution _ τ hτ _ hP b d h0 ?_ hd hsq
  rw [IsScalarTower.toAlgHom_apply, hE, h1, map_neg]

end GlobalTheory.RegSS
end

open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regularSemisimple_selfAdjointPart_tensor_bijective : GlobalTheory.RegSS.PlusTensorBijective := by
  atlas_forward_decl GlobalTheory.RegSS.plusTensorBijective
end

section
section
open GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct

namespace GlobalTheory.RegSS

theorem plusEtale : PlusEtale := by
  intro F E _ _ _ _ n _ _ σ J γ hreg hA hbij
  have : Nontrivial E := quad_nontrivial hreg.quad
  have : Module.Finite F E := quad_finite hreg.quad
  obtain ⟨b⟩ := hA.2.2.1
  have : Module.Free E (genAlg (γ : Matrix n n E)) := Module.Free.of_basis b
  have : Module.Finite E (genAlg (γ : Matrix n n E)) := Module.Finite.of_basis b
  have : Module.Finite F (genAlg (γ : Matrix n n E)) := Module.Finite.trans E _
  have : Module.Finite F (plusAlg σ J (γ : Matrix n n E)) :=
    Module.Finite.of_injective (plusAlg σ J (γ : Matrix n n E)).val.toLinearMap
      Subtype.val_injective
  have : IsReduced (genAlg (γ : Matrix n n E)) := genAlg_isReduced hreg hA
  have : IsReduced (plusAlg σ J (γ : Matrix n n E)) :=
    isReduced_of_injective (plusAlg σ J (γ : Matrix n n E)).val Subtype.val_injective
  refine ⟨etale_of_isReduced _, ?_, hbij⟩
  have hdim := (AlgEquiv.ofBijective _ hbij).toLinearEquiv.finrank_eq
  rw [Module.finrank_tensorProduct, hreg.quad.finrank_eq,
    ← Module.finrank_mul_finrank F E (genAlg (γ : Matrix n n E)), hreg.quad.finrank_eq, Module.finrank_eq_card_basis b] at hdim
  have hr : Module.finrank F (plusAlg σ J (γ : Matrix n n E)) = Fintype.card n := by omega
  exact ⟨(Module.finBasisOfFinrankEq F _ hr).reindex (Fintype.equivFin n).symm⟩

end GlobalTheory.RegSS
end

open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regularSemisimple_selfAdjointPart_etale : GlobalTheory.RegSS.PlusEtale := by
  atlas_forward_decl GlobalTheory.RegSS.plusEtale
end

section
section
open Matrix Formalism.UG GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct

namespace GlobalTheory.RegSS

theorem pointsAdjoint_toMat_tmul {F E : Type} [Field F] [CommRing E] [Algebra F E] {n : Type}
    [Fintype n] [DecidableEq n] (σ : E →ₐ[F] E) (J γ : Matrix n n E) (R : Type) [CommRing R]
    [Algebra F R] (l : plusAlg σ J γ) (c : E ⊗[F] R) :
    toMat σ J γ R (l ⊗ₜ c) = c • ((l : genAlg γ) : Matrix n n E).map (inclE (F := F) R) := by
  rw [Algebra.smul_def, Algebra.commutes]
  exact Algebra.TensorProduct.lift_tmul _ _ _ l c

theorem pointsAdjoint : PointsAdjoint := by
  intro F E _ _ _ _ n _ _ σ J γ h R _ _ u
  induction u using TensorProduct.induction_on with
  | zero => simp [adj_zero]
  | tmul a b =>
    have ha := (adj_eq_iff _ h.nondeg _ _).2 a.2
    have hc : lConj σ J (γ : Matrix n n E) R (a ⊗ₜ b) = a ⊗ₜ sigR σ R b := rfl
    rw [hc, pointsAdjoint_toMat_tmul,
      pointsAdjoint_toMat_tmul, adj_smul,
      adj_map (σ : E →+* E) (sigR σ R) (inclE (F := F) R) (inclE_conj σ R) h.nondeg, ha]
  | add a b ha hb => rw [map_add, map_add, map_add, adj_add, ha, hb]

end GlobalTheory.RegSS
end

open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regularSemisimple_tensor_involution_adjoint : GlobalTheory.RegSS.PointsAdjoint := by
  atlas_forward_decl GlobalTheory.RegSS.pointsAdjoint
end

section
section
open Matrix Formalism.UG GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms GlobalTheory.RegSS
open scoped TensorProduct

namespace GlobalTheory.RegSS

private lemma cT_mul_mul_eq_iff_mul_adj_eq_one {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
    (s : A →+* A) {J g : Matrix n n A} (hJ : IsUnit J.det) :
    cT s g * J * g = J ↔ g * adj s J g = 1 := by
  rw [mul_eq_one_comm, adj]
  constructor
  · intro h
    calc J⁻¹ * cT s g * J * g = J⁻¹ * (cT s g * J * g) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h, Matrix.nonsing_inv_mul _ hJ]
  · intro h
    have key : J * (J⁻¹ * cT s g * J * g) = J := by rw [h, Matrix.mul_one]
    simpa only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hJ, Matrix.one_mul] using key

theorem pointsCentraliser_of_commutant_of_adjoint :
    PointsCommutant → PointsAdjoint → PointsCentraliser := by
  intro hC hA F E _ _ _ _ n _ _ σ J γ hreg hAlg hPlus R _ _
  obtain ⟨hinj, hcomm⟩ := hC F E n σ J γ hreg hAlg hPlus R
  refine ⟨hinj, fun u => hA F E n σ J γ hreg R u, fun g => ?_⟩
  have hJ : IsUnit (J.map (inclE (F := F) R)).det := by
    have h := hreg.nondeg.map (inclE (F := F) R)
    rw [RingHom.map_det] at h
    exact h
  have hb : ((bc (inclE (F := F) R) γ : GL n (E ⊗[F] R)) : Matrix n n (E ⊗[F] R)) =
      (γ : Matrix n n E).map (inclE (F := F) R) := rfl
  simp only [centPts, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  unfold UPts UJ
  simp only [Subgroup.mem_mk, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_ofPred_eq,
    Units.ext_iff, Units.val_mul, hb]
  rw [cT_mul_mul_eq_iff_mul_adj_eq_one _ hJ]
  constructor
  · rintro ⟨hunit, hc⟩
    obtain ⟨u, hu⟩ := (hcomm g).1 hc
    have h1 : u * lConj σ J (γ : Matrix n n E) R u = 1 := by
      apply hinj
      rw [map_mul, hA F E n σ J γ hreg R u, hu, map_one, hunit]
    exact ⟨Units.mkOfMulEqOne u _ h1, h1, hu⟩
  · rintro ⟨u, hu, hg⟩
    have hu' : (u : LPts σ J (γ : Matrix n n E) R) * lConj σ J (γ : Matrix n n E) R u = 1 := hu
    refine ⟨?_, (hcomm _).2 ⟨u, hg⟩⟩
    rw [← hg, ← hA F E n σ J γ hreg R, ← map_mul, hu', map_one]

end GlobalTheory.RegSS
end

open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regularSemisimple_centralizer_points_of_commutant_adjoint : GlobalTheory.RegSS.PointsCommutant → GlobalTheory.RegSS.PointsAdjoint → GlobalTheory.RegSS.PointsCentraliser := by
  atlas_forward_decl GlobalTheory.RegSS.pointsCentraliser_of_commutant_of_adjoint
end

section
section
noncomputable section

namespace GlobalTheory.RegSS

def monomialChar (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] (s : ℕ) (a : Fin s → ℤ) :
    (Fin s → Fˣ) →* Ω where
  toFun t := algebraMap F Ω ((∏ j, t j ^ a j : Fˣ) : F)
  map_one' := by simp
  map_mul' x y := by
    simp only [Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib, Units.val_mul, map_mul]

theorem characterMonomial : CharacterMonomial := by
  classical
  intro F Ω _ _ _ s f S c hf
  by_contra hno

  have hdiff : ∀ a, monomialChar F Ω s a ≠ f := by
    intro a hEq
    refine hno ⟨a, fun t => ?_⟩
    rw [← hEq]
    rfl

  let l : ((Fin s → Fˣ) →* Ω) →₀ Ω :=
    Finsupp.single f 1 - ∑ a ∈ S, Finsupp.single (monomialChar F Ω s a) (c a)
  have hvanish : Finsupp.linearCombination Ω
      (fun φ : (Fin s → Fˣ) →* Ω => (φ : (Fin s → Fˣ) → Ω)) l = 0 := by
    funext t
    simp only [l, map_sub, map_sum, Finsupp.linearCombination_single, one_smul,
      Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hf t]
    rw [sub_eq_zero]
    refine Finset.sum_congr rfl fun a _ => ?_
    show _ = c a * algebraMap F Ω ((∏ j, t j ^ a j : Fˣ) : F)
    rw [Algebra.smul_def, mul_comm]
  have hl0 : l = 0 := (linearIndependent_iff.mp (linearIndependent_monoidHom _ Ω)) l hvanish
  have hlf : l f = 1 := by
    simp only [l, Finsupp.sub_apply, Finsupp.single_eq_same, Finsupp.finsetSum_apply]
    rw [Finset.sum_eq_zero fun a _ => Finsupp.single_eq_of_ne' (hdiff a), sub_zero]
  rw [hl0, Finsupp.zero_apply] at hlf
  exact zero_ne_one hlf

end GlobalTheory.RegSS
end
end

open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.laurentPolynomial_character_isMonomial : GlobalTheory.RegSS.CharacterMonomial := by
  atlas_forward_decl GlobalTheory.RegSS.characterMonomial
end

section
section
open GlobalTheory.RegSS
open scoped TensorProduct

namespace GlobalTheory.RegSS

theorem isField_pi_fin_iff {k : ℕ} (A : Fin k → Type) [∀ i, CommRing (A i)]
    [∀ i, Nontrivial (A i)] : IsField (∀ i, A i) ↔ k = 1 ∧ ∀ i, IsField (A i) := by
  constructor
  · intro h

    have hk : k = 1 := by
      rcases Nat.lt_trichotomy k 1 with hlt | heq | hgt
      · obtain ⟨a, b, hab⟩ := h.exists_pair_ne
        have hk0 : k = 0 := by omega
        subst hk0
        exact absurd (funext fun i => i.elim0) hab
      · exact heq
      · let i₀ : Fin k := ⟨0, by omega⟩
        let i₁ : Fin k := ⟨1, hgt⟩
        have hne : i₁ ≠ i₀ := by
          intro hij
          have := congrArg Fin.val hij
          simp [i₀, i₁] at this
        have hx : (Pi.single i₀ (1 : A i₀) : ∀ i, A i) ≠ 0 := by
          intro hx
          have := congrFun hx i₀
          simp at this
        obtain ⟨y, hy⟩ := h.mul_inv_cancel hx
        have := congrFun hy i₁
        rw [Pi.mul_apply, Pi.single_eq_of_ne hne, zero_mul, Pi.one_apply] at this
        exact absurd this zero_ne_one
    refine ⟨hk, ?_⟩
    subst hk
    intro i
    have hdef : IsField (A default) := (RingEquiv.piUnique A).symm.toMulEquiv.isField h
    exact (Unique.eq_default i).symm ▸ hdef
  · rintro ⟨rfl, h⟩
    exact (RingEquiv.piUnique A).toMulEquiv.isField (h default)

theorem tensorFieldIff : TensorFieldIff := by
  intro F E _ _ _ _ P _ _ k K _ _ ⟨e⟩

  let φ : P ⊗[F] E ≃ₐ[F] ∀ i, K i ⊗[F] E :=
    (Algebra.TensorProduct.congr e AlgEquiv.refl).trans
      ((Algebra.TensorProduct.comm F _ E).trans
        ((Algebra.TensorProduct.piRight F F E K).trans
          (AlgEquiv.piCongrRight fun i => Algebra.TensorProduct.comm F E (K i))))

  have : ∀ i, Nontrivial (K i ⊗[F] E) := fun i =>
    TensorProduct.nontrivial_of_linearMap_injective_of_flat_right (R := F) (M := K i) (N := E)
      (Algebra.linearMap F (K i)) (algebraMap F (K i)).injective
  rw [φ.toRingEquiv.toMulEquiv.isField_congr]
  exact isField_pi_fin_iff _

end GlobalTheory.RegSS
end

open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.product_fields_baseChange_isField_iff : GlobalTheory.RegSS.TensorFieldIff := by
  atlas_forward_decl GlobalTheory.RegSS.tensorFieldIff
end

section
section
open Matrix Formalism.UG GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms GlobalTheory.RegSS
open scoped TensorProduct

namespace GlobalTheory.RegSS

theorem subtorusNotCentral_of (hU : UnitaryCommutant) (hL : SubtorusLaurent)
    (hC : CharacterMonomial) : SubtorusNotCentral := by
  intro F E _ _ _ _ n _ _ σ J γ hreg hE s hs A
  by_contra hcon
  push Not at hcon
  have hfield : IsField (E ⊗[F] F) :=
    MulEquiv.isField hE (Algebra.TensorProduct.rid F F E).toMulEquiv
  haveI : Nontrivial (E ⊗[F] F) := hfield.nontrivial
  haveI : CharZero (E ⊗[F] F) := charZero_of_injective_algebraMap (algebraMap F (E ⊗[F] F)).injective
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  let t₀ : Fin s → Fˣ := fun _ => Units.mk0 2 h2
  have hsq : A.hom F (t₀ * t₀) = 1 := by
    refine Units.ext ?_
    ext i j
    have hH : IsHerm (sigR σ F) (J.map (inclE (F := F) F)) := by
      have h : cT (σ : E →+* E) J = J := hreg.herm
      change cT _ _ = _
      conv_rhs => rw [← h]
      ext a b
      simp only [cT, Matrix.transpose_apply, Matrix.map_apply]
      exact (inclE_conj σ F _).symm
    have hdet : IsUnit (J.map (inclE (F := F) F)).det := isUnit_det_map _ hreg.nondeg
    have hsc : ∀ t, (A.hom F t : Matrix n n (E ⊗[F] F)) =
        ((A.hom F t : Matrix n n (E ⊗[F] F)) i i) • (1 : Matrix n n (E ⊗[F] F)) := by
      intro t
      obtain ⟨c, hc⟩ := hU (E ⊗[F] F) hfield (sigR σ F) (sigR_sigR hreg.quad.invol F) n _ hH hdet
        (A.hom F t : Matrix n n (E ⊗[F] F)) (fun g hg => congrArg Units.val (hcon g hg t))
      rw [hc]; simp
    letI := hfield.toField
    let f : (Fin s → Fˣ) →* E ⊗[F] F :=
      { toFun := fun t => (A.hom F t : Matrix n n (E ⊗[F] F)) i i
        map_one' := by simp
        map_mul' := fun a b => by
          rw [map_mul, Units.val_mul, hsc a, smul_mul_assoc, one_mul]
          simp }
    obtain ⟨S, C, hSC⟩ := hL F E n σ J γ s A
    obtain ⟨a, ha⟩ := hC F (E ⊗[F] F) s f S (fun a => C a i i) (fun t => by
      change (A.hom F t : Matrix n n (E ⊗[F] F)) i i = _
      rw [hSC t, Matrix.sum_apply]
      rfl)
    have hfix : sigR σ F (f t₀) = f t₀ := by
      rw [ha]; simp [sigR]
    have hmem := (mem_UJ_iff_mul_adj (sigR σ F) hdet (A.hom F t₀)).1 (A.mem F t₀).1
    have hadj : adj (sigR σ F) (J.map (inclE (F := F) F)) (A.hom F t₀ : Matrix n n (E ⊗[F] F)) =
        (A.hom F t₀ : Matrix n n (E ⊗[F] F)) := by
      rw [hsc t₀, adj_smul, adj_one _ hdet]
      exact congrArg (· • (1 : Matrix n n (E ⊗[F] F))) hfix
    rw [hadj] at hmem
    rw [map_mul, Units.val_mul, hmem, Units.val_one]
  have h1 : t₀ * t₀ = 1 := A.inj F (by rw [hsq, map_one])
  have h4 := congrArg Units.val (congrFun h1 ⟨0, hs⟩)
  simp only [t₀, Pi.mul_apply, Units.val_mul, Units.val_mk0, Pi.one_apply, Units.val_one] at h4
  norm_num at h4

end GlobalTheory.RegSS
end

open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nontrivial_split_subtorus_not_central : GlobalTheory.RegSS.UnitaryCommutant → GlobalTheory.RegSS.SubtorusLaurent → GlobalTheory.RegSS.CharacterMonomial → GlobalTheory.RegSS.SubtorusNotCentral := by
  atlas_forward_decl GlobalTheory.RegSS.subtorusNotCentral_of
end

section
open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reduced_free_algebra_traceForm_perfect : GlobalTheory.RegSS.TracePerfect := by
  first | exact @GlobalTheory.RegSS.tracePerfect | exact GlobalTheory.RegSS.tracePerfect | (intros; apply GlobalTheory.RegSS.tracePerfect <;> assumption)
end

section
open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normOne_small_multiples_by_cocompact_subgroup : GlobalTheory.RegSS.NormOnePacking := by
  first | exact @GlobalTheory.RegSS.normOnePacking | exact GlobalTheory.RegSS.normOnePacking | (intros; apply GlobalTheory.RegSS.normOnePacking <;> assumption)
end

section
open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteAlgebraAdelicLattice_proof : GlobalTheory.RegSS.TensorLattice := by
  first | exact @GlobalTheory.RegSSLattice.tensorLattice | exact GlobalTheory.RegSSLattice.tensorLattice | (intros; apply GlobalTheory.RegSSLattice.tensorLattice <;> assumption)
end

section
open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fieldAdelicUnitTranslateBounded_of_smallMultiples : GlobalTheory.RegSS.NormOnePacking → GlobalTheory.RegSS.TensorLattice → GlobalTheory.RegSS.FieldUnitBounded := by
  first | exact @GlobalTheory.RegSS.fieldUnitBounded_of_packing | exact GlobalTheory.RegSS.fieldUnitBounded_of_packing | (intros; apply GlobalTheory.RegSS.fieldUnitBounded_of_packing <;> assumption)
end

section
open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normOfUnitBounded_of_tensorLattice' : GlobalTheory.RegSS.TensorLattice → GlobalTheory.RegSS.NormOfUnitBounded := by
  first | exact @GlobalTheory.RegSS.normOfUnitBounded_of_tensorLattice | exact GlobalTheory.RegSS.normOfUnitBounded_of_tensorLattice | (intros; apply GlobalTheory.RegSS.normOfUnitBounded_of_tensorLattice <;> assumption)
end

section
noncomputable section

open Matrix Formalism.UG NumberField GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct

namespace GlobalTheory.RegSS

section Clauses

variable {F E : Type} [Field F] [CommRing E] [Algebra F E] {σ : E →ₐ[F] E}
  {n : Type} [Fintype n] [DecidableEq n] {J : Matrix n n E} {γ : GL n E}

theorem clauseAlg (h1 : CyclicSemilocal) (h2 : CyclicAlgebra) (h : IsRegular σ J γ) :
    ClauseAlg σ J γ := by
  have hJ := h.nondeg
  have : Module.Finite F E := quad_finite h.quad
  have : IsArtinianRing E := isArtinian_of_tower F inferInstance
  obtain ⟨v, hv⟩ := h1 E n (γ : Matrix n n E) h.sep
  obtain ⟨⟨e, he⟩, ⟨b⟩, hbij⟩ := h2 E n (γ : Matrix n n E) v hv
  have hinv : adj (σ : E →+* E) J (γ : Matrix n n E) = ((γ⁻¹ : GL n E) : Matrix n n E) :=
    adj_eq_inv _ hJ h.mem
  unfold ClauseAlg
  refine ⟨⟨e, he⟩, ?_, ⟨b⟩, ⟨v, hbij⟩, ?_, hinv, fun x => adj_algebraMap _ hJ x⟩
  ·
    have : Algebra.Etale E (AdjoinRoot (γ : Matrix n n E).charpoly) := by
      apply etale_adjoinRoot_of_isUnit_derivative (Matrix.charpoly_monic _)
      obtain ⟨a, c, hac⟩ := h.sep
      have h' := congrArg (AdjoinRoot.mk (γ : Matrix n n E).charpoly) hac
      simp only [map_add, map_mul, AdjoinRoot.mk_self, mul_zero, zero_add, map_one] at h'
      exact isUnit_iff_exists_inv.2 ⟨_, (mul_comm _ _).trans h'⟩
    exact Algebra.Etale.of_equiv e
  ·
    intro l hl
    apply mem_genAlg_of_commute hbij
    have hl' : (γ : Matrix n n E) * l = l * (γ : Matrix n n E) := commute_of_mem_genAlg rfl hl
    have key : adj (σ : E →+* E) J l * adj (σ : E →+* E) J (γ : Matrix n n E) =
        adj (σ : E →+* E) J (γ : Matrix n n E) * adj (σ : E →+* E) J l := by
      rw [← adj_mul _ hJ, ← adj_mul _ hJ, hl']
    rw [hinv] at key
    set A := adj (σ : E →+* E) J l
    calc A * (γ : Matrix n n E)
        = (γ : Matrix n n E) * ((γ⁻¹ : GL n E) : Matrix n n E) * A * (γ : Matrix n n E) := by
          rw [Units.mul_inv, one_mul]
      _ = (γ : Matrix n n E) * (((γ⁻¹ : GL n E) : Matrix n n E) * A) * (γ : Matrix n n E) := by
          simp only [mul_assoc]
      _ = (γ : Matrix n n E) * (A * ((γ⁻¹ : GL n E) : Matrix n n E)) * (γ : Matrix n n E) := by
          rw [key]
      _ = (γ : Matrix n n E) * A * (((γ⁻¹ : GL n E) : Matrix n n E) * (γ : Matrix n n E)) := by
          simp only [mul_assoc]
      _ = (γ : Matrix n n E) * A := by rw [Units.inv_mul, mul_one]

theorem centRat_iff (h : IsRegular σ J γ) (hA : ClauseAlg σ J γ) (g : GL n E) :
    g ∈ centRat σ J γ ↔ (g : Matrix n n E) ∈ genAlg (γ : Matrix n n E) ∧
      (g : Matrix n n E) * adj (σ : E →+* E) J (g : Matrix n n E) = 1 := by
  obtain ⟨-, -, -, ⟨v, hv⟩, -⟩ := hA
  have hJ := h.nondeg
  rw [centRat, Subgroup.mem_inf, mem_UJ_iff_mul_adj _ hJ, Subgroup.mem_centralizer_iff]
  simp only [Set.mem_singleton_iff, forall_eq]
  constructor
  · rintro ⟨hu, hc⟩
    refine ⟨mem_genAlg_of_commute hv ?_, hu⟩
    have hc' := congrArg Units.val hc
    rw [Units.val_mul, Units.val_mul] at hc'
    exact hc'.symm
  · rintro ⟨hm, hu⟩
    refine ⟨hu, Units.ext ?_⟩
    rw [Units.val_mul, Units.val_mul]
    exact commute_of_mem_genAlg rfl hm

theorem exists_prod_fields (P : Type) [CommRing P] [Algebra F P] (hP : Algebra.Etale F P) :
    ∃ (k : ℕ) (K : Fin k → Type) (_ : ∀ i, Field (K i)) (_ : ∀ i, Algebra F (K i)),
      Nonempty (P ≃ₐ[F] ∀ i, K i) := by
  have := hP
  obtain ⟨I, hI, A, hA, hA', e, -⟩ :=
    (Algebra.FormallyEtale.iff_exists_algEquiv_prod (K := F) (A := P)).1 inferInstance
  have := hI
  let c := Finite.equivFin I
  exact ⟨Nat.card I, fun i => A (c.symm i), fun i => hA _, fun i => hA' _,
    ⟨e.trans (AlgEquiv.piCongrLeft F A c.symm).symm⟩⟩

theorem exists_idemFamily [CharZero F] (h1 : SplitIdempotents) (h : IsRegular σ J γ)
    (hP : ClausePlus σ J γ) (k : ℕ) (K : Fin k → Type) [∀ i, Field (K i)] [∀ i, Algebra F (K i)]
    (e : Nonempty (plusAlg σ J (γ : Matrix n n E) ≃ₐ[F] ∀ i, K i)) {ι : Type}
    (q : ι → {i : Fin k // ¬ IsField (K i ⊗[F] E)}) (hq : Function.Injective q) :
    ∃ ε : ι → Matrix n n E, IsIdemFamily σ J γ ε := by
  obtain ⟨δ, hne, hid, hort, hconj⟩ := h1 F E σ h.quad (plusAlg σ J (γ : Matrix n n E)) k K e
  have hinj := hP.2.2.1

  refine ⟨fun i => ((plusTensor σ J (γ : Matrix n n E) (δ (q i)) : genAlg (γ : Matrix n n E)) :
    Matrix n n E), ?_⟩
  unfold IsIdemFamily
  refine ⟨fun i => (plusTensor σ J (γ : Matrix n n E) (δ (q i))).2, ?_, ?_, ?_, ?_⟩
  · intro i hi
    apply hne (q i)
    apply hinj
    rw [map_zero]
    exact Subtype.ext hi
  · intro i
    exact congrArg Subtype.val (show plusTensor σ J (γ : Matrix n n E) (δ (q i)) *
      plusTensor σ J (γ : Matrix n n E) (δ (q i)) = plusTensor σ J (γ : Matrix n n E) (δ (q i)) by
        rw [← map_mul, hid])
  · intro i j hij
    exact congrArg Subtype.val (show plusTensor σ J (γ : Matrix n n E) (δ (q i)) *
      plusTensor σ J (γ : Matrix n n E) (δ (q j)) = 0 by
        rw [← map_mul, hort _ _ (hq.ne hij), map_zero])
  · intro i j
    rw [← plusTensor_tConj h]
    exact congrArg Subtype.val (show plusTensor σ J (γ : Matrix n n E) (δ (q i)) *
      plusTensor σ J (γ : Matrix n n E) (tConj _ σ (δ (q j))) = 0 by
        rw [← map_mul, hconj, map_zero])

theorem clauseRank [CharZero F] (h1 : SplitIdempotents) (h2 : SubtorusOfIdempotents)
    (h3 : SplitRankUpper) (h4 : TensorFieldIff) (h : IsRegular σ J γ) (hA : ClauseAlg σ J γ)
    (hP : ClausePlus σ J γ) (hC : PointsClause σ J γ) : ClauseRank σ J γ := by
  unfold ClauseRank
  refine ⟨exists_prod_fields _ hP.1, ?_⟩
  intro k K _ _ e
  unfold HasSplitRank
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  ·
    let c := Finite.equivFin {i : Fin k // ¬ IsField (K i ⊗[F] E)}
    obtain ⟨ε, hε⟩ := exists_idemFamily h1 h hP k K e c.symm c.symm.injective
    obtain ⟨A, -⟩ := h2 F E n σ J γ h hA _ ε hε
    exact ⟨A⟩
  · rintro s ⟨A⟩
    exact h3 F E n σ J γ h hP hC k K e s ⟨A⟩
  · intro hn
    obtain ⟨b⟩ := hP.2.1
    obtain ⟨f⟩ := e
    by_contra hk
    have hk0 : k = 0 := by omega
    subst hk0
    obtain ⟨i⟩ := hn
    apply b.ne_zero i
    apply f.injective
    funext j
    exact j.elim0
  · have := quad_nontrivial h.quad
    exact ((AlgEquiv.ofBijective _ hP.2.2).toMulEquiv.isField_congr.symm).trans (h4 F E _ k K e)

theorem centPts_comm (hC : PointsClause σ J γ) (R : Type) [CommRing R] [Algebra F R] :
    ∀ a ∈ centPts σ J γ R, ∀ b ∈ centPts σ J γ R, a * b = b * a := by
  intro a ha b hb
  obtain ⟨-, -, hiff⟩ := hC R
  obtain ⟨u, -, hu⟩ := (hiff a).1 ha
  obtain ⟨w, -, hw⟩ := (hiff b).1 hb
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, ← hu, ← hw, ← map_mul, ← map_mul,
    mul_comm (u : LPts σ J (γ : Matrix n n E) R)]

theorem tConj_tConj (hσ : ∀ x, σ (σ x) = x) (P : Type) [CommRing P] [Algebra F P]
    (x : P ⊗[F] E) : tConj P σ (tConj P σ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul p e => simp [tConj, Algebra.TensorProduct.map_tmul, hσ]
  | add x y hx hy => simp only [map_add, hx, hy]

end Clauses

theorem regularSemisimple_of (a1 : CyclicSemilocal) (a2 : CyclicAlgebra) (a3 : PlusTensorBijective)
    (a4 : PlusEtale) (a5 : PointsCentraliser) (a6 : SplitClosed) (a7 : SplitIdempotents)
    (a8 : SubtorusOfIdempotents) (a9 : SplitRankUpper) (a10 : TensorFieldIff)
    (a11 : SubtorusNotCentral) (a12 : TraceClause) (a13 : FieldUnitBounded)
    (a14 : NormOfUnitBounded) (a15 : ProductUnitBounded) (a16 : MatOfNormBounded)
    (a17 : CompactOfMatBounded) (a18 : NotCompactOfIdempotent) : RegularSemisimple := by
  unfold RegularSemisimple RegularStructure RegularAdelic
  refine ⟨?_, ?_⟩
  · intro F E _ _ _ _ n _ _ σ J γ h
    have hA := clauseAlg a1 a2 h
    have hP := a4 F E n σ J γ h hA (a3 F E n σ J γ h hA)
    have hC := a5 F E n σ J γ h hA hP
    refine ⟨hA, hP, ?_, clauseRank a7 a8 a9 a10 h hA hP hC, ?_, a12 F E n σ J γ h hA⟩
    · unfold ClauseCent
      refine ⟨fun R _ _ => hC R, fun g => centRat_iff h hA g, ?_⟩
      intro Ω _ _ _
      exact a6 F E σ h.quad _ n hP.1 hP.2.1 Ω
    · unfold ClauseProper
      exact ⟨fun R _ _ => centPts_comm hC R, fun hE s hs A => a11 F E n σ J γ h hE s hs A⟩
  · intro F E _ _ _ _ n _ _ σ J γ h k K _ _ e
    have hA := clauseAlg a1 a2 h
    have hP := a4 F E n σ J γ h hA (a3 F E n σ J γ h hA)
    have hC := a5 F E n σ J γ h hA hP
    constructor
    ·
      intro hc
      by_contra hne
      obtain ⟨i, hi⟩ := not_forall.1 hne
      obtain ⟨ε, hε⟩ := exists_idemFamily a7 h hP k K e (ι := Fin 1) (fun _ => ⟨i, hi⟩)
        (fun a b _ => Subsingleton.elim a b)
      obtain ⟨A, hAε⟩ := a8 F E n σ J γ h hA 1 ε hε
      obtain ⟨hmem, hne0, hidem, -, -⟩ := hε
      refine a18 F E n σ J γ h (ε 0) (hmem 0) (hne0 0) (hidem 0) ?_ hc
      intro t
      exact ⟨A.hom (AdeleRing (𝓞 F) F) (fun _ => t), A.mem (AdeleRing (𝓞 F) F) (fun _ => t),
        hAε (AdeleRing (𝓞 F) F) (fun _ => t) 0⟩
    ·
      intro hf
      have : Module.Finite F E := quad_finite h.quad
      obtain ⟨b⟩ := hP.2.1
      have : Module.Finite F (plusAlg σ J (γ : Matrix n n E)) := Module.Finite.of_basis b
      obtain ⟨f⟩ := e
      have : ∀ i, Module.Finite F (K i) := fun i =>
        Module.Finite.of_surjective ((Pi.evalAlgHom F K i).comp f.toAlgHom).toLinearMap
          (fun x => ⟨f.symm (Pi.single i x), by simp⟩)
      have hU : ∀ i, UnitBounded F (K i ⊗[F] E) (tConj (K i) σ) := fun i =>
        a13 F (K i ⊗[F] E) (tConj (K i) σ) (hf i) (tConj_tConj h.quad.invol (K i))
      have hUP := a15 F E σ (plusAlg σ J (γ : Matrix n n E)) k K ⟨f⟩ hU
      have hN := a14 F _ _ hUP
      exact a17 F E n σ J γ h (a16 F E n σ J γ h hA hP hC hN)

theorem regularSemisimple : RegularSemisimple :=
  regularSemisimple_of (GlobalTheory.T.cyclicVector_semilocal_of_cyclicVector_field GlobalTheory.T.cyclicVector_of_separable_charpoly_field) GlobalTheory.T.cyclicVector_generatedAlgebra_structure GlobalTheory.T.regularSemisimple_selfAdjointPart_tensor_bijective GlobalTheory.T.regularSemisimple_selfAdjointPart_etale
    (GlobalTheory.T.regularSemisimple_centralizer_points_of_commutant_adjoint GlobalTheory.T.regularSemisimple_tensor_commutant GlobalTheory.T.regularSemisimple_tensor_involution_adjoint) GlobalTheory.T.etale_tensor_quadratic_split_algClosed GlobalTheory.T.split_factor_idempotents_exist GlobalTheory.T.split_subtorus_of_idempotent_family
    (GlobalTheory.T.centralizer_splitRank_upper_bound GlobalTheory.T.split_subtorus_laurentPolynomial_points GlobalTheory.T.laurentPolynomial_character_isMonomial GlobalTheory.T.conjugate_factor_points_separate) GlobalTheory.T.product_fields_baseChange_isField_iff
    (GlobalTheory.T.nontrivial_split_subtorus_not_central GlobalTheory.T.unitaryGroup_commutant_scalars GlobalTheory.T.split_subtorus_laurentPolynomial_points GlobalTheory.T.laurentPolynomial_character_isMonomial) (GlobalTheory.T.hermitianTraceForm_of_traceForm_perfect GlobalTheory.T.reduced_free_algebra_traceForm_perfect)
    (GlobalTheory.T.fieldAdelicUnitTranslateBounded_of_smallMultiples GlobalTheory.T.normOne_small_multiples_by_cocompact_subgroup GlobalTheory.T.finiteAlgebraAdelicLattice_proof) (GlobalTheory.T.normOfUnitBounded_of_tensorLattice' GlobalTheory.T.finiteAlgebraAdelicLattice_proof)
    (GlobalTheory.T.adelic_unit_translate_bounded_of_factors GlobalTheory.T.finiteAlgebraAdelicLattice_proof) GlobalTheory.T.centraliser_points_bounded_of_normOne_bounded (GlobalTheory.T.adelic_quotient_compact_of_bounded_matrices GlobalTheory.T.finiteAlgebraAdelicLattice_proof)
    (GlobalTheory.T.adelic_quotient_not_compact_of_split_idempotent GlobalTheory.T.det_restrict_range_idempotent_matrix)

end GlobalTheory.RegSS
end
end
