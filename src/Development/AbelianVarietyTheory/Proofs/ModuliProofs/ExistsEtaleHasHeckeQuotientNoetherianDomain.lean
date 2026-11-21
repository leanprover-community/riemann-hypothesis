import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSubgroupEqRangeOfLists
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LbPowDescendsOfIsotropic
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.WeilRos
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFormEqOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTateIsoHeckeQuotient
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenMovePow
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueTangentLift
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsHeckeIsog
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsQuotientByFiniteGroupOfSections
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueFactorThroughEtaleIsogenyReducedStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TrivOfAxesTrivPullbackEtaleIsogeny
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubeOfExistsRelAmple
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.KTrivAwayOfKTrivFibre
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaOfTranslDiff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecImageNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PolPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaGroupKernelTrivialOfOpenCover
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullbackDegPreStrictLineBundleIso
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RangeOfIsPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDescentOfIsReduced
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsClopenWeilIsIff

section
namespace GlobalTheory.CocycleSplit

section SquareZero

variable {B : Type} [CommRing B] {I : Ideal B}

private lemma mul_eq_zero_of_mem_of_sq_eq_bot (hI : I ^ 2 = ⊥) {s t : B} (hs : s ∈ I) (ht : t ∈ I) :
    s * t = 0 := by
  have h : s * t ∈ I ^ 2 := by
    rw [pow_two]
    exact Ideal.mul_mem_mul hs ht
  rw [hI] at h
  exact (Submodule.mem_bot B).1 h

theorem pow_eq_of_sub_one_mem (hI : I ^ 2 = ⊥) {u : B} (hu : u - 1 ∈ I) (N : ℕ) :
    u ^ N = 1 + N * (u - 1) := by
  have hsq : (u - 1) * (u - 1) = 0 := mul_eq_zero_of_mem_of_sq_eq_bot hI hu hu
  induction N with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih]
    push_cast
    linear_combination (↑n : B) * hsq

theorem eq_of_pow_eq (hI : I ^ 2 = ⊥) {N : ℕ} (hN : IsUnit (N : B)) {u v : B} (hu : u - 1 ∈ I)
    (hv : v - 1 ∈ I) (h : u ^ N = v ^ N) : u = v := by
  rw [pow_eq_of_sub_one_mem hI hu N, pow_eq_of_sub_one_mem hI hv N] at h
  have h3 : (N : B) * (u - 1) = N * (v - 1) := add_left_cancel h
  have h4 := hN.mul_left_cancel h3
  linear_combination h4

private lemma isUnit_of_isUnit_quotient_of_sq_eq_bot (hI : I ^ 2 = ⊥) {a : B} (h : IsUnit (Ideal.Quotient.mk I a)) :
    IsUnit a := by
  obtain ⟨v, hv⟩ := h.exists_right_inv
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective v
  have hm : a * w - 1 ∈ I := Ideal.Quotient.eq.1 (by rw [map_mul, map_one]; exact hv)
  have hsq : (a * w - 1) * (a * w - 1) = 0 := mul_eq_zero_of_mem_of_sq_eq_bot hI hm hm
  have h : a * (w * (2 - a * w)) = 1 := by linear_combination (-1 : B) * hsq
  exact ⟨⟨a, w * (2 - a * w), h, by rw [mul_comm]; exact h⟩, rfl⟩

theorem exists_lift_splitting (hI : I ^ 2 = ⊥) {C : Type} [CommGroup C] [Finite C]
    (hN : IsUnit ((Nat.card C : ℕ) : B)) (c : C → C → Bˣ)
    (hc : ∀ x y z, c x y * c (x * y) z = c y z * c x (y * z)) (b : C → B ⧸ I)
    (hb : ∀ x, IsUnit (b x))
    (hbc : ∀ x y, Ideal.Quotient.mk I (c x y) * b (x * y) = b x * b y) :
    ∃ a : C → B, (∀ x, Ideal.Quotient.mk I (a x) = b x) ∧ ∀ x y, c x y * a (x * y) = a x * a y := by
  classical
  have := Fintype.ofFinite C
  rw [Nat.card_eq_fintype_card] at hN
  choose a₀ ha₀ using fun x => Ideal.Quotient.mk_surjective (b x)
  have hu : ∀ x, IsUnit (a₀ x) := fun x => isUnit_of_isUnit_quotient_of_sq_eq_bot hI (by rw [ha₀]; exact hb x)
  set δ : C → C → B := fun x y =>
    ((c x y : B) * a₀ (x * y) - a₀ x * a₀ y) * ↑(hu x).unit⁻¹ * ↑(hu y).unit⁻¹ with hδeq
  have hδI : ∀ x y, δ x y ∈ I := by
    intro x y
    refine I.mul_mem_right _ (I.mul_mem_right _ (Ideal.Quotient.eq.1 ?_))
    rw [map_mul, map_mul, ha₀, ha₀, ha₀]
    exact hbc x y
  have hδ : ∀ x y, (c x y : B) * a₀ (x * y) = a₀ x * a₀ y + a₀ x * a₀ y * δ x y := by
    intro x y
    have h1 := (hu x).mul_val_inv
    have h2 := (hu y).mul_val_inv
    simp only [hδeq]
    linear_combination (-((c x y : B) * a₀ (x * y) - a₀ x * a₀ y) * (a₀ y * ↑(hu y).unit⁻¹)) * h1
      - ((c x y : B) * a₀ (x * y) - a₀ x * a₀ y) * h2
  have hco : ∀ x y z, δ x y + δ (x * y) z = δ y z + δ x (y * z) := by
    intro x y z
    have hP : IsUnit (a₀ x * a₀ y * a₀ z) := ((hu x).mul (hu y)).mul (hu z)
    have E : (c x y : B) * c (x * y) z = c y z * c x (y * z) := by
      have := congrArg (fun t : Bˣ => (t : B)) (hc x y z)
      simpa using this
    have h12 := mul_eq_zero_of_mem_of_sq_eq_bot hI (hδI x y) (hδI (x * y) z)
    have h34 := mul_eq_zero_of_mem_of_sq_eq_bot hI (hδI y z) (hδI x (y * z))
    have A := hδ x y
    have Bq := hδ (x * y) z
    have Cq := hδ y z
    have D := hδ x (y * z)
    rw [mul_assoc x y z] at Bq
    have key : a₀ x * a₀ y * a₀ z * (δ x y + δ (x * y) z - (δ y z + δ x (y * z))) = 0 := by
      linear_combination a₀ (x * (y * z)) * E - (c x y : B) * Bq
        - a₀ z * (1 + δ (x * y) z) * A + (c y z : B) * D + a₀ x * (1 + δ x (y * z)) * Cq
        - a₀ x * a₀ y * a₀ z * h12 + a₀ x * a₀ y * a₀ z * h34
    rw [hP.mul_right_eq_zero, sub_eq_zero] at key
    exact key
  set F : C → B := fun x => ∑ z, δ x z with hFeq
  have hF : ∀ x y, (Fintype.card C : B) * δ x y + F (x * y) = F y + F x := by
    intro x y
    have hs := Finset.sum_congr rfl (fun z (_ : z ∈ Finset.univ) => hco x y z)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul] at hs
    have hre : ∑ z, δ x (y * z) = ∑ z, δ x z :=
      Fintype.sum_equiv (Equiv.mulLeft y) _ _ (fun z => rfl)
    rw [hre] at hs
    simpa [hFeq] using hs
  set ν : B := ↑hN.unit⁻¹ with hνeq
  have hνN : ν * (Fintype.card C : B) = 1 := hN.val_inv_mul
  set η : C → B := fun x => ν * F x with hηeq
  have hηI : ∀ x, η x ∈ I := fun x => I.mul_mem_left _ (I.sum_mem fun z _ => hδI x z)
  have hsum : ∀ x y, δ x y = η x + η y - η (x * y) := by
    intro x y
    simp only [hηeq]
    linear_combination ν * hF x y - δ x y * hνN
  refine ⟨fun x => a₀ x * (1 + η x), fun x => ?_, fun x y => ?_⟩
  · have h0 : Ideal.Quotient.mk I (η x) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (hηI x)
    simp [ha₀, h0]
  · have h1 := mul_eq_zero_of_mem_of_sq_eq_bot hI (hδI x y) (hηI (x * y))
    have h2 := mul_eq_zero_of_mem_of_sq_eq_bot hI (hηI x) (hηI y)
    linear_combination (1 + η (x * y)) * hδ x y + a₀ x * a₀ y * (hsum x y + h1 - h2)

end SquareZero

theorem exists_twisted_algebra (R : Type) [CommRing R] (C : Type) [CommGroup C] (c : C → C → Rˣ)
    (hs : ∀ x y, c x y = c y x) (hc : ∀ x y z, c x y * c (x * y) z = c y z * c x (y * z)) :
    ∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (e : Module.Basis C R A),
      (∀ x y, e x * e y = (c x y : R) • e (x * y)) ∧ e 1 = algebraMap R A (c 1 1) := by
  classical
  set T : C → Module.End R (C →₀ R) := fun x =>
    Finsupp.linearCombination R (fun y => Finsupp.single (x * y) (c x y : R)) with hTeq
  have hTs : ∀ x y (r : R), T x (Finsupp.single y r) = Finsupp.single (x * y) (r * c x y) := by
    intro x y r
    simp [hTeq, Finsupp.linearCombination_single, Finsupp.smul_single]
  have hcR : ∀ x y z, (c x y : R) * c (x * y) z = c y z * c x (y * z) := by
    intro x y z
    have := congrArg (fun t : Rˣ => (t : R)) (hc x y z)
    simpa using this
  have hc1 : ∀ z, c 1 z = c 1 1 := by
    intro z
    have h := hc 1 1 z
    simp only [one_mul] at h
    exact (mul_right_cancel h).symm
  have hT1 : T 1 = (c 1 1 : R) • 1 := by
    apply Finsupp.lhom_ext
    intro z r
    rw [hTs, LinearMap.smul_apply, Module.End.one_apply, Finsupp.smul_single, hc1, one_mul,
      smul_eq_mul, mul_comm]
  have hTmul : ∀ x y, T x * T y = (c x y : R) • T (x * y) := by
    intro x y
    apply Finsupp.lhom_ext
    intro z r
    rw [Module.End.mul_apply, hTs, hTs, LinearMap.smul_apply, hTs, Finsupp.smul_single, mul_assoc,
      smul_eq_mul, mul_assoc x y z]
    congr 1
    linear_combination (-r) * hcR x y z
  have hcomm : ∀ a ∈ Set.range T, ∀ b ∈ Set.range T, a * b = b * a := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    rw [hTmul, hTmul, hs, mul_comm x y]
  have hAc := Algebra.isMulCommutative_adjoin R hcomm
  set S := Algebra.adjoin R (Set.range T) with hSeq
  let hA : CommRing S :=
    { (inferInstance : Ring S) with mul_comm := fun a b => hAc.is_comm.comm a b }
  let f : R →+* S :=
    { toFun := fun r => ⟨algebraMap R (Module.End R (C →₀ R)) r, S.algebraMap_mem r⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun r s => Subtype.ext (map_mul _ r s)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun r s => Subtype.ext (map_add _ r s) }
  let alg : Algebra R S := f.toAlgebra
  let V : S →ₗ[R] Module.End R (C →₀ R) :=
    { toFun := fun a => (a : Module.End R (C →₀ R))
      map_add' := fun _ _ => rfl
      map_smul' := fun r a => by
        show algebraMap R _ r * (a : Module.End R (C →₀ R)) = r • (a : Module.End R (C →₀ R))
        rw [Algebra.smul_def] }
  let e : C → S := fun x => ⟨T x, Algebra.subset_adjoin ⟨x, rfl⟩⟩
  have hliT : LinearIndependent R T := by
    have h0 := (Finsupp.basisSingleOne : Module.Basis C R (C →₀ R)).linearIndependent.units_smul
      (fun x => c x 1)
    apply LinearIndependent.of_comp (LinearMap.applyₗ (Finsupp.single (1 : C) (1 : R)))
    convert h0 using 1
    funext x
    simp [hTs, Units.smul_def, Finsupp.smul_single]
  have hli : LinearIndependent R e := LinearIndependent.of_comp V hliT
  have hone : (1 : Module.End R (C →₀ R)) = ((c 1 1)⁻¹ : Rˣ) • T 1 := by
    rw [hT1, Units.smul_def, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
  have hle : Algebra.adjoin R (Set.range T) ≤ (Submodule.span R (Set.range T)).toSubalgebra
      (by rw [hone]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
      (by
        intro a b ha hb
        have hm := Submodule.mul_mem_mul ha hb
        rw [Submodule.span_mul_span] at hm
        refine Submodule.span_le.2 ?_ hm
        rintro _ ⟨_, ⟨x, rfl⟩, _, ⟨y, rfl⟩, rfl⟩
        beta_reduce
        rw [hTmul]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)) :=
    Algebra.adjoin_le (fun _ h => Submodule.subset_span h)
  have hsp : ⊤ ≤ Submodule.span R (Set.range e) := by
    intro y _
    have hy : (y : Module.End R (C →₀ R)) ∈ Submodule.span R (Set.range T) := hle y.2
    have hr : Set.range T = V '' Set.range e := by
      rw [← Set.range_comp]
      rfl
    rw [hr, ← Submodule.map_span] at hy
    obtain ⟨z, hz, hzy⟩ := hy
    have hzy' : z = y := Subtype.ext hzy
    exact hzy' ▸ hz
  refine ⟨S, hA, alg, Module.Basis.mk hli hsp, fun x y => ?_, ?_⟩
  · rw [Module.Basis.mk_apply, Module.Basis.mk_apply, Module.Basis.mk_apply]
    apply Subtype.ext
    show T x * T y = algebraMap R (Module.End R (C →₀ R)) (c x y : R) * T (x * y)
    rw [hTmul, Algebra.smul_def]
  · rw [Module.Basis.mk_apply]
    apply Subtype.ext
    show T 1 = algebraMap R (Module.End R (C →₀ R)) (c 1 1 : R)
    rw [hT1, Algebra.algebraMap_eq_smul_one]

theorem etale_of_twisted_basis {R : Type} [CommRing R] {C : Type} [CommGroup C] [Finite C]
    (c : C → C → Rˣ) (hc : ∀ x y z, c x y * c (x * y) z = c y z * c x (y * z))
    (hN : IsUnit ((Nat.card C : ℕ) : R)) {A : Type} [CommRing A] [Algebra R A]
    (e : Module.Basis C R A) (he : ∀ x y, e x * e y = (c x y : R) • e (x * y))
    (h1 : e 1 = algebraMap R A (c 1 1)) (hu : ∀ x, IsUnit (e x)) : Algebra.Etale R A := by
  classical
  have hfree : Module.Free R A := Module.Free.of_basis e
  have hfin : Module.Finite R A := Module.Finite.of_basis e
  have hfp : Module.FinitePresentation R A := Module.finitePresentation_of_projective R A
  have hafp : Algebra.FinitePresentation R A := Algebra.FinitePresentation.of_finitePresentation R A
  have hcR : ∀ x y z, (c x y : R) * c (x * y) z = c y z * c x (y * z) := by
    intro x y z
    have := congrArg (fun t : Rˣ => (t : R)) (hc x y z)
    simpa using this
  have hmap : ∀ {T : Type} [CommRing T] [Algebra R T] (g : A →ₐ[R] T) (x y : C),
      algebraMap R T (c x y) * g (e (x * y)) = g (e x) * g (e y) := by
    intro T _ _ g x y
    rw [← map_mul, he, map_smul, Algebra.smul_def]
  have hone : (1 : A) = (↑(c 1 1)⁻¹ : R) • e 1 := by
    rw [h1, Algebra.smul_def, ← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one]
  refine { formallyEtale := ?_, finitePresentation := hafp }
  rw [Algebra.FormallyEtale.iff_comp_bijective]
  intro B _ _ I hI
  have hN' : IsUnit ((Nat.card C : ℕ) : B) := by
    have := hN.map (algebraMap R B)
    simpa using this
  constructor
  · intro g₁ g₂ hg
    apply AlgHom.toLinearMap_injective
    apply e.ext
    intro x
    show g₁ (e x) = g₂ (e x)
    have hq : ∀ x, Ideal.Quotient.mk I (g₂ (e x)) = Ideal.Quotient.mk I (g₁ (e x)) := by
      intro x
      have := congrArg (fun g : A →ₐ[R] B ⧸ I => g (e x)) hg
      simpa using this.symm
    set v : C → B := fun x => ↑((hu x).map g₁).unit⁻¹ with hveq
    have hinv : ∀ x, g₁ (e x) * v x = 1 := fun x => ((hu x).map g₁).mul_val_inv
    set w : C → B := fun x => g₂ (e x) * v x with hweq
    have hw1 : ∀ x, w x - 1 ∈ I := by
      intro x
      have h : w x - 1 = (g₂ (e x) - g₁ (e x)) * v x := by
        simp only [hweq]
        linear_combination hinv x
      rw [h]
      exact I.mul_mem_right _ (Ideal.Quotient.eq.1 (hq x))
    have hwmul : ∀ x y, w (x * y) = w x * w y := by
      intro x y
      have k : algebraMap R B (c x y) * v x * v y = v (x * y) := by
        calc algebraMap R B (c x y) * v x * v y
            = algebraMap R B (c x y) * v x * v y * (g₁ (e (x * y)) * v (x * y)) := by
              rw [hinv, mul_one]
          _ = (algebraMap R B (c x y) * g₁ (e (x * y))) * v x * v y * v (x * y) := by ring
          _ = (g₁ (e x) * v x) * (g₁ (e y) * v y) * v (x * y) := by rw [hmap]; ring
          _ = v (x * y) := by rw [hinv, hinv]; ring
      simp only [hweq]
      rw [← k]
      linear_combination v x * v y * hmap g₂ x y
    have hw1' : w 1 = 1 := by
      have hm := hwmul 1 1
      rw [one_mul] at hm
      have hsq := mul_eq_zero_of_mem_of_sq_eq_bot hI (hw1 1) (hw1 1)
      linear_combination (-1 : B) * hm - hsq
    have hpow : ∀ k : ℕ, w x ^ k = w (x ^ k) := by
      intro k
      induction k with
      | zero => simp [hw1']
      | succ k ih => rw [pow_succ, ih, ← hwmul, pow_succ]
    have hx1 : w x = 1 := by
      refine eq_of_pow_eq hI hN' (hw1 x) (by simp) ?_
      rw [hpow, pow_card_eq_one', hw1', one_pow]
    have hx1' : g₂ (e x) * v x = 1 := hx1
    linear_combination g₂ (e x) * hinv x - g₁ (e x) * hx1'
  · intro f
    set c' : C → C → Bˣ := fun x y => Units.map (algebraMap R B).toMonoidHom (c x y) with hcpeq
    have hc' : ∀ x y z, c' x y * c' (x * y) z = c' y z * c' x (y * z) := by
      intro x y z
      have := congrArg (Units.map (algebraMap R B).toMonoidHom) (hc x y z)
      simpa [hcpeq] using this
    have hbc : ∀ x y, Ideal.Quotient.mk I (c' x y : B) * f (e (x * y)) = f (e x) * f (e y) := by
      intro x y
      have := hmap f x y
      simpa [hcpeq] using this
    obtain ⟨a, ha, hac⟩ := exists_lift_splitting hI hN' c' hc' (fun x => f (e x))
      (fun x => (hu x).map f) hbc
    have ha1u : IsUnit (a 1) := isUnit_of_isUnit_quotient_of_sq_eq_bot hI (by rw [ha]; exact (hu 1).map f)
    have ha1 : a 1 = algebraMap R B (c 1 1) := by
      have h := hac 1 1
      rw [one_mul] at h
      have h' : (c' 1 1 : B) * a 1 = a 1 * a 1 := h
      exact ((ha1u.mul_left_inj).1 h').symm
    set L : A →ₗ[R] B := e.constr R a with hLeq
    have hLe : ∀ x, L (e x) = a x := fun x => e.constr_basis R a x
    have hL1 : L 1 = 1 := by
      rw [hone, L.map_smul, hLe, ha1, Algebra.smul_def, ← map_mul, ← Units.val_mul, inv_mul_cancel,
        Units.val_one, map_one]
    have hbil : (LinearMap.mul R B).compl₁₂ L L = (LinearMap.mul R A).compr₂ L := by
      apply e.ext
      intro x
      apply e.ext
      intro y
      have h := hac x y
      simp only [LinearMap.compl₁₂_apply, LinearMap.mul_apply', LinearMap.compr₂_apply, hLe, he]
      rw [L.map_smul, hLe, Algebra.smul_def, ← h]
      rfl
    have hLmul : ∀ p q, L (p * q) = L p * L q := by
      intro p q
      have := LinearMap.congr_fun (LinearMap.congr_fun hbil p) q
      simpa using this.symm
    refine ⟨AlgHom.ofLinearMap L hL1 hLmul, ?_⟩
    apply AlgHom.toLinearMap_injective
    apply e.ext
    intro x
    show Ideal.Quotient.mk I (L (e x)) = f (e x)
    rw [hLe, ha]

theorem exists_etale_splitting :
    ∀ (R : Type) [CommRing R] (n : ℕ) (C : Type) [CommGroup C] [Finite C] (c : C → C → Rˣ), IsUnit (n : R) → 0 < n → (∀ x : C, x ^ n = 1) → (∀ x y, c x y = c y x) → (∀ x y z, c x y * c (x * y) z = c y z * c x (y * z)) → ∃ (R' : Type) (_ : CommRing R') (_ : Algebra R R'), Algebra.Etale R R' ∧ Module.Finite R R' ∧ Module.FaithfullyFlat R R' ∧ ∃ b : C → R'ˣ, ∀ x y, Units.map (algebraMap R R').toMonoidHom (c x y) * b (x * y) = b x * b y := by
  intro R _ n C _ _ c hn hn0 hexp hs hc
  obtain ⟨A, hA, hAlg, e, he, h1⟩ := exists_twisted_algebra R C c hs hc
  have hone : (1 : A) = (↑(c 1 1)⁻¹ : R) • e 1 := by
    rw [h1, Algebra.smul_def, ← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one]
  have hpow : ∀ x (k : ℕ), ∃ r : Rˣ, e x ^ k = (r : R) • e (x ^ k) := by
    intro x k
    induction k with
    | zero => exact ⟨(c 1 1)⁻¹, by rw [pow_zero, pow_zero, hone]⟩
    | succ k ih =>
      obtain ⟨r, hr⟩ := ih
      refine ⟨r * c (x ^ k) x, ?_⟩
      rw [pow_succ, hr, smul_mul_assoc, he, smul_smul, pow_succ, Units.val_mul]
  have hu : ∀ x, IsUnit (e x) := by
    intro x
    obtain ⟨r, hr⟩ := hpow x n
    rw [hexp, h1, Algebra.smul_def, ← map_mul] at hr
    have hun : IsUnit (e x ^ n) := by
      rw [hr]
      exact (r.isUnit.mul (c 1 1).isUnit).map (algebraMap R A)
    exact (isUnit_pow_iff (Nat.pos_iff_ne_zero.1 hn0)).1 hun
  have hN : IsUnit ((Nat.card C : ℕ) : R) := by
    obtain ⟨m, hm⟩ := card_dvd_exponent_pow_rank' (G := C) hexp
    have hun : IsUnit ((n ^ Group.rank C : ℕ) : R) := by
      rw [Nat.cast_pow]
      exact hn.pow _
    rw [hm, Nat.cast_mul] at hun
    exact isUnit_of_mul_isUnit_left hun
  have hfree : Module.Free R A := Module.Free.of_basis e
  refine ⟨A, hA, hAlg, etale_of_twisted_basis c hc hN e he h1 hu, Module.Finite.of_basis e, ?_,
    fun x => (hu x).unit, fun x y => ?_⟩
  · rcases subsingleton_or_nontrivial R with hR | hR
    · exact { submodule_ne_top := fun m hm => (hm.ne_top (Subsingleton.elim _ _)).elim }
    · have hnt : Nontrivial A := nontrivial_of_ne (e 1) 0 (e.ne_zero 1)
      infer_instance
  · apply Units.ext
    simp only [Units.val_mul, Units.coe_map, IsUnit.unit_spec]
    rw [he, Algebra.smul_def]
    rfl

end GlobalTheory.CocycleSplit
end

section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.ThetaLin

open GlobalTheory.CommPairing GlobalTheory.ThetaSplit ReciprocityTheory.ChartRestriction.G.H1

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem translT_mul [IsCommMonObj A] {T : Over S} (x y : T ⟶ A) :
    Out.translT A (x * y) = Out.translT A x ≫ Out.translT A y := by
  conv_rhs => rw [Out.translT, CommutatorPairing.lift_translT]
  rw [Out.translT]
  congr 1
  show (fst T A ≫ (x * y)) * snd T A = (fst T A ≫ y) * ((fst T A ≫ x) * snd T A)
  rw [MonObj.comp_mul, _root_.mul_assoc, mul_left_comm]

theorem translT_snd {T : Over S} (x : T ⟶ A) :
    (Out.translT A x).left ≫ (snd T A).left = (Out.translPt A x).left := by
  rw [← Over.comp_left, Out.translT, lift_snd]

theorem translT_translPt [IsCommMonObj A] {T : Over S} (x y : T ⟶ A) :
    (Out.translT A x).left ≫ (Out.translPt A y).left = (Out.translPt A (x * y)).left := by
  rw [← translT_snd (x * y), translT_mul, Over.comp_left, Category.assoc, translT_snd]

theorem exists_symm_cocycle (hG : Out.GlobalFnsSt) (hA : IsAbelianScheme A) {L : LB A.left} (hL : L.IsLB) {k : ℤ}
    {T : Over S} {C : Type} [CommGroup C] (θ : C → Out.ThetaGrp A L k T)
    (hm : ∀ c c', (θ (c * c')).pt = (θ c).pt * (θ c').pt) (hc : ∀ c c', Out.CommIsOf A L k (θ c) (θ c') 1) :
    ∃ a : C → C → Γ(T.left, ⊤)ˣ, (∀ x y, a x y = a y x) ∧ (∀ x y z, a x y * a (x * y) z = a y z * a x (y * z)) ∧
      ∀ c c' (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J), Good L z J →
        tval (θ (c * c')) r z J = tval (θ c) r z J * tval (θ c') (r ≫ (Out.translT A (θ c).pt).left) z J *
          gm (r ≫ (fst T A).left) z ⊤ (a c c') := by
  have := hA.comm
  let e : T.left ⟶ (T ⊗ A).left := (lift (𝟙 T) 1).left
  have he : e ≫ (fst T A).left = 𝟙 _ := by rw [← Over.comp_left, lift_fst]; rfl
  have ex : ∀ c c', ∃ a : Γ(T.left, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J), Good L z J →
      tval (θ (c * c')) r z J = tval (θ c) r z J * tval (θ c') (r ≫ (Out.translT A (θ c).pt).left) z J *
          gm (r ≫ (fst T A).left) z ⊤ a := fun c c' => by
    obtain ⟨a, ha⟩ := CommutatorPairing.exists_ratio hL (fun U _ g => by
        refine Eq.trans ?_ (Fintype.prod_sum_type _).symm
        simp only [Fin.prod_univ_two, Sum.elim_inl, Sum.elim_inr]
        show g (snd T A).left ^ k * g (Out.translPt A (θ (c * c')).pt).left ^ (-k) =
          g (snd T A).left ^ k * g (Out.translPt A (θ c).pt).left ^ (-k) *
            (g ((Out.translT A (θ c).pt).left ≫ (snd T A).left) ^ k *
              g ((Out.translT A (θ c).pt).left ≫ (Out.translPt A (θ c').pt).left) ^ (-k))
        rw [translT_snd, translT_translPt, hm]
        simp only [zpow_neg, _root_.mul_assoc, inv_mul_cancel_left]) (fst T A).left e he (surj_fst hG hA T)
      (θ (c * c')).isGen
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (θ c).isGen
        (DVR.pullGen_isGen _ _ _ _ (θ c').isGen (Out.translT A (θ c).pt).left))
    exact ⟨a, fun Z r z J hJ => (ha Z r z J hJ).trans (congrArg (· * _) ((val_mul hJ _ _ _).trans
      (congrArg (tval (θ c) r z J * ·) (val_pull hJ _ _ _))))⟩
  choose a ha using ex
  have inj : ∀ u u' : Γ(T.left, ⊤)ˣ, (∀ (y : T.left) (J), Good L y J →
      gm (e ≫ (fst T A).left) y ⊤ u = gm (e ≫ (fst T A).left) y ⊤ u') → u = u' :=
    fun u u' h => unit_ext fun y _ => by
      choose J hJ using fun χ : T.left ⟶ A.left => exists_chart hL (χ y)
      rw [← he]; exact h y J hJ
  refine ⟨a, fun c c' => inj _ _ fun y J hJ => ?_, fun c c' c'' => inj _ _ fun y J hJ => ?_, ha⟩
  · have e₁ := ha c c' _ e y J hJ
    have e₂ := ha c' c _ e y J hJ
    have e₃ := (commIsOf_iff hL _ _ _).1 (hc c c') _ e y J hJ
    rw [map_one, _root_.mul_one] at e₃
    rw [e₃] at e₁
    rw [mul_comm c' c, e₁] at e₂
    exact mul_left_cancel e₂
  · have e₁ := ha c c' _ e y J hJ
    have e₂ := ha (c * c') c'' _ e y J hJ
    have e₃ := ha c' c'' _ (e ≫ (Out.translT A (θ c).pt).left) y J hJ
    have e₄ := ha c (c' * c'') _ e y J hJ
    rw [_root_.mul_assoc c] at e₂
    rw [Category.assoc, Category.assoc, translT_fst, ← Over.comp_left _ _ _ (Out.translT A (θ c).pt), ← translT_mul, ← hm] at e₃
    rw [map_mul, map_mul]
    apply Additive.ofMul.injective
    have a₁ := congrArg Additive.ofMul e₁
    have a₂ := congrArg Additive.ofMul e₂
    have a₃ := congrArg Additive.ofMul e₃
    have a₄ := congrArg Additive.ofMul e₄
    simp only [ofMul_mul] at a₁ a₂ a₃ a₄ ⊢
    linear_combination (norm := abel) a₃ + a₄ - a₁ - a₂

theorem exists_linearisation {L : LB A.left} (hL : L.IsLB) (n : ℕ) {T : Over S} {C : Type} [CommGroup C]
    (θ : C → Out.ThetaGrp A L n T) (a : C → C → Γ(T.left, ⊤)ˣ)
    (ha : ∀ c c' (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J), Good L z J →
        tval (θ (c * c')) r z J = tval (θ c) r z J * tval (θ c') (r ≫ (Out.translT A (θ c).pt).left) z J *
          gm (r ≫ (fst T A).left) z ⊤ (a c c'))
    {S' : Scheme.{0}} {A' : Over S'} [GrpObj A'] [IsCommMonObj A'] {f : S' ⟶ S} {φ : A'.left ⟶ A.left}
    (hp : IsGrpPullback A' A f φ) {L' : LB A'.left} (hL' : L'.IsLB) (hw : LBIso L' (L.pull φ))
    (τ : S' ⟶ T.left) (hτ : τ ≫ T.hom = f) (i' : C →* (𝟙_ (Over S') ⟶ A'))
    (hi : ∀ c, τ ≫ (θ c).pt.left = (i' c).left ≫ φ) (b : C → Γ(S', ⊤)ˣ)
    (hb : ∀ c c', Units.map τ.appTop.hom.toMonoidHom (a c c') * b (c * c') = b c * b c') :
    ∃ u : ∀ c, LB.Gen (LB.LinComb (lbPow L' n) (K := Fin 2) ![𝟙 A'.left, transl (i' c)] ![1, -1]),
      (∀ c, (u c).IsGen) ∧ ∀ c c', LB.Gen.Corr (lbPow L' n) _ _ _ _ (u (c * c'))
        (LB.mulGen (lbPow L' n) _ _ _ _ (u c) (LB.pullGen (lbPow L' n) _ _ (u c') (transl (i' c)))) := by
  obtain ⟨w, hw⟩ := hw
  have hτ' : (τ : (𝟙_ (Over S')).left ⟶ T.left) ≫ T.hom = (𝟙_ (Over S')).hom ≫ f :=
    hτ.trans (Category.id_comp _).symm
  choose θ' hθ' hR using fun c => WeilPull.exists_rel_down hp (T := 𝟙_ (Over S')) τ hτ' hL hL' w hw (i' c) (θ c) (hi c)
  have key : ∀ c c' (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over S') ⊗ A').left) (z : Z) (J), Good L' z J →
      tval (θ' (c * c')) r z J = tval (θ' c) r z J * tval (θ' c') (r ≫ (Out.translT A' (i' c)).left) z J *
        gm ((r ≫ (fst _ A').left) ≫ τ) z ⊤ (a c c') := fun c c' Z r z J hJ => by
    choose J₀ hJ₀ using fun ψ : Z ⟶ A.left => exists_chart hL (ψ z)
    have e := ha c c' Z (r ≫ (psiO hp (T := 𝟙_ (Over S')) τ hτ').left) z J₀ hJ₀
    have t : (r ≫ (psiO hp (T := 𝟙_ (Over S')) τ hτ').left) ≫ (Out.translT A (θ c).pt).left =
        (r ≫ (Out.translT A' (i' c)).left) ≫ (psiO hp (T := 𝟙_ (Over S')) τ hτ').left := by
      rw [Category.assoc, Category.assoc, psi_transl hp (T := 𝟙_ (Over S')) τ hτ' _ _ (hi c)]
    have g : (r ≫ (psiO hp (T := 𝟙_ (Over S')) τ hτ').left) ≫ (fst T A).left = (r ≫ (fst _ A').left) ≫ τ := by
      rw [Category.assoc, psi_fst, Category.assoc]
    have s : (r ≫ (Out.translT A' (i' c)).left) ≫ (snd _ A').left = r ≫ (Out.translPt A' (i' c)).left := by
      rw [Category.assoc, translT_snd]
    have q : (r ≫ (Out.translT A' (i' c)).left) ≫ (Out.translPt A' (i' c')).left =
        r ≫ (Out.translPt A' (i' (c * c'))).left := by
      rw [Category.assoc, translT_translPt, map_mul]
    rw [t, g, hR _ Z _ z J₀ J hJ₀ hJ, hR _ Z _ z J₀ J hJ₀ hJ, hR _ Z _ z J₀ J hJ₀ hJ, hθ', hθ', hθ', s, q] at e
    simp only [zpow_neg] at e
    apply Additive.ofMul.injective
    have e' := congrArg Additive.ofMul e
    simp only [ofMul_mul, ofMul_inv] at e' ⊢
    linear_combination (norm := abel) e'
  choose v hv ev using fun c => exists_gen_theta hL' (θ' c) (hθ' c)
  choose u hu eu using fun c => exists_gen_lbPow n (ε := ![1, -1]) (fun k => by fin_cases k <;> simp) (v c) (hv c)
    (pullU A'.hom ⊤ (b c))
  refine ⟨u, hu, fun c c' => corr_of_val (DVR.linComb_isLB L' hL' _ _) fun y J hJ => ?_⟩
  have hJ' : Good L' y (fun χ => J χ PUnit.unit) := fun χ => Set.mem_iInter.1 (hJ χ) PUnit.unit
  have g : ∀ (r : A'.left ⟶ A'.left) (a : Γ(S', ⊤)ˣ), gm r y ⊤ (pullU A'.hom ⊤ a) = gm (r ≫ A'.hom) y ⊤ a :=
    fun r a => gm_pull r A'.hom y ⊤ trivial a
  refine Eq.trans ?_ ((val_mul hJ _ _ _).trans (congrArg (val (u c) (𝟙 _) y J * ·) (val_pull hJ _ _ _))).symm
  rw [eu _ _ _ y J hJ, eu _ _ _ y J hJ, eu _ _ _ y J hJ, g, g, g, Category.assoc, transl_hom,
    ev _ _ _ y _ hJ', ev _ _ _ y _ hJ', ev _ _ _ y _ hJ', key c c' _ _ y _ hJ']
  have f₁ : (𝟙 A'.left ≫ (lift (toUnit A') (𝟙 A')).left) ≫ (fst _ A').left = 𝟙 A'.left ≫ A'.hom := by
    rw [Category.assoc, ← Over.comp_left, lift_fst]; rfl
  have f₂ : (𝟙 A'.left ≫ (lift (toUnit A') (𝟙 A')).left) ≫ (Out.translT A' (i' c)).left =
      (𝟙 A'.left ≫ transl (i' c)) ≫ (lift (toUnit A') (𝟙 A')).left := by
    rw [Category.assoc, Category.assoc, transl_lift]
  have f₃ := gm_pull (𝟙 A'.left ≫ A'.hom) τ y ⊤ trivial (a c c')
  have f₄ := congrArg (gm (𝟙 A'.left ≫ A'.hom) y ⊤) (hb c c')
  rw [map_mul, map_mul] at f₄
  rw [f₁, f₂, _root_.mul_assoc]
  exact (congrArg (_ * ·) ((congrArg (· * _) f₃.symm).trans f₄)).trans (_root_.mul_mul_mul_comm _ _ _ _)

theorem exists_lifts_away {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {L : LB A.left} (hL : L.IsLB) {k : ℤ}
    {C : Type} [Finite C] (x : C → (𝟙_ (Over (Sp R)) ⟶ A)) (q : PrimeSpectrum R)
    (hW : ∀ c, Out.WeilIs A L k (x c) (x c) 1) :
    ∃ r : R, r ∉ q.asIdeal ∧ ∀ c, ∃ θ : Out.ThetaGrp A L k (Over.mk (spMap (algebraMap R (Localization.Away r)))),
      θ.pt = toUnit _ ≫ x c := by
  choose V hV hθ using fun c => hW c q
  have ho : IsOpen (X := PrimeSpectrum R) (⋂ c, (V c).1) := isOpen_iInter_of_finite fun c => (V c).2
  obtain ⟨_, ⟨r, rfl⟩, hr, hle⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    (Set.mem_iInter.2 hV) ho
  refine ⟨r, hr, fun c => ?_⟩
  obtain ⟨⟨θ, -, e, -⟩, -⟩ := hθ c
  have hsub : Set.range (spMap (algebraMap R (Localization.Away r))) ⊆ Set.range (V c).ι := by
    rintro _ ⟨p, rfl⟩
    have : PrimeSpectrum.comap (algebraMap R (Localization.Away r)) p ∈
        (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) := by
      rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]; exact ⟨p, rfl⟩
    exact ⟨⟨_, Set.mem_iInter.1 (hle this) c⟩, rfl⟩
  let h : Over.mk (spMap (algebraMap R (Localization.Away r))) ⟶ Out.overRes (V c) :=
    Over.homMk (IsOpenImmersion.lift (V c).ι _ hsub) (by
      show IsOpenImmersion.lift (V c).ι _ hsub ≫ (V c).ι ≫ 𝟙 _ = _
      rw [Category.comp_id, IsOpenImmersion.lift_fac]; rfl)
  obtain ⟨θ', e', -⟩ := exists_pull hL h θ
  exact ⟨θ', by rw [e', e, ← Category.assoc, toUnit_unique (h ≫ _) (toUnit _)]⟩

end GlobalTheory.ThetaLin

namespace GlobalTheory

open ThetaLin in

theorem exists_etale_linearisation : ∀ (R : Type) [CommRing R] (P : Out.PolAV (Sp R)) (n : ℕ) (C : Type) [CommGroup C] [Finite C] (i : C →* (𝟙_ (Over (Sp R)) ⟶ P.A)) (q : PrimeSpectrum R), IsUnit (n : R) → 0 < n → (∀ c : C, c ^ n = 1) → (∀ c c', Out.WeilIs P.A P.L n (i c) (i c') 1) → ∃ (R' : Type) (_ : CommRing R') (_ : Algebra R R'), Algebra.Etale R R' ∧ q ∈ Set.range (PrimeSpectrum.comap (algebraMap R R')) ∧ ∀ (A' : Over (Sp R')) [GrpObj A'] [IsCommMonObj A'] (φ : A'.left ⟶ P.A.left) (L' : LB A'.left) (i' : C →* (𝟙_ (Over (Sp R')) ⟶ A')), IsGrpPullback A' P.A (spMap (algebraMap R R')) φ → L'.IsLB → LBIso L' (P.L.pull φ) → (∀ c, (i' c).left ≫ φ = spMap (algebraMap R R') ≫ (i c).left) → ∃ u : ∀ c : C, LB.Gen (LB.LinComb (lbPow L' n) (K := Fin 2) ![𝟙 A'.left, ((toUnit A' ≫ i' c) * 𝟙 A').left] ![1, -1]), (∀ c, (u c).IsGen) ∧ ∀ c c', LB.Gen.Corr (lbPow L' n) _ _ _ _ (u (c * c')) (LB.mulGen (lbPow L' n) _ _ _ _ (u c) (LB.pullGen (lbPow L' n) _ _ (u c') ((toUnit A' ≫ i' c) * 𝟙 A').left)) := by
  intro R _ P n C _ _ i q hnR hn htor hW
  have hG := GlobalTheory.globalFns_holds
  have := P.isAb.comm
  obtain ⟨r, hr, hθ⟩ := exists_lifts_away P.isLB (fun c => i c) q (fun c => hW c c)
  choose θ hθ using hθ
  let R₁ := Localization.Away r
  obtain ⟨a, hs, hc, ha⟩ := exists_symm_cocycle hG P.isAb P.isLB θ
    (fun c c' => by rw [hθ, hθ, hθ, map_mul, MonObj.comp_mul]) (fun c c' => by
      refine (GlobalLift.weilIs_iff_commIsOf hG P.isAb P.isLB _ _ _).1 ?_
      have H := CommPairing.weilIs_pull hG P.isAb P.isLB (toUnit (Over.mk (spMap (algebraMap R R₁)))) (hW c c')
      rw [map_one] at H
      rw [hθ, hθ]; exact H)
  let e₁ : Γ(Sp R₁, ⊤) ≃+* R₁ := (Scheme.ΓSpecIso (CommRingCat.of R₁)).commRingCatIsoToRingEquiv
  let E₁ : Γ(Sp R₁, ⊤)ˣ →* R₁ˣ := Units.map e₁.toRingHom.toMonoidHom
  obtain ⟨R', _, _, het, -, hff, b, hb⟩ := GlobalTheory.CocycleSplit.exists_etale_splitting R₁ n C (fun x y => E₁ (a x y))
    (by simpa using hnR.map (algebraMap R R₁)) hn htor (fun x y => congrArg E₁ (hs x y))
    (fun x y z => (map_mul E₁ _ _).symm.trans ((congrArg E₁ (hc x y z)).trans (map_mul E₁ _ _)))
  letI : Algebra R R' := ((algebraMap R₁ R').comp (algebraMap R R₁)).toAlgebra
  have : IsScalarTower R R₁ R' := IsScalarTower.of_algebraMap_eq' rfl
  have : Algebra.Etale R R₁ := Algebra.Etale.of_isLocalizationAway r
  refine ⟨R', inferInstance, inferInstance, Algebra.Etale.comp R R₁ R', ?_, ?_⟩
  · have h₁ : q ∈ Set.range (PrimeSpectrum.comap (algebraMap R R₁)) := by
      rw [PrimeSpectrum.localization_away_comap_range R₁ r]; exact hr
    obtain ⟨p, rfl⟩ := h₁
    obtain ⟨p', rfl⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := R₁) (B := R') p
    exact ⟨p', rfl⟩
  · intro A' _ _ φ L' i' hp hL' hw hi
    have hτ : spMap (algebraMap R₁ R') ≫ spMap (algebraMap R R₁) = spMap (algebraMap R R') := by
      rw [← Spec.map_comp]; rfl
    let e' : Γ(Sp R', ⊤) ≃+* R' := (Scheme.ΓSpecIso (CommRingCat.of R')).commRingCatIsoToRingEquiv
    refine exists_linearisation P.isLB n θ a ha hp hL' hw (spMap (algebraMap R₁ R')) hτ i' (fun c => ?_)
      (fun c => Units.map e'.symm.toRingHom.toMonoidHom (b c)) (fun c c' => ?_)
    · rw [hθ, hi, ← hτ, Category.assoc]; rfl
    · rw [← map_mul, ← hb, map_mul]
      congr 1
      apply Units.ext
      apply e'.injective
      have := congrArg (fun g => g.hom (a c c').val)
        (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R₁ R')))
      exact this.trans (e'.apply_symm_apply _).symm

end GlobalTheory
end
end

section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory

open HeckePoint

theorem hasQuot_of_isIsogT : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (𝔓 : Ideal (𝓞 E)) (p i : ℕ) (S : Scheme.{0}) [IsReduced S] (s : S ⟶ Sp (KA l)) (o : Ob D l s) (t' : SAB H S) (ψ : o.t.G ⟶ t'.G) (K : Set o.t.G.left), 1 ≤ D.p + D.q → admitted l 𝔓 p → IsProper t'.G.hom → Out.RelAmple t'.G t'.PP.L → Out.KTriv t'.G t'.PP.L → IsIsogT o.t t' p ψ → KerSet ψ K → HeckeSet D o.t 𝔓 p i K → HasQuot o p K := by
  intro E _ _ _ H D l 𝔓 p i S _ s o t' ψ K _ ⟨h𝔓, hco, hp, hp𝔓, hpM⟩ hpr ham hkt hI hker hHk
  obtain ⟨hhom, hfin, het, hsur, hlin, hiso⟩ := hI
  have hG : Out.GlobalFnsSt := (show Out.Laws from GlobalTheory.firstFiveLaws.1).globalFns
  have hab := isAbelianScheme_of_proper o.t o.proper
  have hab' := isAbelianScheme_of_proper t' hpr
  have hW := fun (n : ℤ) (T : Over S) (x y : T ⟶ o.t.G) c c' =>
    weilIs_along_hom hG _ o.t.G t'.G ψ o.t.PP.L t'.PP.L (p ^ 2) n T x y c c' hab hab' o.t.PP.isLB t'.PP.isLB hhom hiso
  obtain ⟨p₀, hp₀⟩ := exists_inv_mod hp hpM
  have hMM : l.M ∣ l.M' := Nat.dvd_lcm_left _ _
  have hAM : l.A ∣ l.M' := Nat.dvd_lcm_right _ _
  have etaM : ∀ a, o.eta (l.M • a) = 1 := fun a => o.eta_ker _ (by
    rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
    exact Submodule.smul_mem_smul (natCast_M_mem l) Submodule.mem_top)
  let o' : Ob D l s :=
    { t := t', proper := hpr, ample := ham, ktriv := hkt
      eta := fun a => o.eta (p₀ • a) ≫ ψ
      eta_add := fun a c => by rw [smul_add, o.eta_add, MonObj.mul_comp]
      eta_ker := fun a ha => by rw [o.eta_ker _ (nsmul_mem ha _), MonObj.one_comp]
      etaA := fun a => o.etaA (p₀ • a) ≫ ψ
      etaA_add := fun a c => by rw [smul_add, o.etaA_add, MonObj.mul_comp]
      etaA_ker := fun a => by rw [smul_comm, o.etaA_ker, MonObj.one_comp]
      geom := by
        intro k _ _ x β hx
        obtain ⟨hdet, I, hζ, hA, hM⟩ := o.geom k x β hx
        refine ⟨fun τ => ?_, ?_⟩
        · simp only [← LieEtale.lieMult_iff_of_etale _ _ _ _ ψ o.t.act t'.act hhom het hlin k x τ]
          exact hdet τ
        obtain ⟨C, hC, -, c₂, c₃, c₄, c₅, -⟩ := hHk k x
        have mem : ∀ z : Over.mk x ⟶ o.t.G, z ≫ ψ = 1 ↔ z ∈ C := fun z => (hker k x z).trans (hC z).symm
        let ψx : (Over.mk x ⟶ o.t.G) →* (Over.mk x ⟶ t'.G) :=
          MonoidHom.mk' (fun z => z ≫ ψ) fun a c => MonObj.mul_comp a c ψ
        have uniq : ∀ (n : ℤ) (z w : Over.mk x ⟶ o.t.G) (c c' : kˣ),
            Out.WeilIs o.t.G o.t.PP.L n z w (unitOn c) → Out.WeilIs o.t.G o.t.PP.L n z w (unitOn c') → c = c' :=
          fun n z w c c' h h' => (unitOn_bijective k).1 (CommutatorPairing.weilIs_unique hG hab o.t.PP.isLB h h')
        obtain ⟨I', hζ', hev⟩ := exists_tateIso_heckeQuotient SimAlg.sim_group E H D 𝔓 p k _ _ _
          (fun a g => g ≫ t'.act.act a) _
          (fun n g g' c => Out.WeilIs t'.G t'.PP.L n g g' (unitOn c)) I ψx h𝔓 hco hp hp𝔓
          (fun y => exists_lift_pt ψ x y)
          (fun a z => by
            show (z ≫ _) ≫ ψ = (z ≫ ψ) ≫ _
            rw [Category.assoc, hlin, Category.assoc])
          (fun J hJ z _ hz' => (mem z).2 (c₂ J hJ hz'))
          (fun z hz => ⟨by
            rw [← comp_act_natCast o.t.act]
            refine c₃ ((mem z).1 hz) _ ?_
            rw [Nat.cast_pow, pow_two]
            refine Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) ?_
            have := Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hp𝔓
            rwa [map_natCast] at this, c₃ ((mem z).1 hz)⟩)
          (fun z w hz hw => by
            have h := c₄ z ((mem z).1 hz) w ((mem w).1 hw)
            rw [← Nat.cast_pow] at h
            exact (congrArg (Out.WeilIs o.t.G o.t.PP.L ((p ^ 2 : ℕ) : ℤ) z w) unitOn_one).mpr h)
          (by rw [← c₅, show ψx.ker = C from Subgroup.ext mem])
          (fun n z w c c' _ _ _ h h' => uniq n z w c c' h h')
          (fun n z w c hn hz hw h => by
            obtain ⟨c', hc⟩ := exists_weil t'.cub hz hw
            have hc' := (weilIs_iff t'.cub hG hab' hz hw hc c').2 rfl
            obtain ⟨c', rfl⟩ := (unitOn_bijective k).2 c'
            have h₂ := (hW n _ z w 1 _ hc').1
            rw [← Nat.cast_mul] at h₂
            rw [uniq _ z w c c' h h₂]
            exact hc')
        refine ⟨I', by rw [hζ']; exact hζ, fun a => ?_, fun a ha => ?_⟩
        · rw [hev l.A p₀ l.A_pos (hp₀.of_dvd hAM), ← hA, ← Category.assoc]; rfl
        · rw [hev l.M p₀ (by have := l.three_le; omega) (hp₀.of_dvd hMM), ← hM _ (nsmul_mem ha _),
            ← Category.assoc]; rfl }
  refine ⟨o', ψ, ⟨⟨hhom, hfin, het, hsur, hlin, hiso⟩, fun p' hp' a => ?_⟩, hker⟩
  have e := modEq_of_inv hp' hp₀
  exact ⟨congrArg (· ≫ ψ) (eq_of_modEq o.eta o.eta_add etaM (e.of_dvd hMM) a),
    congrArg (· ≫ ψ) (eq_of_modEq o.etaA o.etaA_add o.etaA_ker (e.of_dvd hAM) a)⟩

end GlobalTheory
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory

theorem exists_oAct_descend_of_etale_isogeny :
    ∀ (O : Type) [CommRing O] (S : Scheme.{0}) [IsReduced S] (A B : Over S) [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B] (ψ : A ⟶ B) (a : OAct O A), IsAbelianScheme A → IsAbelianScheme B → IsMonHom ψ → IsFinite ψ.left → Etale ψ.left → Surjective ψ.left → (∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S) (x : Over.mk t ⟶ A) (c : O), x ≫ ψ = 1 → (x ≫ a.act c) ≫ ψ = 1) → ∃ b : OAct O B, ∀ c, a.act c ≫ ψ = ψ ≫ b.act c := by
  intro O _ S _ A B _ _ _ _ ψ a hA hB hψ hf he hs hker
  have hsep : IsSeparated B.hom := by
    have := hB.proper
    infer_instance
  have key : ∀ c : O, ∃ g' : B ⟶ B, IsMonHom g' ∧ ψ ≫ g' = a.act c ≫ ψ ∧
      ∀ g'' : B ⟶ B, ψ ≫ g'' = a.act c ≫ ψ → g'' = g' := by
    intro c
    have := a.hom c
    refine GlobalTheory.T.exists_unique_factor_through_etale_isogeny_reduced S A B B ψ (a.act c ≫ ψ) hA hB hsep hψ hf he hs inferInstance ?_
    intro k _ _ t x hx
    rw [← Category.assoc]
    exact hker k t x c hx
  choose f hf1 hf2 hf3 using key
  refine ⟨⟨f, hf1, ?_, ?_, ?_⟩, fun c => (hf2 c).symm⟩
  · refine (hf3 1 _ ?_).symm
    rw [a.one, Category.id_comp, Category.comp_id]
  · intro x y
    refine (hf3 _ _ ?_).symm
    rw [← Category.assoc, hf2, Category.assoc, hf2, a.mul, Category.assoc]
  · intro x y
    refine (hf3 _ _ ?_).symm
    rw [MonObj.comp_mul, hf2, hf2, a.add]
    exact (map_mul (IsMonHom.monoidHom ψ A) _ _).symm

end GlobalTheory
end

section
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.DescentFamily

open GlobalTheory.CechPic

theorem card_ker_pullback {S S' : Scheme.{0}} (t : S' ⟶ S) {A B : Over S} [GrpObj A] [GrpObj B] (ψ : A ⟶ B) :
    Nat.card {x : 𝟙_ (Over S') ⟶ (Over.pullback t).obj A // x ≫ (Over.pullback t).map ψ = 1} =
      Nat.card {x : Over.mk ((𝟙_ (Over S')).hom ≫ t) ⟶ A // x ≫ ψ = 1} := by
  have hA := isGrpPullback_pullback A t
  have hB := isGrpPullback_pullback B t
  have inj : ∀ {G : Over S} [GrpObj G] (h : IsGrpPullback ((Over.pullback t).obj G) G t (pullback.fst G.hom t)),
      Function.Injective (pushHom h (𝟙_ (Over S'))) := fun h x y e =>
    Over.OverMorphism.ext (h.1.hom_ext (congrArg (fun z => z.left) e) (by rw [Over.w, Over.w]))
  have surj : Function.Surjective (pushHom hA (𝟙_ (Over S'))) := fun x =>
    ⟨Over.homMk (hA.1.lift x.left (𝟙_ (Over S')).hom (Over.w x)) (hA.1.lift_snd _ _ _),
      Over.OverMorphism.ext (hA.1.lift_fst _ _ _)⟩
  refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.ofBijective _ ⟨inj hA, surj⟩) fun x => ?_)
  have e : pushHom hB (𝟙_ (Over S')) (x ≫ (Over.pullback t).map ψ) = pushHom hA (𝟙_ (Over S')) x ≫ ψ := by
    refine Over.OverMorphism.ext ?_
    show (x.left ≫ ((Over.pullback t).map ψ).left) ≫ pullback.fst B.hom t = (x.left ≫ pullback.fst A.hom t) ≫ ψ.left
    rw [Category.assoc, Category.assoc]
    exact congrArg (x.left ≫ ·) (pullback.lift_fst _ _ _)
  exact (map_eq_one_iff _ (inj hB)).symm.trans (Eq.congr_left e)

theorem kTriv_fibre {S : Scheme.{0}} (P : Out.PolAV S) {n : ℕ} (B : Over S) [GrpObj B] (ψ : P.A ⟶ B) (M : LB B.left)
    (hn : 0 < n) (hB : IsAbelianScheme B) (hM : M.IsLB) [IsMonHom ψ] [IsFinite ψ.left] [Etale ψ.left]
    [Surjective ψ.left] (hiso : LBIso (lbPow P.L n) (M.pull ψ.left)) (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (t : Sp k ⟶ S) (hc : Nat.card {x : Over.mk (𝟙 _ ≫ t) ⟶ P.A // x ≫ ψ = 1} = n ^ P.g) :
    Out.KTriv ((Over.pullback t).obj B) (M.pull (pullback.fst B.hom t)) := by
  have hw : ((Over.pullback t).map ψ).left ≫ pullback.fst B.hom t = pullback.fst P.A.hom t ≫ ψ.left :=
    pullback.lift_fst _ _ _
  have hp : IsPullback (pullback.fst P.A.hom t) ((Over.pullback t).map ψ).left ψ.left (pullback.fst B.hom t) := by
    refine IsPullback.of_bot ?_ hw.symm (IsPullback.of_hasPullback B.hom t)
    have e : ((Over.pullback t).map ψ).left ≫ pullback.snd B.hom t = pullback.snd P.A.hom t :=
      Over.w ((Over.pullback t).map ψ)
    rw [e, Over.w ψ]
    exact IsPullback.of_hasPullback _ _
  have hL' := pull_isLB P.isLB (pullback.fst P.A.hom t)
  have hM' := pull_isLB hM (pullback.fst B.hom t)
  have h₁ : (lbPow (P.L.pull (pullback.fst P.A.hom t)) n).IsLB := LB.isLB_linComb hL' _ _
  have h₂ := pull_isLB hM' ((Over.pullback t).map ψ).left
  have h₀ := (cls_eq_iff (LB.isLB_linComb P.isLB _ _) (pull_isLB hM _)).2 hiso
  rw [cls_lbPow P.isLB, cls_pull hM] at h₀
  have he : cls _ h₁ = cls _ h₂ := by
    rw [cls_lbPow hL', cls_pull hM', cls_pull P.isLB, cls_pull hM, ← pull_comp, hw, pull_comp, ← h₀, map_nsmul]
  have hmon : IsMonHom ((Over.pullback t).map ψ) := inferInstance
  refine kTriv_of_descent firstFiveLaws.1 k (StrictPull.polPull P t) n _ ((Over.pullback t).map ψ) _ hn
    (PolPull.isAbelianScheme_of_isGrpPullback hB (isGrpPullback_pullback B t)) hM' hmon
    (MorphismProperty.of_isPullback (P := @IsFinite) hp inferInstance)
    (MorphismProperty.of_isPullback (P := @Etale) hp inferInstance)
    (MorphismProperty.of_isPullback (P := @Surjective) hp inferInstance)
    ((card_ker_pullback t ψ).trans hc) ?_
  refine (cls_eq_iff (LB.isLB_linComb h₁ _ _) (LB.isLB_linComb h₂ _ _)).1 ?_
  refine (cls_cube_two (G := (Over.pullback t).obj P.A) h₁ _ _ _).trans
    (Eq.trans ?_ (cls_cube_two (G := (Over.pullback t).obj P.A) h₂ _ _ _).symm)
  exact congrArg (fun c => lam (G := (Over.pullback t).obj P.A) c _ _) he

end GlobalTheory.DescentFamily

namespace GlobalTheory

open GlobalTheory.CechPic

theorem relAmple_kTriv_of_descent_family : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (P : Out.PolAV (Sp R)) (n : ℕ) (B : Over (Sp R)) [GrpObj B] (ψ : P.A ⟶ B) (M : LB B.left), (∀ m : ℕ, 0 < m → IsUnit (m : R)) → 0 < n → IsAbelianScheme B → M.IsLB → IsMonHom ψ → IsFinite ψ.left → Etale ψ.left → Surjective ψ.left → (∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R), Nat.card {x : Over.mk t ⟶ P.A // x ≫ ψ = 1} = n ^ P.g) → LBIso (lbPow P.L n) (M.pull ψ.left) → Out.RelAmple B M ∧ Out.KTriv B M := by
  intro R _ _ P n B _ ψ M hu hn hB hM hψ hf he hs hc hiso
  have hA := P.isAb
  have hn' : (lbPow P.L n).IsLB := LB.isLB_linComb P.isLB _ _
  have hid : IsFinite (𝟙 P.A : P.A ⟶ P.A).left := by rw [Over.id_left]; infer_instance
  have a₁ : Out.RelAmple P.A (lbPow P.L n) :=
    (relAmple_finite_pow_iso _ P.A P.A (𝟙 _) P.L n hn hA hA P.isLB hid).2.1.2 P.ample
  have a₂ : Out.RelAmple P.A (M.pull ψ.left) :=
    (relAmple_finite_pow_iso _ P.A P.A (𝟙 _) _ 1 one_pos hA hA hn' hid).2.2.2 _ (pull_isLB hM _) hiso a₁
  have a₃ : Out.RelAmple B M :=
    (relAmple_finite_pow_iso _ P.A B ψ M 1 one_pos hA hB hM hf).2.2.1 inferInstance hs a₂
  refine ⟨a₃, ?_⟩
  have loc : ∀ q : PrimeSpectrum R, ∃ f : R, f ∉ q.asIdeal ∧
      Out.KTriv ((Over.pullback (spMap (algebraMap R (Localization.Away f)))).obj B)
        (M.pull (pullback.fst B.hom (spMap (algebraMap R (Localization.Away f))))) := by
    intro q
    let k := AlgebraicClosure q.asIdeal.ResidueField
    let x : R →+* k := (algebraMap q.asIdeal.ResidueField k).comp (algebraMap R q.asIdeal.ResidueField)
    have : CharZero k := charZero_of_inj_zero fun m hm => by
      by_contra h
      have := (hu m (Nat.pos_of_ne_zero h)).map x
      rw [map_natCast, hm] at this
      exact not_isUnit_zero this
    obtain ⟨f, hf, H⟩ := kTriv_away_of_kTriv_fibre firstFiveLaws.1.globalFns R B M k x hB hM a₃
      (DescentFamily.kTriv_fibre P B ψ M hn hB hM hiso k (spMap x) (hc k _))
    refine ⟨f, fun h => hf ?_, H⟩
    show algebraMap q.asIdeal.ResidueField k (algebraMap R q.asIdeal.ResidueField f) = 0
    rw [Ideal.algebraMap_residueField_eq_zero.2 h, map_zero]
  choose f hf H using loc
  let j : ∀ q, Sp (Localization.Away (f q)) ⟶ Sp R := fun q => spMap (algebraMap R (Localization.Away (f q)))
  have hj : ∀ q, IsOpenImmersion (j q) := fun q => IsOpenImmersion.of_isLocalization (f q)
  let G := fun q => (Over.pullback (j q).isoOpensRange.inv).obj ((Over.pullback (j q)).obj B)
  have gp : ∀ q, IsGrpPullback (G q) ((Over.pullback (j q)).obj B) (j q).isoOpensRange.inv (pullback.fst _ _) :=
    fun q => isGrpPullback_pullback _ _
  have hM₁ := fun q => pull_isLB hM (pullback.fst B.hom (j q))
  have hB₁ := fun q => PolPull.isAbelianScheme_of_isGrpPullback hB (isGrpPullback_pullback B (j q))
  have key := fun q => pol_pull _ _ _ (G q) _ _ _ _ (hM₁ q) (pull_isLB (hM₁ q) _) (hB₁ q) (gp q)
    ((cls_eq_iff (pull_isLB (hM₁ q) _) (pull_isLB (hM₁ q) _)).1 rfl)
  refine CoverGlue.kTriv_of_cover (Sp R) (PrimeSpectrum R) (fun q => (j q).opensRange) B G
    (fun q => pullback.fst _ (j q).isoOpensRange.inv ≫ pullback.fst B.hom (j q)) ?_
    (fun q => ((gp q).comp (isGrpPullback_pullback B (j q))).congr (Scheme.Hom.isoOpensRange_inv_comp _) rfl)
    M _ hM (fun q => pull_isLB (hM₁ q) _) (fun q => ?_) hB (fun q => (key q).1) (fun q => (key q).2.2 (H q))
  · refine top_le_iff.1 fun q _ => TopologicalSpace.Opens.mem_iSup.2 ⟨q, ?_⟩
    have : q ∈ Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away (f q)))) := by
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away (f q)) (f q)]
      exact hf q
    exact this
  · rw [← cls_eq_iff (pull_isLB (hM₁ q) _) (pull_isLB hM _), cls_pull (hM₁ q), cls_pull hM, cls_pull hM, pull_comp]

end GlobalTheory
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relAmple_principal_descendedBundle_noetherian : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (P : Out.PolAV (Sp R)) (n : ℕ) (B : Over (Sp R)) [GrpObj B] (ψ : P.A ⟶ B) (M : LB B.left), (∀ m : ℕ, 0 < m → IsUnit (m : R)) → 0 < n → IsAbelianScheme B → M.IsLB → IsMonHom ψ → IsFinite ψ.left → Etale ψ.left → Surjective ψ.left → (∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R), Nat.card {x : Over.mk t ⟶ P.A // x ≫ ψ = 1} = n ^ P.g) → LBIso (lbPow P.L n) (M.pull ψ.left) → Out.RelAmple B M ∧ Out.KTriv B M := by
  atlas_forward_decl GlobalTheory.relAmple_kTriv_of_descent_family
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkFam

open CechPic

theorem exists_quotient_triple_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (t : SAB H (Sp R)) (g p : ℕ) (B : Over (Sp R)) [GrpObj B] (ψ : t.G ⟶ B) (M : LB B.left), (∀ m : ℕ, 0 < m → IsUnit (m : R)) → 0 < p → IsProper t.G.hom → SmoothOfRelativeDimension g t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → IsAbelianScheme B → M.IsLB → IsMonHom ψ → IsFinite ψ.left → Etale ψ.left → Surjective ψ.left → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Sp R), Nat.card {z : Over.mk x ⟶ t.G // z ≫ ψ = 1} = p ^ (2 * g) ∧ ∀ z : Over.mk x ⟶ t.G, z ≫ ψ = 1 → z ^ p ^ 2 = 1 ∧ ∀ a, (z ≫ t.act.act a) ≫ ψ = 1) → LBIso (lbPow t.PP.L (p ^ 2)) (M.pull ψ.left) → ∃ (t' : SAB H (Sp R)) (ψ' : t.G ⟶ t'.G), IsProper t'.G.hom ∧ Out.RelAmple t'.G t'.PP.L ∧ Out.KTriv t'.G t'.PP.L ∧ IsIsogT t t' p ψ' ∧ ∀ (T : Over (Sp R)) (z : T ⟶ t.G), z ≫ ψ' = 1 ↔ z ≫ ψ = 1 := by
  intro E _ _ _ H R _ _ _ t g p B _ ψ M hR hp hprop hsm hamp hK hB hM hψ hf he hs hker hiso
  have laws : Out.Laws := GlobalTheory.firstFiveLaws.1
  have hA : IsAbelianScheme t.G := AbelianSchemeGerms.isAbelianScheme_of_proper t.G t.semi
  have hL := t.PP.isLB
  let P : Out.PolAV (Sp R) :=
    { A := t.G, isAb := hA, g := g, smoothDim := hsm, L := t.PP.L, isLB := hL,
      rigid := ⟨t.PP.rig, t.PP.rigGen⟩, sym := sym_of_isSymmetric t.PP t.sym, ample := hamp, ktriv := hK }
  have hn : 0 < p ^ 2 := pow_pos hp 2
  have := hB.comm
  have hred : IsReduced (Sp R) := inferInstance
  have hc : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Sp R),
      Nat.card {z : Over.mk x ⟶ t.G // z ≫ ψ = 1} = (p ^ 2) ^ g := fun k _ _ x => by
    rw [← pow_mul]; exact (hker k x).1
  have hMamp : Out.RelAmple B M := (GlobalTheory.T.relAmple_principal_descendedBundle_noetherian R P (p ^ 2) B ψ M hR hn hB hM hψ hf he hs hc hiso).1
  have hΘ : ∃ s : LB.Gen (Theta B M), s.IsGen := cube_of_relAmple _ B M hB hM hMamp
  obtain ⟨act, hact⟩ := GlobalTheory.exists_oAct_descend_of_etale_isogeny (𝓞 E) (Sp R) t.G B ψ t.act hA hB hψ hf he hs
    fun k _ _ x z c hz => ((hker k x).2 z hz).2 c
  have hα : ∀ a, ψ ≫ act.act a = t.act.act a ≫ ψ := fun a => (hact a).symm
  have hunit : IsUnit ((p ^ 2 : ℕ) : Γ(Sp R, ⊤)) := by
    have h := (hR _ hn).map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    rwa [map_natCast] at h
  set l := cls t.PP.L hL with hl
  set m := cls M hM with hm
  have hψm : pull ψ.left m = (p ^ 2) • l := by
    rw [← cls_lbPow hL (p ^ 2) (LB.isLB_linComb hL _ _)]
    exact ((cls_eq_iff _ (pull_isLB hM _)).2 hiso).symm
  have lamψ : ∀ {T : Over (Sp R)} (u v : T ⟶ t.G), lam m (u ≫ ψ) (v ≫ ψ) = (p ^ 2) • lam l u v := fun u v => by
    rw [← lam_pull, hψm, lam_nsmul]
  have adj : ∀ a, LBIso (cubeLB B ![fst B B ≫ act.act a, snd B B] M)
      (cubeLB B ![fst B B, snd B B ≫ act.act (H.bar a)] M) := by
    intro a
    have := act.hom a
    have := act.hom (H.bar a)
    have adjA : ∀ {T : Over (Sp R)} (u v : T ⟶ t.G), lam l (u ≫ t.act.act a) v = lam l u (v ≫ t.act.act (H.bar a)) := by
      intro T u v
      have h := (cls_eq_iff (LB.isLB_linComb hL _ _) (LB.isLB_linComb hL _ _)).2 (t.adj a)
      have h' := congrArg (pull (lift u v).left)
        ((cls_cube_two hL _ _ _).symm.trans (h.trans (cls_cube_two hL _ _ _)))
      simpa only [pull_lam, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc] using h'
    have adjψ : ∀ {T : Over (Sp R)} (u v : T ⟶ t.G),
        lam m ((u ≫ ψ) ≫ act.act a) (v ≫ ψ) = lam m (u ≫ ψ) ((v ≫ ψ) ≫ act.act (H.bar a)) := by
      intro T u v
      rw [Category.assoc, Category.assoc, hα, hα, ← Category.assoc, ← Category.assoc, lamψ, lamψ, adjA]
    have h₁ : (cubeLB B ![fst B B ≫ act.act a, snd B B] M).IsLB := LB.isLB_linComb hM _ _
    have h₂ : (cubeLB B ![fst B B, snd B B ≫ act.act (H.bar a)] M).IsLB := LB.isLB_linComb hM _ _
    have hN := LB.isLB_div h₂ h₁
    have val : ∀ {T : Over (Sp R)} (x y : T ⟶ B), lam m (x ≫ act.act a) y = lam m x (y ≫ act.act (H.bar a)) →
        ∃ s : ((LB.div (cubeLB B ![fst B B, snd B B ≫ act.act (H.bar a)] M)
          (cubeLB B ![fst B B ≫ act.act a, snd B B] M)).pull (lift x y).left).Gen, s.IsGen := by
      intro T x y h
      refine (cls_eq_zero_iff (pull_isLB hN _)).1 ?_
      rw [cls_pull hN, cls_div h₂ h₁, cls_cube_two hM, cls_cube_two hM, map_sub, pull_lam, pull_lam, lift_fst,
        lift_snd, lift_fst_assoc, lift_snd_assoc, ← hm, h, sub_self]
    refine GlobalTheory.T.triv_of_axes_triv_pullback_etale_isogeny (Sp R) t.G B ψ M _ (p ^ 2) hA hB hM hMamp hN hψ hf he hs hn hunit
      (fun k _ _ x z hz => ((hker k x).2 z hz).1) (val _ _ ?_) (val _ _ ?_) ?_
    · rw [MonObj.one_comp, lam_one_left, lam_one_left]
    · rw [MonObj.one_comp, lam_one_right, lam_one_right]
    · have e : ψ ⊗ₘ ψ = lift (fst t.G t.G ≫ ψ) (snd t.G t.G ≫ ψ) := by ext <;> simp
      rw [e]
      exact val _ _ (adjψ _ _)
  obtain ⟨PP, cub, hsym, hPP, -, hprim, hadj⟩ :=
    GlobalTheory.PrimNorm.exists_primitive_normalisation laws.globalFns E H _ B act M hB hM hΘ adj
  have hP' := PP.isLB
  have hpull : pull ψ.left (cls PP.L hP') = (p ^ 2) • l := by
    have h := (cls_eq_iff hL (LB.isLB_linComb hL _ _)).2 t.prim
    have h' := (cls_eq_iff hP' (LB.isLB_linComb hM _ _)).2 hPP
    have e : l = lam l (𝟙 _) (t.act.act H.w0) := h.trans (cls_cube_two hL _ _ _)
    have e' : cls PP.L hP' = lam m (𝟙 _) (act.act H.w0) := h'.trans (cls_cube_two hM _ _ _)
    rw [e', pull_lam, hα, Category.comp_id, ← Category.id_comp ψ, ← Category.assoc, Category.comp_id, lamψ, ← e]
  have hn' : (lbPow t.PP.L (p ^ 2)).IsLB := LB.isLB_linComb hL _ _
  have hfinal : LBIso (lbPow t.PP.L (p ^ 2)) (PP.L.pull ψ.left) := by
    rw [← cls_eq_iff hn' (pull_isLB hP' _), cls_lbPow hL, cls_pull hP', hpull]
  obtain ⟨a₃, a₄⟩ := GlobalTheory.T.relAmple_principal_descendedBundle_noetherian R P (p ^ 2) B ψ PP.L hR hn hB hP' hψ hf he hs hc hfinal
  exact ⟨{ G := B, semi := isSemiAbelian_of_isAbelianScheme B hB, act := act, PP := PP, cub := cub, sym := hsym,
           adj := hadj, prim := hprim }, ψ, hB.proper, a₃, a₄, ⟨hψ, hf, he, hs, hact, hfinal⟩, fun _ _ => Iff.rfl⟩

end GlobalTheory.HkFam
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_quotient_triple_family_reduced_noetherian : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (t : SAB H (Sp R)) (g p : ℕ) (B : Over (Sp R)) [GrpObj B] (ψ : t.G ⟶ B) (M : LB B.left), (∀ m : ℕ, 0 < m → IsUnit (m : R)) → 0 < p → IsProper t.G.hom → SmoothOfRelativeDimension g t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → IsAbelianScheme B → M.IsLB → IsMonHom ψ → IsFinite ψ.left → Etale ψ.left → Surjective ψ.left → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Sp R), Nat.card {z : Over.mk x ⟶ t.G // z ≫ ψ = 1} = p ^ (2 * g) ∧ ∀ z : Over.mk x ⟶ t.G, z ≫ ψ = 1 → z ^ p ^ 2 = 1 ∧ ∀ a, (z ≫ t.act.act a) ≫ ψ = 1) → LBIso (lbPow t.PP.L (p ^ 2)) (M.pull ψ.left) → ∃ (t' : SAB H (Sp R)) (ψ' : t.G ⟶ t'.G), IsProper t'.G.hom ∧ Out.RelAmple t'.G t'.PP.L ∧ Out.KTriv t'.G t'.PP.L ∧ IsIsogT t t' p ψ' ∧ ∀ (T : Over (Sp R)) (z : T ⟶ t.G), z ≫ ψ' = 1 ↔ z ≫ ψ = 1 := by
  atlas_forward_decl GlobalTheory.HkFam.exists_quotient_triple_family
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkLoc

theorem range_subset_iff {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsSeparated G.hom] {N n : ℕ}
    {σ : Fin n → (𝟙_ (Over S) ⟶ G)} {K : Set G.left} (h : Lists N σ K) {k : Type} [Field k] (x : Sp k ⟶ S)
    (z : Over.mk x ⟶ G) : Set.range z.left ⊆ K ↔ ∃ j, z = toUnit _ ≫ σ j := by
  obtain ⟨-, rfl, -⟩ := h
  obtain ⟨q⟩ : Nonempty (Sp k) := inferInstance
  constructor
  · intro hz
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 (hz ⟨q, rfl⟩)
    have h1 := ListedSubgroup.eq_comp_section G.hom (σ j).left (Over.w (σ j)) _ q hj
    rw [Over.w z] at h1
    exact ⟨j, Over.OverMorphism.ext h1⟩
  · rintro ⟨j, rfl⟩ _ ⟨y, rfl⟩
    exact Set.mem_iUnion.2 ⟨j, x y, (Scheme.Hom.comp_apply x (σ j).left y).symm⟩

theorem isUnit_natCast {F R : Type} [Field F] [CharZero F] [CommRing R] (s : Sp R ⟶ Sp F) (m : ℕ) (hm : 0 < m) :
    IsUnit (m : R) := by
  have h : IsUnit (m : F) := (Nat.cast_ne_zero.2 hm.ne').isUnit
  simpa using h.map (Spec.preimage s).hom

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

noncomputable abbrev pol {S : Scheme.{0}} {s : S ⟶ Sp (KA l)} (o : Ob D l s) : Out.PolAV S :=
  have h := GlobalTheory.obj_isAbelianScheme_dim_rigidified_sym E H D l _ _ S s o
  { A := o.t.G, isAb := h.1, g := Module.finrank ℚ E / 2 * (D.p + D.q), smoothDim := h.2.1, L := o.t.PP.L,
    isLB := o.t.PP.isLB, rigid := h.2.2.1, sym := h.2.2.2, ample := o.ample, ktriv := o.ktriv }

theorem weilIs_one {S : Scheme.{0}} [ConnectedSpace S] {s : S ⟶ Sp (KA l)} (o : Ob D l s) {𝔓 : Ideal (𝓞 E)}
    {p i n : ℕ} {σ : Fin n → (𝟙_ (Over S) ⟶ o.t.G)} {K : Set o.t.G.left} (hp : 0 < p)
    (hu : IsUnit ((p ^ 2 : ℕ) : Γ(S, ⊤))) (hL : Lists (p ^ 2) σ K) (hH : HeckeSet D o.t 𝔓 p i K) (j j' : Fin n) :
    Out.WeilIs o.t.G o.t.PP.L ((p ^ 2 : ℕ) : ℤ) (σ j) (σ j') 1 := by
  have := o.proper
  obtain ⟨U, hU, hW⟩ := GlobalTheory.exists_clopen_weilIs_iff GlobalTheory.firstFiveLaws.1 S (pol o) (p ^ 2) (𝟙_ (Over S)) (σ j) (σ j') 1
    (pow_pos hp 2) hu (hL.1 j) (hL.1 j') (one_pow _)
  obtain ⟨s₀⟩ : Nonempty S := inferInstance
  let k : Type := AlgebraicClosure (S.residueField s₀)
  let x : Sp k ⟶ S := Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s₀) k)) ≫ S.fromSpecResidueField s₀
  obtain ⟨C, hC, hk⟩ := hH k x
  obtain ⟨q⟩ : Nonempty (Sp k) := inferInstance
  have hmem : ∀ j, toUnit (Over.mk x) ≫ σ j ∈ C := fun j =>
    (hC _).2 ((range_subset_iff hL x _).2 ⟨j, rfl⟩)
  have h₁ := (hW (Over.mk x) (toUnit _)).1 (by
    rw [map_one, Nat.cast_pow]
    exact hk.2.2.2.1 _ (hmem j) _ (hmem j'))
  have : ConnectedSpace (𝟙_ (Over S)).left := ‹ConnectedSpace S›
  have hc : IsClopen (U : Set (𝟙_ (Over S)).left) := ⟨hU, U.isOpen⟩
  have h₂ : (U : Set (𝟙_ (Over S)).left) = Set.univ := hc.eq_univ ⟨_, h₁ ⟨q, rfl⟩⟩
  have h₃ := (hW (𝟙_ (Over S)) (𝟙 _)).2 (by rw [h₂]; exact Set.subset_univ _)
  rw [map_one, Category.id_comp, Category.id_comp] at h₃
  exact h₃

theorem hasQuot_of_linearisation {R : Type} [CommRing R] [IsNoetherianRing R] [_root_.IsReduced R]
    {s : Sp R ⟶ Sp (KA l)} (o : Ob D l s) {𝔓 : Ideal (𝓞 E)} {p i n : ℕ}
    {σ : Fin n → (𝟙_ (Over (Sp R)) ⟶ o.t.G)} {K : Set o.t.G.left} (hD : 1 ≤ D.p + D.q) (hA : admitted l 𝔓 p)
    (hL : Lists (p ^ 2) σ K) (hH : HeckeSet D o.t 𝔓 p i K) (C : Type) [CommGroup C] [Finite C]
    (v : C →* (𝟙_ (Over (Sp R)) ⟶ o.t.G)) (e : C → Fin n) (he : Function.Injective e) (hv : ∀ c, v c = σ (e c))
    (hσ : ∀ j, ∃ c, v c = σ j)
    (hu : ∃ u : ∀ c : C, LB.Gen (LB.LinComb (lbPow o.t.PP.L (p ^ 2)) (K := Fin 2)
        ![𝟙 o.t.G.left, ((toUnit o.t.G ≫ v c) * 𝟙 o.t.G).left] ![1, -1]), (∀ c, (u c).IsGen) ∧
      ∀ c c', LB.Gen.Corr (lbPow o.t.PP.L (p ^ 2)) _ _ _ _ (u (c * c')) (LB.mulGen (lbPow o.t.PP.L (p ^ 2)) _ _ _ _ (u c)
        (LB.pullGen (lbPow o.t.PP.L (p ^ 2)) _ _ (u c') ((toUnit o.t.G ≫ v c) * 𝟙 o.t.G).left))) :
    HasQuot o p K := by
  have := o.proper
  obtain ⟨u, hu₁, hu₂⟩ := hu
  have hinj : ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (c : C),
      toUnit (Over.mk t) ≫ v c = 1 → c = 1 := fun k _ _ t c h => by
    have h₁ : toUnit (Over.mk t) ≫ v c = toUnit (Over.mk t) ≫ v 1 := by rw [h, map_one, MonObj.comp_one]
    rw [hv, hv] at h₁
    exact he (hL.2.2 k t (congrArg CommaMorphism.left h₁))
  obtain ⟨B, gB, ψ, hB, hψ, hf, het, hs, hk₁, hk₂⟩ : ∃ (B : Over (Sp R)) (_ : GrpObj B) (ψ : o.t.G ⟶ B),
      IsAbelianScheme B ∧ IsMonHom ψ ∧ IsFinite ψ.left ∧ Etale ψ.left ∧ Surjective ψ.left ∧ (∀ c, v c ≫ ψ = 1) ∧
      ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (x : Over.mk t ⟶ o.t.G),
        x ≫ ψ = 1 ↔ ∃ c, x = toUnit _ ≫ v c :=
    GlobalTheory.exists_quotient_by_finite_group_of_sections R (pol o) C v hinj
  obtain ⟨M, hM, hiso⟩ := GlobalTheory.LinDescent.exists_descent (Sp R) o.t.G B ψ C v (lbPow o.t.PP.L (p ^ 2))
    (LB.isLB_linComb o.t.PP.isLB _ _) hψ hf het hs hk₁ (fun k _ _ t => ⟨hk₂ k t, hinj k t⟩) u hu₁ hu₂
  have hker : KerSet ψ K := fun k _ _ t z => by
    rw [hk₂, range_subset_iff hL]
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨e c, by rw [hv]⟩
    · rintro ⟨j, rfl⟩
      obtain ⟨c, hc⟩ := hσ j
      exact ⟨c, by rw [hc]⟩
  obtain ⟨t', ψ', h₁, h₂, h₃, h₄, h₅⟩ := GlobalTheory.T.exists_quotient_triple_family_reduced_noetherian E H R o.t _ p B ψ M (isUnit_natCast s) hA.2.2.1.pos o.proper
    (pol o).smoothDim o.ample o.ktriv hB hM hψ hf het hs (fun k _ _ x => by
      obtain ⟨C₀, hC₀, hk⟩ := hH k x
      have hm : ∀ z : Over.mk x ⟶ o.t.G, z ≫ ψ = 1 ↔ z ∈ C₀ := fun z => (hker k x z).trans (hC₀ z).symm
      refine ⟨(Nat.card_congr (Equiv.subtypeEquivRight hm)).trans hk.2.2.2.2.1, fun z hz => ⟨?_, fun a => ?_⟩⟩
      · obtain ⟨c, rfl⟩ := (hk₂ k x z).1 hz
        rw [← MonObj.comp_pow, hv, hL.1, MonObj.comp_one]
      · exact (hm _).2 (hk.1 z ((hm z).1 hz) a)) hiso
  exact GlobalTheory.hasQuot_of_isIsogT E H D l 𝔓 p i (Sp R) s o t' ψ' K hD hA h₁ h₂ h₃ h₄
    (fun k _ _ x z => (h₅ _ z).trans (hker k x z)) hH

end GlobalTheory.HkLoc

open GlobalTheory.HkLoc in

theorem GlobalTheory.exists_etale_hasQuot_of_lists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (𝔓 : Ideal (𝓞 E)) (p i n : ℕ) (R : Type) [CommRing R] [IsNoetherianRing R] [IsDomain R] (s : Sp R ⟶ Sp (KA l)) (o : Ob D l s) (σ : Fin n → (𝟙_ (Over (Sp R)) ⟶ o.t.G)) (K : Set o.t.G.left) (q : Sp R), 1 ≤ D.p + D.q → admitted l 𝔓 p → Lists (p ^ 2) σ K → HeckeSet D o.t 𝔓 p i K → ∃ (R' : Type) (_ : CommRing R') (π : Sp R' ⟶ Sp R) (o' : Ob D l (π ≫ s)) (m : ObjMap o' o π), Etale π ∧ q ∈ Set.range π ∧ HasQuot o' p (m.toSABMap.φ ⁻¹' K) := by
  intro E _ _ _ H D l 𝔓 p i n R _ _ _ s o σ K q hD hA hL hH
  have hp : 0 < p := hA.2.2.1.pos
  have hΓ : ∀ m : ℕ, 0 < m → IsUnit (m : Γ(Sp R, ⊤)) := fun m hm => by
    simpa using (isUnit_natCast s m hm).map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  obtain ⟨C, hC⟩ := GlobalTheory.HkFam.exists_subgroup_eq_range_of_lists E H D 𝔓 p i n (Sp R) o.t σ K o.proper (hΓ p hp) hL hH
  have hmem : ∀ c : C, ∃ j, σ j = c := fun c => by
    have : c.1 ∈ (C : Set (𝟙_ (Over (Sp R)) ⟶ o.t.G)) := c.2
    rwa [hC] at this
  choose e he using hmem
  have einj : Function.Injective e := fun c c' h => Subtype.ext (by rw [← he, h, he])
  have : Finite C := Finite.of_injective e einj
  obtain ⟨R', _, _, het, hq, hlin⟩ := GlobalTheory.exists_etale_linearisation R (pol o) (p ^ 2) C C.subtype q
    (isUnit_natCast s _ (pow_pos hp 2)) (pow_pos hp 2)
    (fun c => Subtype.ext (by
      have := hL.1 (e c)
      rw [he] at this
      exact this))
    (fun c c' => by
      have := weilIs_one o hp (hΓ _ (pow_pos hp 2)) hL hH (e c) (e c')
      rw [he, he] at this
      exact this)
  let π : Sp R' ⟶ Sp R := spMap (algebraMap R R')
  have hπ : Etale π := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact RingHom.etale_algebraMap.2 het
  have : IsNoetherianRing R' := Algebra.FiniteType.isNoetherianRing R R'
  have : AlgebraicGeometry.IsReduced (Sp R') := GlobalTheory.isReduced_of_smooth_of_isReduced π
  have : _root_.IsReduced R' := (affine_isReduced_iff (CommRingCat.of R')).1 this
  obtain ⟨o', ⟨m⟩⟩ := GlobalTheory.obj_pull E H D l _ _ (baseKA l) (baseKA l) (RingHom.id _) _ _ s (π ≫ s) π rfl rfl
    (by simp [spMap]) o
  obtain ⟨h₁, -, h₂⟩ := (GlobalTheory.heckeSets_pull E H D 𝔓 p i _ _ o.t o'.t π m.toSABMap o.proper).2 K
  obtain ⟨σ', hσ', hL'⟩ := h₂ _ _ σ hL
  obtain ⟨ρ, e₀⟩ := GlobalTheory.HkSetPull.exists_equiv m.cart (𝟙_ (Over (Sp R')))
  have tu : (toUnit (Over.mk ((𝟙_ (Over (Sp R'))).hom ≫ π))).left = π := by simp
  let v : C →* (𝟙_ (Over (Sp R')) ⟶ o'.t.G) := MonoidHom.mk' (fun c => ρ.symm (toUnit _ ≫ c.1)) fun c c' => by
    rw [← map_mul, ← MonObj.comp_mul]
    rfl
  have hv : ∀ c, (v c).left ≫ m.toSABMap.φ = π ≫ c.1.left := fun c => by
    change (ρ.symm (toUnit _ ≫ c.1)).left ≫ _ = _
    rw [← e₀, ρ.apply_symm_apply, Over.comp_left, tu]
  have hv' : ∀ (c : C) j, σ j = c → v c = σ' j := fun c j h =>
    Over.OverMorphism.ext (m.cart.1.hom_ext (by rw [hv, hσ', h]) ((Over.w _).trans (Over.w _).symm))
  refine ⟨R', inferInstance, π, o', m, hπ, hq, hasQuot_of_linearisation o' hD hA hL' (h₁ hH) C v e einj
    (fun c => hv' c _ (he c)) (fun j => ⟨⟨σ j, ?_⟩, hv' _ j rfl⟩) ?_⟩
  · change σ j ∈ (C : Set (𝟙_ (Over (Sp R)) ⟶ o.t.G))
    rw [hC]
    exact ⟨j, rfl⟩
  · exact hlin o'.t.G m.toSABMap.φ o'.t.PP.L v m.cart o'.t.PP.isLB (m.lin.imp fun _ h => h.1) hv
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_etale_hasHeckeQuotient_noetherian_domain : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (𝔓 : Ideal (𝓞 E)) (p i n : ℕ) (R : Type) [CommRing R] [IsNoetherianRing R] [IsDomain R] (s : Sp R ⟶ Sp (KA l)) (o : Ob D l s) (σ : Fin n → (𝟙_ (Over (Sp R)) ⟶ o.t.G)) (K : Set o.t.G.left) (q : Sp R), 1 ≤ D.p + D.q → admitted l 𝔓 p → Lists (p ^ 2) σ K → HeckeSet D o.t 𝔓 p i K → ∃ (R' : Type) (_ : CommRing R') (π : Sp R' ⟶ Sp R) (o' : Ob D l (π ≫ s)) (m : ObjMap o' o π), Etale π ∧ q ∈ Set.range π ∧ HasQuot o' p (m.toSABMap.φ ⁻¹' K) := by
  atlas_forward_decl GlobalTheory.exists_etale_hasQuot_of_lists
end
