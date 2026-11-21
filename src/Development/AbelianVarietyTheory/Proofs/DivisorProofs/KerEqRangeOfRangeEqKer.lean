import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneRanksFieldCharP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowFinrankCotangentLeFinrankFrobeniusKernelQuoti
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankRigidExtensionsEqHeightAndDimAddDualStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierDualHeightOneAdjoinPrimitiveEqTopStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppOneEqZeroOfKernelIdealOfCompEqPrimeSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapMapEqSelfOfInjectiveFiniteHopf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusKernelIdealEqKernelRelativeFrobenius

section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

noncomputable section

namespace GlobalTheory.PDiv

variable {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Bialgebra R A] [Bialgebra R B]

variable (R A) in

def restrZeroLeft : A ⊗[R] A →ₗ[R] A :=
  (TensorProduct.lid R A).toLinearMap ∘ₗ (counit (R := R) (A := A)).rTensor A

theorem restrZeroLeft_tmul (a b : A) : restrZeroLeft R A (a ⊗ₜ b) = counit (R := R) a • b := by
  simp [restrZeroLeft]

theorem restrZeroLeft_comul (a : A) : restrZeroLeft R A (comul a) = a := by
  simp [restrZeroLeft, Coalgebra.rTensor_counit_comul]

variable (R A) in

def restrZeroZero : A ⊗[R] (A ⊗[R] A) →ₗ[R] A :=
  (TensorProduct.lid R A).toLinearMap ∘ₗ TensorProduct.map (counit (R := R) (A := A))
    (restrZeroLeft R A)

theorem restrZeroZero_tmul (a : A) (t : A ⊗[R] A) :
    restrZeroZero R A (a ⊗ₜ t) = counit (R := R) a • restrZeroLeft R A t := by
  simp [restrZeroZero]

theorem restrZeroZero_assoc (u : A ⊗[R] A) (b : A) :
    restrZeroZero R A (TensorProduct.assoc R A A A (u ⊗ₜ b)) =
      counit (R := R) (restrZeroLeft R A u) • b := by
  induction u with
  | zero => simp
  | add x y hx hy => simp only [add_tmul, map_add, hx, hy, add_smul]
  | tmul x y =>
    rw [TensorProduct.assoc_tmul, restrZeroZero_tmul, restrZeroLeft_tmul, restrZeroLeft_tmul,
      map_smul, smul_eq_mul, mul_smul]

theorem restrZeroLeft_of_cobTwo_eq_zero {c : A ⊗[R] A} (hc : cobTwo R A c = 0) :
    restrZeroLeft R A c =
      algebraMap R A (TensorProduct.lid R R (TensorProduct.map (counit (R := R) (A := A))
        (counit (R := R) (A := A)) c)) := by
  have key : ∀ t : A ⊗[R] A, restrZeroZero R A (cobTwo R A t) = restrZeroLeft R A t -
      algebraMap R A (TensorProduct.lid R R (TensorProduct.map (counit (R := R) (A := A))
        (counit (R := R) (A := A)) t)) := fun t => by
    induction t with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]; abel
    | tmul a b =>
      rw [cobTwo_apply]
      simp only [map_sub, map_add, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, LinearMap.flip_apply,
        TensorProduct.mk_apply, restrZeroZero_assoc, restrZeroZero_tmul, restrZeroLeft_comul,
        restrZeroLeft_tmul, Bialgebra.counit_one, one_smul, TensorProduct.map_tmul,
        TensorProduct.lid_tmul, smul_eq_mul, Algebra.algebraMap_eq_smul_one, mul_smul]
      abel
  have := key c
  rw [hc, map_zero] at this
  exact (sub_eq_zero.1 this.symm)

end GlobalTheory.PDiv

namespace GlobalTheory.PDiv

variable {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Bialgebra R A] [Bialgebra R B]

theorem dUnit_mul'_map (f g : A →ₐc[R] B) (t : A ⊗[R] A) :
    dUnit R (LinearMap.mul' R B (TensorProduct.map (f : A →ₗ[R] B) (g : A →ₗ[R] B) t)) =
      cotMap g (dUnit R (restrZeroLeft R A t)) +
        cotMap f (dUnit R (restrZeroLeft R A (TensorProduct.comm R A A t))) := by
  induction t with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]; abel
  | tmul a b =>
    have e1 : dUnit R (counit (R := R) a • b) = counit (R := R) a • dUnit R b :=
      map_smul (AugCot.d _) _ _
    have e2 : dUnit R (counit (R := R) b • a) = counit (R := R) b • dUnit R a :=
      map_smul (AugCot.d _) _ _
    rw [TensorProduct.map_tmul, LinearMap.mul'_apply, TensorProduct.comm_tmul, restrZeroLeft_tmul,
      restrZeroLeft_tmul, e1, e2, map_smul, map_smul, cotMap_d, cotMap_d, dUnit, AugCot.d_mul]
    have c1 : counitAlgHom R B (f a) = counit (R := R) a := CoalgHomClass.counit_comp_apply f a
    have c2 : counitAlgHom R B (g b) = counit (R := R) b := CoalgHomClass.counit_comp_apply g b
    exact congrArg₂ (· + ·) (congrArg₂ (· • ·) c1 rfl) (congrArg₂ (· • ·) c2 rfl)

theorem dUnit_mul'_map_of_mem (f g : A →ₐc[R] B) {c : A ⊗[R] A} (hc : c ∈ symCocycles R A) :
    dUnit R (LinearMap.mul' R B (TensorProduct.map (f : A →ₗ[R] B) (g : A →ₗ[R] B) c)) = 0 := by
  obtain ⟨h1, h2⟩ := mem_symCocycles.1 hc
  rw [dUnit_mul'_map, h2, restrZeroLeft_of_cobTwo_eq_zero h1, dUnit, AugCot.d_algebraMap,
    map_zero, map_zero, zero_add]

end GlobalTheory.PDiv

namespace GlobalTheory.PDivGroup

variable {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] {G H : PDivGroup p R}

theorem rigExtMap_add (f g : G ⟶ H) : rigExtMap (f + g) = rigExtMap f + rigExtMap g := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨⟨c, w⟩, rfl⟩ := Submodule.mkQ_surjective _ x
  let B : G.funs := ⟨fun n => LinearMap.mul' R _ (TensorProduct.map (f.app n : H.A n →ₗ[R] G.A n)
      (g.app n : H.A n →ₗ[R] G.A n) (c.1 n)), fun n => by
    dsimp only
    rw [← (c.2 n).2]
    generalize c.1 (n + 1) = t
    induction t with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul x y => simp [res_app]⟩
  have hB : G.dFun B = 0 :=
    Subtype.ext (funext fun n => dUnit_mul'_map_of_mem (f.app n) (g.app n) (c.2 n).1)
  have hc : cocyclesMap (f + g) c = cocyclesMap f c + cocyclesMap g c + G.cob B :=
    Subtype.ext (funext fun n => T.bialgebraPullbackTwo_convMul_symmetricCocycle (f.app n) (g.app n) (c.1 n) (c.2 n).1)
  change G.rigMk (cocyclesMap (f + g) c, omegaMap G H (f + g) w) =
    G.rigMk (cocyclesMap f c, omegaMap G H f w) + G.rigMk (cocyclesMap g c, omegaMap G H g w)
  rw [← map_add, Prod.mk_add_mk, map_add (omegaMap G H) f g, LinearMap.add_apply, hc]
  refine (Submodule.Quotient.eq _).2 ⟨B, Prod.ext ?_ ?_⟩
  · show G.cob B = _
    simp
  · show G.dFun B = _
    rw [hB]
    simp

variable (G) in

theorem rigExtMap_natCast_smul_id (hp : (p : R) = 0) : rigExtMap ((p : ℤ_[p]) • 𝟙 G) = 0 := by
  let φ : (G ⟶ G) →+ (G.RigExt →ₗ[R] G.RigExt) :=
    AddMonoidHom.mk' (fun f => rigExtMap f) (fun f g => rigExtMap_add f g)
  have h : φ (p • 𝟙 G) = p • φ (𝟙 G) := map_nsmul φ p (𝟙 G)
  rw [← Nat.cast_smul_eq_nsmul ℤ_[p], ← Nat.cast_smul_eq_nsmul R, hp, zero_smul] at h
  exact h

theorem rigExtMap_add_and_natCast_smul_id : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R]
    (h : (p : R) = 0) (G H : PDivGroup p R),
    (∀ f g : G ⟶ H, rigExtMap (f + g) = rigExtMap f + rigExtMap g) ∧
      rigExtMap ((p : ℤ_[p]) • 𝟙 G) = 0 :=
  fun _ _ _ _ h G _ => ⟨rigExtMap_add, G.rigExtMap_natCast_smul_id h⟩

end GlobalTheory.PDivGroup
end
end

section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rigidifiedExtensionPullback_add_and_prime_smul_id : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (h : (p : R) = 0) (G H : PDivGroup p R), (∀ f g : G ⟶ H, rigExtMap (f + g) = rigExtMap f + rigExtMap g) ∧ rigExtMap ((p : ℤ_[p]) • 𝟙 G) = 0 := by
  first | exact @GlobalTheory.PDivGroup.rigExtMap_add_and_natCast_smul_id | exact GlobalTheory.PDivGroup.rigExtMap_add_and_natCast_smul_id | (intros; apply GlobalTheory.PDivGroup.rigExtMap_add_and_natCast_smul_id <;> assumption)
end

section
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.PDivGroup

theorem frobProj_frobTwist_app {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] (h : (p : R) = 0)
    (G : PDivGroup p R) (n : ℕ) (x : (frobTwist h G).A n) :
    ((frobProj h G).frobTwist h h).app n x = (frobProj h (frobTwist h G)).app n x := by
  induction x using frobTwist_induction h n with
  | h0 => simp only [map_zero]
  | h2 x y hx hy => simp only [map_add, hx, hy]
  | h1 r a =>
    rw [SemiBialgHom.smul_map, SemiBialgHom.smul_map, SemiHom.frobTwist_app_frobProj]

theorem pow_char_eq_zero_of_verschiebung (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R]
    (h : (p : R) = 0) (G : PDivGroup p R) (n : ℕ) (χ : CartierDual R ((frobTwist h G).A n))
    (hχ : ∀ a : G.A n, χ ((verschiebung h G).app n a) = 0) : χ ^ p = 0 := by
  refine CartierDual.ext_apply fun y => ?_
  induction y using frobTwist_induction h n with
  | h0 => simp only [map_zero]
  | h2 x y hx hy => rw [map_add, hx, hy, map_add]
  | h1 r a =>
    rw [map_smul, ← frobTwistDual_verschiebung h (G := frobTwist h G) n χ,
      ← SemiHom.app_verschiebung h h (frobProj h G), frobProj_frobTwist_app,
      frobTwistDual_frobProj, hχ, zero_pow (Fact.out : p.Prime).ne_zero, smul_zero]
    rfl

end GlobalTheory.PDivGroup
end

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pow_char_eq_zero_of_kills_verschiebung : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (h : (p : R) = 0) (G : PDivGroup p R) (n : ℕ) (χ : CartierDual R ((frobTwist h G).A n)), (∀ a : G.A n, χ ((verschiebung h G).app n a) = 0) → χ ^ p = 0 := by
  atlas_forward_decl GlobalTheory.PDivGroup.pow_char_eq_zero_of_verschiebung
end

section
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.PDiv

theorem exists_primitive_dUnit_eq : ∀ (p : ℕ) [Fact p.Prime] (K H : Type) [Field K] [CharP K p]
    [CommRing H] [HopfAlgebra K H] [IsCocomm K H] [Module.Finite K H],
    (∀ φ ∈ augIdeal K (CartierDual K H), φ ^ p = 0) →
    ∀ w : Cot K H, ∃ b : H, cobOne K H b = 0 ∧ dUnit K b = w := by
  intro p _ K H _ _ _ _ _ _ hnil w
  have hgen := GlobalTheory.T.cartierDual_height_one_adjoin_primitive_eq_top p K (CartierDual K H) hnil
  set e := CartierDual.bidual K H
  have hH : Algebra.adjoin K {b : H | cobOne K H b = 0} = ⊤ := by
    let f : CartierDual K (CartierDual K H) →ₐ[K] H :=
      ((e.symm : CartierDual K (CartierDual K H) →ₐc[K] H) : CartierDual K (CartierDual K H) →ₐ[K] H)
    have himg : f '' {φ | cobOne K (CartierDual K (CartierDual K H)) φ = 0} ⊆
        {b : H | cobOne K H b = 0} := by
      rintro _ ⟨φ, hφ, rfl⟩
      simp only [Set.mem_setOf_eq] at hφ ⊢
      show cobOne K H ((e.symm : CartierDual K (CartierDual K H) →ₐc[K] H) φ) = 0
      rw [← pullTwo_cobOne, hφ, map_zero]
    rw [eq_top_iff]
    intro x _
    refine Algebra.adjoin_mono himg ?_
    rw [Algebra.adjoin_image]
    refine ⟨e x, ?_, ?_⟩
    · rw [hgen]; trivial
    · exact e.symm_apply_apply x
  let P : Submodule K H := LinearMap.ker (cobOne K H)
  let S : Submodule K (Cot K H) := P.map (AugCot.d (counitAlgHom K H))
  have hS : ∀ a ∈ Algebra.adjoin K {b : H | cobOne K H b = 0}, dUnit K a ∈ S := by
    intro a ha
    induction ha using Algebra.adjoin_induction with
    | mem x hx => exact Submodule.mem_map_of_mem (p := P) hx
    | algebraMap r => rw [dUnit, AugCot.d_algebraMap]; exact S.zero_mem
    | add x y _ _ hx hy => rw [dUnit, map_add]; exact S.add_mem hx hy
    | mul x y _ _ hx hy =>
      rw [dUnit, AugCot.d_mul]
      exact S.add_mem (S.smul_mem _ hy) (S.smul_mem _ hx)
  obtain ⟨a, rfl⟩ := AugCot.d_surjective (counitAlgHom K H) w
  obtain ⟨b, hb, hbd⟩ := hS a (by rw [hH]; trivial)
  exact ⟨b, hb, hbd⟩

end GlobalTheory.PDiv
end

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_primitive_with_cotangent_of_dual_height_one : ∀ (p : ℕ) [Fact p.Prime] (K H : Type) [Field K] [CharP K p] [CommRing H] [HopfAlgebra K H] [IsCocomm K H] [Module.Finite K H], (∀ φ ∈ augIdeal K (CartierDual K H), φ ^ p = 0) → ∀ w : Cot K H, ∃ b : H, cobOne K H b = 0 ∧ dUnit K b = w := by
  atlas_forward_decl GlobalTheory.PDiv.exists_primitive_dUnit_eq
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.PDiv

theorem isHopfIdeal_kerIdeal {R A C : Type} [CommRing R] [CommRing A] [CommRing C]
    [HopfAlgebra R A] [HopfAlgebra R C] (f : C →ₐc[R] A) : (kerIdeal f).IsHopfIdeal R where
  counit_eq_zero x hx := by
    have hle : kerIdeal f ≤ augIdeal R A := by
      refine Ideal.map_le_iff_le_comap.mpr fun c hc => ?_
      have hc' : counit (R := R) c = 0 := by simpa using hc
      rw [Ideal.mem_comap, RingHom.mem_ker]
      simpa [CoalgHomClass.counit_comp_apply] using hc'
    simpa using hle hx
  map_mkQ_comul_eq_zero := by
    intro x hx
    let Q := A ⧸ kerIdeal f
    let q := Ideal.Quotient.mkₐ R (kerIdeal f)
    let Φ : A →ₐ[R] Q ⊗[R] Q := (Algebra.TensorProduct.map q q).comp (Bialgebra.comulAlgHom R A)
    have hqf : ∀ c : C, q (f c) = algebraMap R Q (counit (R := R) c) := by
      intro c
      have hmem : f (c - algebraMap R C (counit (R := R) c)) ∈ kerIdeal f := by
        refine Ideal.mem_map_of_mem (f : C →ₐ[R] A) ?_
        rw [RingHom.mem_ker]
        simp
      have h0 : q (f (c - algebraMap R C (counit (R := R) c))) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr hmem
      rw [map_sub, map_sub, AlgHomClass.commutes, AlgHomClass.commutes, sub_eq_zero] at h0
      exact h0
    have hg : q.toLinearMap ∘ₗ (f : C →ₗ[R] A) = Algebra.linearMap R Q ∘ₗ counit :=
      LinearMap.ext hqf
    have hΦ : kerIdeal f ≤ RingHom.ker Φ := by
      refine Ideal.map_le_iff_le_comap.mpr fun c hc => ?_
      have hc' : counit (R := R) c = 0 := by simpa using hc
      rw [Ideal.mem_comap, RingHom.mem_ker]
      change TensorProduct.map q.toLinearMap q.toLinearMap (comul (f c)) = 0
      rw [← CoalgHomClass.map_comp_comul_apply, ← LinearMap.comp_apply, ← TensorProduct.map_comp,
        hg]
      have hsplit : TensorProduct.map (Algebra.linearMap R Q ∘ₗ counit)
          (Algebra.linearMap R Q ∘ₗ counit) =
          TensorProduct.map (Algebra.linearMap R Q) (Algebra.linearMap R Q ∘ₗ counit) ∘ₗ
            LinearMap.rTensor C (counit (R := R) (A := C)) := by
        rw [LinearMap.rTensor, ← TensorProduct.map_comp, LinearMap.comp_id]
      rw [hsplit, LinearMap.comp_apply, Coalgebra.rTensor_counit_comul, TensorProduct.map_tmul]
      simp [hc']
    exact hΦ hx
  antipode_mem := by
    have h0 : ((1 : WithConv (A →ₐ[R] A)).ofConv).comp (f : C →ₐ[R] A) =
        (1 : WithConv (C →ₐ[R] A)).ofConv := by
      ext c
      simp [CoalgHomClass.counit_comp_apply]
    have h1 : WithConv.toConv ((HopfAlgebra.antipodeAlgHom R A).comp (f : C →ₐ[R] A)) *
        WithConv.toConv (f : C →ₐ[R] A) = 1 := by
      have := AlgHom.convMul_comp_bialgHom_distrib
        (WithConv.toConv (HopfAlgebra.antipodeAlgHom R A)) (WithConv.toConv (AlgHom.id R A)) f
      rw [AlgHom.antipode_id_cancel, h0] at this
      apply WithConv.ofConv_injective
      rw [this]
      rfl
    have h2 : (HopfAlgebra.antipodeAlgHom R A).comp (f : C →ₐ[R] A) =
        (f : C →ₐ[R] A).comp (HopfAlgebra.antipodeAlgHom R C) :=
      congrArg WithConv.ofConv (eq_inv_of_mul_eq_one_left h1)
    have hS : ∀ c : C, HopfAlgebra.antipode R (f c) = f (HopfAlgebra.antipode R c) := fun c => by
      simpa using DFunLike.congr_fun h2 c
    have hle : kerIdeal f ≤ Ideal.comap (HopfAlgebra.antipodeAlgHom R A) (kerIdeal f) := by
      refine Ideal.map_le_iff_le_comap.mpr fun c hc => ?_
      rw [Ideal.mem_comap, Ideal.mem_comap]
      have hc' : counit (R := R) c = 0 := by simpa using hc
      change HopfAlgebra.antipode R (f c) ∈ kerIdeal f
      rw [hS]
      refine Ideal.mem_map_of_mem (f : C →ₐ[R] A) ?_
      rw [RingHom.mem_ker]
      simpa using hc'
    intro x hx
    exact hle hx

theorem isCocomm_of_surjective {R A B : Type} [CommRing R] [CommRing A] [CommRing B]
    [Bialgebra R A] [Bialgebra R B] [IsCocomm R A] (f : A →ₐc[R] B)
    (hf : Function.Surjective f) : IsCocomm R B := by
    refine ⟨LinearMap.ext fun b => ?_⟩
    obtain ⟨a, rfl⟩ := hf b
    have h1 := CoalgHomClass.map_comp_comul_apply f a
    have h2 := TensorProduct.map_comm (f : A →ₗ[R] B) (f : A →ₗ[R] B) (comul (R := R) a)
    have h3 := Coalgebra.comm_comul R a
    show TensorProduct.comm R B B (comul (f a)) = comul (f a)
    rw [← h1, ← h2, h3]

end GlobalTheory.PDiv

namespace GlobalTheory.PDivGroup

theorem exists_cobOne_relFrob_eq_zero_dUnit_eq (p : ℕ) [Fact p.Prime] (K : Type) [Field K]
    (h : (p : K) = 0) (G : PDivGroup p K) (w : Cot K ((frobTwist h G).A 1)) :
    ∃ (β : (frobTwist h G).A 1) (w' : Cot K (G.A 1)),
      cobOne K (G.A 1) ((relFrob h G).app 1 β) = 0 ∧
        dUnit K β = w + cotMap ((verschiebung h G).app 1) w' := by
    haveI : CharP K p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr h
    set V := (verschiebung h G).app 1 with hV
    set F := (relFrob h G).app 1 with hF
    set J : Ideal ((frobTwist h G).A 1) := kerIdeal V with hJdef
    haveI hJ : J.IsHopfIdeal K := GlobalTheory.PDiv.isHopfIdeal_kerIdeal V
    let π : (frobTwist h G).A 1 →ₐc[K] (frobTwist h G).A 1 ⧸ J := Bialgebra.Quotient.mkBialgHom J
    have hπa : ∀ a, π a = Ideal.Quotient.mk J a := fun a => rfl
    have hπ : Function.Surjective π := Ideal.Quotient.mk_surjective
    haveI : IsCocomm K ((frobTwist h G).A 1 ⧸ J) := GlobalTheory.PDiv.isCocomm_of_surjective π hπ
    haveI : Module.Finite K ((frobTwist h G).A 1 ⧸ J) :=
      Module.Finite.of_surjective (π : (frobTwist h G).A 1 →ₗ[K] _) hπ
    have hJaug : ∀ x ∈ J, counit (R := K) x = 0 := fun x hx =>
      Submodule.IsCoideal.counit_eq_zero (I := J.restrictScalars K) hx

    have hπV : ∀ a : G.A 1, π (V a) = algebraMap K _ (counit (R := K) a) := by
      intro a
      have hmem : V (a - algebraMap K (G.A 1) (counit (R := K) a)) ∈ J := by
        refine Ideal.mem_map_of_mem (V : G.A 1 →ₐ[K] (frobTwist h G).A 1) ?_
        rw [RingHom.mem_ker]
        simp
      have h0 : π (V (a - algebraMap K (G.A 1) (counit (R := K) a))) = 0 := by
        rw [hπa]; exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem
      rw [map_sub, map_sub, AlgHomClass.commutes, AlgHomClass.commutes, sub_eq_zero] at h0
      exact h0

    have hdual : ∀ φ ∈ augIdeal K (CartierDual K ((frobTwist h G).A 1 ⧸ J)), φ ^ p = 0 := by
      intro φ hφ
      have hφ1 : φ 1 = 0 := by
        have : counit (R := K) φ = 0 := by simpa using hφ
        simpa using this
      have hχ : (CartierDual.map π φ) ^ p = 0 := by
        apply GlobalTheory.T.pow_char_eq_zero_of_kills_verschiebung p K h G 1
        intro a
        rw [CartierDual.map_apply, hπV, Algebra.algebraMap_eq_smul_one]
        change φ.ofConv (counit (R := K) a • 1) = 0
        rw [map_smul]
        change counit (R := K) a • φ 1 = 0
        rw [hφ1, smul_zero]
      have hχ' : CartierDual.map π (φ ^ p) = 0 := by rw [map_pow]; exact hχ
      apply CartierDual.ext_apply
      intro x
      obtain ⟨a, rfl⟩ := hπ x
      have := congrArg (fun χ : CartierDual K ((frobTwist h G).A 1) => χ a) hχ'
      simp only [CartierDual.map_apply] at this
      simpa using this
    obtain ⟨b, hb0, hbw⟩ := GlobalTheory.T.exists_primitive_with_cotangent_of_dual_height_one p K ((frobTwist h G).A 1 ⧸ J) hdual (cotMap π w)
    obtain ⟨β, rfl⟩ := hπ b

    have hker : RingHom.ker π ≤ RingHom.ker F := by
      intro a ha
      have haJ : a ∈ J := by
        rw [RingHom.mem_ker, hπa] at ha
        exact Ideal.Quotient.eq_zero_iff_mem.mp ha
      rw [RingHom.mem_ker]
      exact GlobalTheory.T.app_one_eq_zero_of_kernel_ideal_of_comp_eq_prime_smul p K (frobTwist h G) G (verschiebung h G) (relFrob h G)
        (relFrob_comp_verschiebung h G) a haJ
    have hFβ : F β = liftSurj π hπ F hker (π β) := (liftSurj_apply π hπ F hker β).symm

    have hrange : ∀ x : Cot K ((frobTwist h G).A 1), cotMap π x = 0 →
        x ∈ LinearMap.range (cotMap V) := by
      let Rg := LinearMap.range (cotMap V)
      let D₀ : (frobTwist h G).A 1 →ₗ[K] Cot K ((frobTwist h G).A 1) ⧸ Rg :=
        Rg.mkQ ∘ₗ AugCot.d (counitAlgHom K ((frobTwist h G).A 1))
      have hD₀ : ∀ a, D₀ a = Rg.mkQ (dUnit K a) := fun a => rfl
      have hD₀mul : ∀ a b, D₀ (a * b) =
          counit (R := K) a • D₀ b + counit (R := K) b • D₀ a := by
        intro a b
        rw [hD₀, hD₀, hD₀]
        change Rg.mkQ (AugCot.d _ (a * b)) =
          counit (R := K) a • Rg.mkQ (AugCot.d _ b) + counit (R := K) b • Rg.mkQ (AugCot.d _ a)
        rw [AugCot.d_mul]
        simp
      have hJD : ∀ x ∈ J, D₀ x = 0 := by
        intro x hx
        refine Submodule.span_induction (p := fun x _ => D₀ x = 0) ?_ ?_ ?_ ?_ hx
        · rintro _ ⟨c, hc, rfl⟩
          rw [hD₀, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
          exact ⟨dUnit K c, cotMap_d V c⟩
        · exact map_zero D₀
        · intro u v _ _ hu hv
          rw [map_add, hu, hv, add_zero]
        · intro a u hu hu0
          rw [smul_eq_mul, hD₀mul, hu0, hJaug u hu, zero_smul, smul_zero, add_zero]
      let D : ((frobTwist h G).A 1 ⧸ J) →ₗ[K] Cot K ((frobTwist h G).A 1) ⧸ Rg :=
        (J.restrictScalars K).liftQ D₀ (fun x hx => hJD x hx) ∘ₗ
          (Submodule.Quotient.restrictScalarsEquiv K J).symm.toLinearMap
      have hD : ∀ a, D (Ideal.Quotient.mk J a) = D₀ a := fun a => rfl
      have hDmul : ∀ u v, D (u * v) = counit (R := K) u • D v + counit (R := K) v • D u := by
        intro u v
        obtain ⟨a, rfl⟩ := hπ u
        obtain ⟨b, rfl⟩ := hπ v
        rw [← map_mul, hπa, hπa, hπa, hD, hD, hD, hD₀mul]
        rfl
      let L := AugCot.lift (counitAlgHom K ((frobTwist h G).A 1 ⧸ J)) D
        (fun u v => by simpa using hDmul u v)
      have hL : L ∘ₗ cotMap π = Rg.mkQ := by
        apply AugCot.hom_ext
        intro a
        rw [LinearMap.comp_apply]
        change L (cotMap π (dUnit K a)) = Rg.mkQ (dUnit K a)
        rw [cotMap_d]
        change L (AugCot.d _ (π a)) = _
        rw [AugCot.lift_d, hπa, hD, hD₀]
      intro x hx
      have := congrArg (fun g => g x) hL
      simp only [LinearMap.comp_apply, hx, map_zero] at this
      exact (Submodule.Quotient.mk_eq_zero Rg).mp this.symm
    obtain ⟨w', hw'⟩ := hrange (dUnit K β - w) (by rw [map_sub, cotMap_d, hbw, sub_self])
    refine ⟨β, w', ?_, ?_⟩
    · rw [hFβ, ← pullTwo_cobOne, hb0, map_zero]
    · rw [hw']
      abel

end GlobalTheory.PDivGroup
end
end

section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_additive_frobeniusPullback_cotangent_mod_verschiebung : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (h : (p : K) = 0) (G : PDivGroup p K), ∀ w : Cot K ((frobTwist h G).A 1), ∃ (β : (frobTwist h G).A 1) (w' : Cot K (G.A 1)), cobOne K (G.A 1) ((relFrob h G).app 1 β) = 0 ∧ dUnit K β = w + cotMap ((verschiebung h G).app 1) w' := by
  first | exact @GlobalTheory.PDivGroup.exists_cobOne_relFrob_eq_zero_dUnit_eq | exact GlobalTheory.PDivGroup.exists_cobOne_relFrob_eq_zero_dUnit_eq | (intros; apply GlobalTheory.PDivGroup.exists_cobOne_relFrob_eq_zero_dUnit_eq <;> assumption)
end

section
section
set_option autoImplicit false

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.PDivGroup

theorem mulP_mem_kerIdeal_comp_of_app_eq_zero (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R]
    (G H : PDivGroup p R) (f : G ⟶ H) (g : H ⟶ G) (hfg : f ≫ g = (p : ℤ_[p]) • 𝟙 G)
    (a : G.A 1) (ha : g.app 1 a = 0) :
    G.mulP 1 a ∈ kerIdeal ((G.mulP 1).comp (f.app 1)) := by
  set K := kerIdeal ((G.mulP 1).comp (f.app 1)) with hK
  let x := Ideal.Quotient.mkₐ R K
  have hx := (kerIdeal_le_ker_iff ((G.mulP 1).comp (f.app 1)) x).1
    fun c hc => Ideal.Quotient.eq_zero_iff_mem.2 hc
  let y := x.comp (f.app 2 : H.A 2 →ₐ[R] G.A 2)
  have hy : torsionIdeal R (H.A 2) p ≤ RingHom.ker y :=
    (kerIdeal_le_ker_iff _ y).2 fun z => by
      have e : f.app 2 (mulBy R _ p z) = G.mulP 1 (f.app 1 (H.res 1 z)) := by
        rw [map_mulBy, ← PDivGroup.res_app, mulP_res]
      have := hx (H.res 1 z)
      rw [CoalgHomClass.counit_comp_apply] at this
      exact (congrArg x e).trans this
  obtain ⟨b, rfl⟩ := G.res_surjective 1 a
  rw [← PDivGroup.res_app] at ha
  have hb : g.app 2 b ∈ torsionIdeal R (H.A 2) p := by
    have : g.app 2 b ∈ torsionIdeal R (H.A 2) (p ^ 1) := by
      rw [← H.ker_res 1]
      exact ha
    rwa [pow_one] at this
  have h1 : x (f.app 2 (g.app 2 b)) = 0 := hy hb
  have e2 : f.app 2 (g.app 2 b) = mulBy R _ p b := by
    have := congrArg (fun φ : G ⟶ G => φ.app 2 b) hfg
    simp only [comp_app, natCast_smul_id_app] at this
    exact this
  rw [e2] at h1
  rw [mulP_res]
  exact Ideal.Quotient.eq_zero_iff_mem.1 h1

end GlobalTheory.PDivGroup

open GlobalTheory.PDivGroup in

theorem GlobalTheory.PDivGroup.mem_kerIdeal_of_app_eq_zero : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K]
    (G H : PDivGroup p K) (f : G ⟶ H) (g : H ⟶ G), f ≫ g = (p : ℤ_[p]) • 𝟙 G →
    g ≫ f = (p : ℤ_[p]) • 𝟙 H → ∀ a : G.A 1, g.app 1 a = 0 → a ∈ kerIdeal (f.app 1) := by
  intro p _ K _ G H f g hfg _ a ha
  have hmulP : Function.Injective (G.mulP 1) := fun a b e => by
    refine CartierDual.eq_of_forall_apply (R := K) fun φ => ?_
    obtain ⟨ψ, rfl⟩ := G.dual_mulP_surjective 1 φ
    change ψ.ofConv (G.mulP 1 a) = ψ.ofConv (G.mulP 1 b)
    rw [e]
  have h1 := mulP_mem_kerIdeal_comp_of_app_eq_zero p K G H f g hfg a ha
  rw [kerIdeal_comp] at h1
  rw [← GlobalTheory.PDiv.comap_map_eq_self_of_hopf_injective K _ _ (G.mulP 1) hmulP (kerIdeal (f.app 1))]
  exact h1
end

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_kernel_ideal_of_app_eq_zero_field : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (G H : PDivGroup p K) (f : G ⟶ H) (g : H ⟶ G), f ≫ g = (p : ℤ_[p]) • 𝟙 G → g ≫ f = (p : ℤ_[p]) • 𝟙 H → ∀ a : G.A 1, g.app 1 a = 0 → a ∈ kerIdeal (f.app 1) := by
  atlas_forward_decl GlobalTheory.PDivGroup.mem_kerIdeal_of_app_eq_zero
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.PDivGroup

theorem range_rigOfOmega_le_range_rigExtMap_verschiebung :
    ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (h : (p : K) = 0) (G : PDivGroup p K),
      LinearMap.range (frobTwist h G).rigOfOmega ≤
        LinearMap.range (rigExtMap (verschiebung h G)) := by
  intro p _ K _ h G
  rintro _ ⟨w, rfl⟩
  obtain ⟨β, w', hβ, hd⟩ := GlobalTheory.T.exists_additive_frobeniusPullback_cotangent_mod_verschiebung p K h G (-(w.1 1))
  obtain ⟨-, c, B₀, -, hB₀, -, hB₀'⟩ := exists_of_cobOne_eq_zero hβ
  obtain ⟨B, hB⟩ : cocyclesMap (verschiebung h G) c ∈ LinearMap.range (frobTwist h G).cob :=
    (Submodule.Quotient.mk_eq_zero _).1
      (LinearMap.congr_fun (vecExtMap_verschiebung h G) (Submodule.Quotient.mk c))
  have h1 : funsMap (relFrob h G) B - B₀ = 0 := G.eq_zero_of_cob_eq_zero h (by
    rw [map_sub, ← cocyclesMap_cob, hB, hB₀, ← relFrob_comp_verschiebung h G, sub_eq_zero]
    exact Subtype.ext (funext fun _ => (pullTwo_comp _ _ _).symm))
  have h2 : (relFrob h G).app 1 (B.1 1 - β) = 0 := by
    rw [map_sub, ← hB₀']
    exact congrArg (fun z : G.funs => z.1 1) h1
  obtain ⟨w'', hw''⟩ := dUnit_mem_range_of_mem_kerIdeal _
    (GlobalTheory.T.mem_kernel_ideal_of_app_eq_zero_field p K _ _ (verschiebung h G) (relFrob h G) (verschiebung_comp_relFrob h G)
      (relFrob_comp_verschiebung h G) _ h2)
  obtain ⟨u, hu⟩ := G.omegaLevel_surjective 1 (w' + w'')
  have h3 : (frobTwist h G).dFun B = omegaMap _ _ (verschiebung h G) u - w :=
    ((frobTwist h G).omegaLevel_one_bijective h).1 (by
      rw [map_sub, omegaLevel_apply, omegaLevel_apply, omegaLevel_apply, omegaMap_val,
        ← omegaLevel_apply, ← omegaLevel_apply _ _ u, hu, map_add, hw'']
      change dUnit K (B.1 1) = _
      rw [dUnit, dUnit, map_sub, ← dUnit, ← dUnit, hd]
      abel)
  refine ⟨G.rigMk (c, u), ?_⟩
  rw [rigExtMap_mk]
  refine (Submodule.Quotient.eq _).2 ⟨B, Prod.ext ?_ ?_⟩
  · exact hB.trans (sub_zero _).symm
  · exact h3

end GlobalTheory.PDivGroup
end
end

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.range_rigOfOmega_le_range_rigExtMap_verschiebung' : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (h : (p : K) = 0) (G : PDivGroup p K), LinearMap.range (frobTwist h G).rigOfOmega ≤ LinearMap.range (rigExtMap (verschiebung h G)) := by
  atlas_forward_decl GlobalTheory.PDivGroup.range_rigOfOmega_le_range_rigExtMap_verschiebung
end

section
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PDiv.HeightOnePrim

theorem apply_eq_zero_of_mem_sq {K H : Type} [Field K] [CommRing H] [HopfAlgebra K H]
    [IsCocomm K H] [Module.Finite K H] {φ : CartierDual K H} (hφ : cobOne K (CartierDual K H) φ = 0) {b : H}
    (hb : b ∈ augIdeal K H ^ 2) : φ b = 0 := by
  have hp := isPrimitiveElem_of_mem_ker (R := K) (A := CartierDual K H) (b := φ) hφ
  have hmul : ∀ x y : H, φ (x * y) = φ x * counit (R := K) y + counit (R := K) x * φ y := by
    intro x y
    rw [← CartierDual.pair_comul_tmul, show comul φ = _ from hp, map_add, LinearMap.add_apply,
      CartierDual.pair_tmul_tmul, CartierDual.pair_tmul_tmul, CartierDual.one_apply,
      CartierDual.one_apply]
  rw [pow_two] at hb
  refine Submodule.mul_induction_on hb (fun x hx y hy => ?_) (fun x y hx hy => ?_)
  · have hx' : counit (R := K) x = 0 := hx
    have hy' : counit (R := K) y = 0 := hy
    rw [hmul, hx', hy', mul_zero, zero_mul, add_zero]
  · rw [map_add, hx, hy, add_zero]

theorem eq_zero_of_cobOne_eq_zero_of_dUnit_eq_zero : ∀ (p : ℕ) [Fact p.Prime] (K H : Type) [Field K] [CharP K p] [CommRing H]
    [HopfAlgebra K H] [IsCocomm K H] [Module.Finite K H], (∀ a ∈ augIdeal K H, a ^ p = 0) →
    ∀ b : H, cobOne K H b = 0 → dUnit K b = 0 → b = 0 := by
  intro p _ K H _ _ _ _ _ _ hpow b hb hd
  have hcb : counit (R := K) b = 0 := (mulBy_of_cobOne_eq_zero hb 0).2
  have hsq : b ∈ augIdeal K H ^ 2 := by
    have := (AugCot.d_eq_zero_iff (counitAlgHom K H) b).1 hd
    simpa [hcb] using this
  have hgen := GlobalTheory.T.cartierDual_height_one_adjoin_primitive_eq_top p K H hpow
  have hall : ∀ φ : CartierDual K H, φ b = 0 := by
    intro φ
    have hφ : φ ∈ Algebra.adjoin K {φ : CartierDual K H | cobOne K (CartierDual K H) φ = 0} := by
      rw [hgen]; trivial
    induction hφ using Algebra.adjoin_induction with
    | mem x hx => exact apply_eq_zero_of_mem_sq hx hsq
    | algebraMap r =>
      rw [Algebra.algebraMap_eq_smul_one]
      change r • (1 : CartierDual K H) b = 0
      rw [CartierDual.one_apply, hcb, smul_zero]
    | add x y _ _ hx hy => rw [WithConv.ofConv_add, LinearMap.add_apply, hx, hy, add_zero]
    | mul x y _ _ hx hy =>
      have := evalAt_mul (R := K) (A := H) ⟨b, hb⟩ x y
      simp only [CartierDual.evalAt_apply] at this
      rw [this, hx, hy, smul_zero, smul_zero, add_zero]
  exact CartierDual.eq_of_forall_apply (R := K) fun φ => by rw [hall φ, map_zero]

end GlobalTheory.PDiv.HeightOnePrim
end
end

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hopf_height_one_primitive_eq_zero_of_zero_differential : ∀ (p : ℕ) [Fact p.Prime] (K H : Type) [Field K] [CharP K p] [CommRing H] [HopfAlgebra K H] [IsCocomm K H] [Module.Finite K H], (∀ a ∈ augIdeal K H, a ^ p = 0) → ∀ b : H, cobOne K H b = 0 → dUnit K b = 0 → b = 0 := by
  atlas_forward_decl GlobalTheory.PDiv.HeightOnePrim.eq_zero_of_cobOne_eq_zero_of_dUnit_eq_zero
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.PDiv.FrobKerPrim

theorem mem_frobKerIdeal_of_cobOne (p : ℕ) [Fact p.Prime] (K H : Type) [Field K] [CharP K p]
    [CommRing H] [HopfAlgebra K H] [IsCocomm K H] [Module.Finite K H] (b : H)
    (_hb : counit (R := K) b = 0) (hd : dUnit K b = 0)
    (hc : Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K (frobKerIdeal p K H))
      (Ideal.Quotient.mkₐ K (frobKerIdeal p K H)) (cobOne K H b) = 0) :
    b ∈ frobKerIdeal p K H := by
  haveI := FrobKerOrder.isHopfIdeal p K H
  set J := frobKerIdeal p K H with hJ
  let π : H →ₐc[K] H ⧸ J := Bialgebra.Quotient.mkBialgHom J
  have hπ : Function.Surjective π := Ideal.Quotient.mk_surjective
  haveI : IsCocomm K (H ⧸ J) := by
    constructor
    refine LinearMap.ext fun y => ?_
    obtain ⟨x, rfl⟩ := hπ y
    have h1 := pullTwo_comul π x
    simp only [LinearMap.comp_apply]
    rw [← h1]
    simp only [pullbackTwo]
    have h2 := TensorProduct.map_comm (π : H →ₗ[K] H ⧸ J) (π : H →ₗ[K] H ⧸ J) (comul x)
    rw [comm_comul] at h2
    exact h2.symm
  have hpow : ∀ a ∈ augIdeal K (H ⧸ J), a ^ p = 0 := by
    intro a ha
    obtain ⟨x, rfl⟩ := hπ a
    have hx : x ∈ augIdeal K H := ha
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (pow_mem_frobKerIdeal hx)
  have hc' : cobOne K (H ⧸ J) (π b) = 0 := by
    rw [← pullTwo_cobOne]
    exact hc
  have hd' : dUnit K (π b) = 0 := by
    rw [← cotMap_d, hd, map_zero]
  have h0 := GlobalTheory.T.hopf_height_one_primitive_eq_zero_of_zero_differential p K (H ⧸ J) hpow (π b) hc' hd'
  exact Ideal.Quotient.eq_zero_iff_mem.1 h0

end GlobalTheory.PDiv.FrobKerPrim
end
end

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_frobeniusKernelIdeal_of_zero_differential : ∀ (p : ℕ) [Fact p.Prime] (K H : Type) [Field K] [CharP K p] [CommRing H] [HopfAlgebra K H] [IsCocomm K H] [Module.Finite K H], ∀ b : H, counit (R := K) b = 0 → dUnit K b = 0 → Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K (frobKerIdeal p K H)) (Ideal.Quotient.mkₐ K (frobKerIdeal p K H)) (cobOne K H b) = 0 → b ∈ frobKerIdeal p K H := by
  atlas_forward_decl GlobalTheory.PDiv.FrobKerPrim.mem_frobKerIdeal_of_cobOne
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.PDiv.FrobRigKer

variable {O A B : Type} [CommRing O] [CommRing A] [CommRing B] [Bialgebra O A] [Bialgebra O B]

variable (O A) in

def evalZeroTwo : A ⊗[O] A →ₗ[O] O :=
  (TensorProduct.lid O O).toLinearMap ∘ₗ TensorProduct.map (counit (R := O)) (counit (R := O))

@[simp] theorem evalZeroTwo_tmul (a b : A) :
    evalZeroTwo O A (a ⊗ₜ b) = counit (R := O) a * counit (R := O) b := by
  simp [evalZeroTwo]

theorem evalZeroTwo_pullTwo (f : A →ₐc[O] B) (c : A ⊗[O] A) :
    evalZeroTwo O B (pullbackTwo f c) = evalZeroTwo O A c := by
  induction c using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [pullbackTwo, evalZeroTwo_tmul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]

theorem evalZeroTwo_comul (b : A) : evalZeroTwo O A (comul b) = counit (R := O) b := by
  have key : TensorProduct.map (counit (R := O)) (counit (R := O)) (comul (R := O) b) =
      LinearMap.lTensor O (counit (R := O)) (LinearMap.rTensor A (counit (R := O)) (comul b)) := by
    rw [← LinearMap.lTensor_comp_rTensor, LinearMap.comp_apply]
  show TensorProduct.lid O O (TensorProduct.map (counit (R := O)) (counit (R := O)) (comul b)) = _
  rw [key, Coalgebra.rTensor_counit_comul, LinearMap.lTensor_tmul, TensorProduct.lid_tmul, one_smul]

theorem evalZeroTwo_cobOne (b : A) : evalZeroTwo O A (cobOne O A b) = - counit (R := O) b := by
  rw [cobOne_apply, map_sub, map_sub, evalZeroTwo_comul, evalZeroTwo_tmul, evalZeroTwo_tmul,
    Bialgebra.counit_one]
  ring

theorem mk_kerIdeal_apply (f : A →ₐc[O] B) (a : A) :
    Ideal.Quotient.mkₐ O (kerIdeal f) (f a) = counit (R := O) a • 1 := by
  have hmem : a - algebraMap O A (counit (R := O) a) ∈ augIdeal O A := by
    simp [RingHom.mem_ker]
  have himg := Ideal.mem_map_of_mem (f : A →ₐ[O] B) hmem
  have e : (f : A →ₐ[O] B) (algebraMap O A (counit (R := O) a)) = algebraMap O B (counit (R := O) a) :=
    AlgHom.commutes _ _
  rw [map_sub, e] at himg
  rw [Algebra.smul_def, mul_one, ← AlgHom.commutes (Ideal.Quotient.mkₐ O (kerIdeal f)),
    Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq]
  exact himg

theorem map_mk_pullTwo (f : A →ₐc[O] B) (c : A ⊗[O] A) :
    Algebra.TensorProduct.map (Ideal.Quotient.mkₐ O (kerIdeal f)) (Ideal.Quotient.mkₐ O (kerIdeal f))
      (pullbackTwo f c) = evalZeroTwo O A c • 1 := by
  induction c using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    simp only [pullbackTwo, TensorProduct.map_tmul, BialgHom.coe_toLinearMap,
      Algebra.TensorProduct.map_tmul, mk_kerIdeal_apply, evalZeroTwo_tmul,
      Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul]
    rw [mul_comm]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, add_smul]

theorem map_mk_cobOne_eq_zero (f : A →ₐc[O] B) {c : A ⊗[O] A} {b : B}
    (hb : counit (R := O) b = 0) (hc : cobOne O B b = pullbackTwo f c) :
    Algebra.TensorProduct.map (Ideal.Quotient.mkₐ O (kerIdeal f)) (Ideal.Quotient.mkₐ O (kerIdeal f))
      (cobOne O B b) = 0 := by
  rw [hc, map_mk_pullTwo, ← evalZeroTwo_pullTwo f c, ← hc, evalZeroTwo_cobOne, hb, neg_zero,
    zero_smul]

def oneFun {p : ℕ} (G : PDivGroup p O) : G.funs := ⟨fun _ => 1, fun _ => map_one _⟩

theorem funsMap_oneFun {p : ℕ} {G H : PDivGroup p O} (f : G ⟶ H) :
    funsMap f (oneFun H) = oneFun G :=
  Subtype.ext (funext fun n => map_one (f.app n))

theorem dUnit_one : dUnit O (1 : A) = 0 := by
  simp [dUnit]

end GlobalTheory.PDiv.FrobRigKer

namespace GlobalTheory.PDivGroup

open GlobalTheory.PDiv.FrobRigKer

theorem ker_rigExtMap_relFrob_le_range_rigOfOmega (p : ℕ) [Fact p.Prime] (K : Type) [Field K]
    (h : (p : K) = 0) (G : PDivGroup p K) :
    LinearMap.ker (rigExtMap (relFrob h G)) ≤ LinearMap.range (frobTwist h G).rigOfOmega := by
  have : CharP K p := (CharP.charP_iff_prime_eq_zero (Fact.out)).2 h
  intro x hx
  rw [LinearMap.mem_ker] at hx
  obtain ⟨⟨c, w⟩, rfl⟩ : ∃ z, (frobTwist h G).rigMk z = x := Submodule.mkQ_surjective _ x
  rw [rigExtMap_mk] at hx
  obtain ⟨B, hB⟩ := (Submodule.Quotient.mk_eq_zero _).1 hx
  have hB1 : G.cob B = cocyclesMap (relFrob h G) c := congrArg Prod.fst hB
  have hB2 : G.dFun B = G.omegaMap _ (relFrob h G) w := congrArg Prod.snd hB
  set t : K := counit (R := K) (B.1 1) with ht
  set B₁ : G.funs := B - t • oneFun G with hB₁
  set c₁ : (frobTwist h G).cocycles := c - t • (frobTwist h G).cob (oneFun (frobTwist h G))
    with hc₁def
  have hc₁ : G.cob B₁ = cocyclesMap (relFrob h G) c₁ := by
    simp only [hB₁, hc₁def, map_sub, map_smul, hB1, cocyclesMap_cob, funsMap_oneFun]
  have hb0 : counit (R := K) (B₁.1 1) = 0 := by
    show counit (R := K) (B.1 1 - t • (1 : G.A 1)) = 0
    rw [map_sub, map_smul, Bialgebra.counit_one, smul_eq_mul, mul_one, ht, sub_self]
  have hbd : dUnit K (B₁.1 1) = 0 := by
    have e1 : G.dFun B = 0 := by rw [hB2, omegaMap_relFrob, LinearMap.zero_apply]
    have e2 : G.dFun (oneFun G) = 0 := Subtype.ext (funext fun n => dUnit_one)
    have e : G.dFun B₁ = 0 := by rw [hB₁, map_sub, map_smul, e1, e2, smul_zero, sub_zero]
    exact congrArg (fun z : G.omega => z.1 1) e
  have hcob : cobOne K (G.A 1) (B₁.1 1) = pullbackTwo ((relFrob h G).app 1) (c₁.1 1) :=
    congrArg (fun z : G.cocycles => z.1 1) hc₁
  have hker := GlobalTheory.T.frobeniusKernelIdeal_eq_kernel_relativeFrobenius p K h G 1
  have hmem : B₁.1 1 ∈ frobKerIdeal p K (G.A 1) := by
    refine GlobalTheory.T.mem_frobeniusKernelIdeal_of_zero_differential p K (G.A 1) _ hb0 hbd ?_
    rw [hker]
    exact map_mk_cobOne_eq_zero ((relFrob h G).app 1) hb0 hcob
  rw [hker] at hmem
  have hV : (verschiebung h G).app 1 (B₁.1 1) = 0 :=
    GlobalTheory.T.app_one_eq_zero_of_kernel_ideal_of_comp_eq_prime_smul p K G (frobTwist h G) (relFrob h G) (verschiebung h G)
      (verschiebung_comp_relFrob h G) _ hmem
  have hcomp : cocyclesMap (verschiebung h G) (cocyclesMap (relFrob h G) c₁) =
      cocyclesMap (verschiebung h G ≫ relFrob h G) c₁ :=
    Subtype.ext (funext fun n => (pullTwo_comp _ _ _).symm)
  obtain ⟨B', hB'⟩ : c₁ ∈ LinearMap.range (frobTwist h G).cob := by
    refine GlobalTheory.T.pDivCocycle_mem_range_cob_of_pullback_mulP (frobTwist h G) c₁ (funsMap (verschiebung h G) B₁) ?_ hV
    rw [← cocyclesMap_cob, hc₁, hcomp, verschiebung_comp_relFrob]
  set B₀ : (frobTwist h G).funs := B' + t • oneFun (frobTwist h G) with hB₀
  have hc0 : (frobTwist h G).cob B₀ = c := by
    rw [hB₀, map_add, map_smul, hB', hc₁def, sub_add_cancel]
  refine ⟨w - (frobTwist h G).dFun B₀, ?_⟩
  show Submodule.Quotient.mk ((0 : (frobTwist h G).cocycles), w - (frobTwist h G).dFun B₀) =
    Submodule.Quotient.mk (c, w)
  refine ((Submodule.Quotient.eq
    (LinearMap.range ((frobTwist h G).cob.prod (frobTwist h G).dFun))).2
    (LinearMap.mem_range.2 ⟨B₀, Prod.ext ?_ ?_⟩)).symm
  · show (frobTwist h G).cob B₀ = c - 0
    rw [sub_zero]
    exact hc0
  · show (frobTwist h G).dFun B₀ = w - (w - (frobTwist h G).dFun B₀)
    exact (sub_sub_cancel w _).symm

end GlobalTheory.PDivGroup
end
end

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ker_rigExtMap_relFrob_le_range_rigOfOmega' : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (h : (p : K) = 0) (G : PDivGroup p K), LinearMap.ker (rigExtMap (relFrob h G)) ≤ LinearMap.range (frobTwist h G).rigOfOmega := by
  atlas_forward_decl GlobalTheory.PDivGroup.ker_rigExtMap_relFrob_le_range_rigOfOmega
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct

namespace GlobalTheory

namespace PDivGroup

open PDiv

theorem ker_eq_range_of_range_eq_ker {K V W : Type} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (_ : Module.Finite K V) (_ : Module.Finite K W) (f : V →ₗ[K] W)
    (g : W →ₗ[K] V) (hd : Module.finrank K V = Module.finrank K W) (h0 : g ∘ₗ f = 0)
    (h1 : LinearMap.range g = LinearMap.ker f) : LinearMap.ker g = LinearMap.range f := by
  have e1 := g.finrank_range_add_finrank_ker
  have e2 := f.finrank_range_add_finrank_ker
  rw [h1] at e1
  exact (Submodule.eq_of_le_of_finrank_eq (LinearMap.range_le_ker_iff.2 h0) (by omega)).symm

theorem rigExt_field_of_charP (p : ℕ) [Fact p.Prime] (K : Type)
    [Field K] (h : (p : K) = 0) (G : PDivGroup p K) :
    Module.Finite K G.RigExt ∧ Module.finrank K G.RigExt = G.height ∧
    Module.finrank K G.omega + Module.finrank K G.dual.omega = G.height ∧
    LinearMap.range (rigExtMap (verschiebung h G)) = LinearMap.range (frobTwist h G).rigOfOmega ∧
    LinearMap.ker (rigExtMap (relFrob h G)) = LinearMap.range (frobTwist h G).rigOfOmega ∧
    LinearMap.ker (rigExtMap (verschiebung h G)) = LinearMap.range (rigExtMap (relFrob h G)) ∧
    LinearMap.range (rigExtMap (relFrob h G)) = Submodule.span K (Set.range (absFrob h G).rig) := by
  obtain ⟨-, f1, d1, d2⟩ := GlobalTheory.T.finrank_rigidExtensions_eq_height_and_dim_add_dual p K h G
  obtain ⟨-, f2, d3, -⟩ := GlobalTheory.T.finrank_rigidExtensions_eq_height_and_dim_add_dual p K h (frobTwist h G)
  have h4 := le_antisymm (range_rigExtMap_verschiebung_le h G) (GlobalTheory.T.range_rigOfOmega_le_range_rigExtMap_verschiebung' p K h G)
  have h5 := le_antisymm (GlobalTheory.T.ker_rigExtMap_relFrob_le_range_rigOfOmega' p K h G)
    (LinearMap.range_le_ker_iff.2 (rigExtMap_relFrob_comp_rigOfOmega h G))
  have h6 : rigExtMap (verschiebung h G) ∘ₗ rigExtMap (relFrob h G) = 0 :=
    (rigExtMap_comp (verschiebung h G) (relFrob h G)).symm.trans
      ((congrArg rigExtMap (verschiebung_comp_relFrob h G)).trans
        (GlobalTheory.T.rigidifiedExtensionPullback_add_and_prime_smul_id p K h (frobTwist h G) (frobTwist h G)).2)
  exact ⟨f1, d1, d2, h4, h5, ker_eq_range_of_range_eq_ker f2 f1 _ _
    (d3.trans ((frobTwist_height h G).trans d1.symm)) h6 (h4.trans h5.symm),
    range_rigExtMap_relFrob h G⟩

end PDivGroup

end GlobalTheory
end
end
