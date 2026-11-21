import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteSupport
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestKTypesJointShapeBlockUnitary
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GluingLawHolds
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFockPolynomialIsoUnitaryPair
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesPureInnerProductsTensorProduct
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubstitutionTotalDegreeLe
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultTEqZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NoIntertwinerSmallerFockToDiscreteSeries
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EquivariantMapCarriesGelfandInvariantToFunction
import Development.AbelianVarietyTheory.Statements.HaarFundamentalDomain.ExistsHaarFundDom
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScalarOfComm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InclTprodUpdate
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsKActOfStable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AbsIrrOfEquiv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryImage
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteDimensionalKill
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoverKerOfDown
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLocalFockIntertwinerRealPlaceOfCoverContra
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegrationByPartsRightDerivativeAdelicQuotient
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOfContinuous
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOnMulRight

section
noncomputable section

open scoped TensorProduct Classical
open GlobalTheory.Chain.IoLift

namespace GlobalTheory.TensorContraction

variable {ι : Type} [Fintype ι] {K : ι → Type} [∀ i, AddCommGroup (K i)] [∀ i, Module ℂ (K i)]

theorem prod_update_self [d : DecidableEq ι] (φ : ∀ j, K j →ₗ[ℂ] ℂ) (s : Finset ι) (j : ι) (hj : j ∉ s)
    (v : ∀ k, K k) (x : K j) :
    ∏ k ∈ s, φ k (Function.update v j x k) = ∏ k ∈ s, φ k (v k) := by
  refine Finset.prod_congr rfl fun k hk => ?_
  have hk' : k ≠ j := fun e => hj (e ▸ hk)
  rw [Function.update_of_ne hk']

theorem prod_update_mem [d : DecidableEq ι] (φ : ∀ j, K j →ₗ[ℂ] ℂ) (s : Finset ι) (j : ι) (hj : j ∈ s)
    (v : ∀ k, K k) (x : K j) :
    ∏ k ∈ s, φ k (Function.update v j x k) = φ j x * ∏ k ∈ s.erase j, φ k (v k) := by
  rw [← Finset.mul_prod_erase s _ hj, Function.update_self,
    prod_update_self φ (s.erase j) j (Finset.notMem_erase j s) v x]

def contrM (φ : ∀ j, K j →ₗ[ℂ] ℂ) (s : Finset ι) (i : ι) (hi : i ∉ s) (hs : ∀ j, j ≠ i → j ∈ s) :
    MultilinearMap ℂ K (K i) where
  toFun v := (∏ k ∈ s, φ k (v k)) • v i
  map_update_add' v j x y := by
    by_cases h : j = i
    · subst h
      simp only [prod_update_self φ s j hi, Function.update_self, smul_add]
    · simp only [prod_update_mem φ s j (hs j h), Function.update_of_ne (Ne.symm h), map_add, add_mul, add_smul]
  map_update_smul' v j c x := by
    by_cases h : j = i
    · subst h
      simp only [prod_update_self φ s j hi, Function.update_self]
      rw [smul_comm]
    · simp only [prod_update_mem φ s j (hs j h), Function.update_of_ne (Ne.symm h), map_smul, smul_eq_mul,
        mul_assoc, mul_smul]

def contrL (φ : ∀ j, K j →ₗ[ℂ] ℂ) (i : ι) : (⨂[ℂ] j, K j) →ₗ[ℂ] K i :=
  PiTensorProduct.lift (contrM φ (Finset.univ.erase i) i (Finset.notMem_erase _ _)
    fun j h => Finset.mem_erase.2 ⟨h, Finset.mem_univ j⟩)

theorem contrL_tprod (φ : ∀ j, K j →ₗ[ℂ] ℂ) (i : ι) (v : ∀ j, K j) :
    contrL φ i (PiTensorProduct.tprod ℂ v) = (∏ k ∈ Finset.univ.erase i, φ k (v k)) • v i := by
  rw [contrL, PiTensorProduct.lift.tprod]
  rfl

theorem contrL_comp_mapFactor (φ : ∀ j, K j →ₗ[ℂ] ℂ) (i : ι) (f : Module.End ℂ (K i)) :
    contrL φ i ∘ₗ intersection_update_fsHerm_neg_one i f = f ∘ₗ contrL φ i := by
  apply PiTensorProduct.ext
  refine MultilinearMap.ext fun v => ?_
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, position_tprod, contrL_tprod]
  rw [prod_update_self φ _ i (Finset.notMem_erase i _), Function.update_self, map_smul]

private theorem eq_zero_of_contrL_eq_zero (i : ι) (z : ⨂[ℂ] j, K j)
    (h : ∀ φ : ∀ j, K j →ₗ[ℂ] ℂ, contrL φ i z = 0) : z = 0 := by
  let b : ∀ j, Module.Basis (Module.Basis.ofVectorSpaceIndex ℂ (K j)) ℂ (K j) :=
    fun j => Module.Basis.ofVectorSpace ℂ (K j)
  let B := Basis.piTensorProduct b
  refine B.forall_coord_eq_zero_iff.1 fun p => ?_
  let φ : ∀ j, K j →ₗ[ℂ] ℂ := fun j => (b j).coord (p j)
  have key : B.coord p = (b i).coord (p i) ∘ₗ contrL φ i := by
    apply PiTensorProduct.ext
    refine MultilinearMap.ext fun v => ?_
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, contrL_tprod, map_smul, smul_eq_mul, Module.Basis.coord_apply, B,
      Basis.piTensorProduct_repr_tprod_apply, φ]
    rw [Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  rw [key, LinearMap.comp_apply, h φ, map_zero]

theorem eq_of_contrL (i : ι) (x y : ⨂[ℂ] j, K j) (h : ∀ φ : ∀ j, K j →ₗ[ℂ] ℂ, contrL φ i x = contrL φ i y) :
    x = y := by
  rw [← sub_eq_zero]
  exact eq_zero_of_contrL_eq_zero i (x - y) fun φ => by rw [map_sub, h φ, sub_self]

private theorem piTensorProduct_map_ite_eq_self_of_slot_fixed (p : ∀ j, Module.End ℂ (K j)) (x : ⨂[ℂ] j, K j)
    (h : ∀ i, intersection_update_fsHerm_neg_one i (p i) x = x) (s : Finset ι) :
    PiTensorProduct.map (fun j => if j ∈ s then p j else LinearMap.id) x = x := by
  induction s using Finset.induction_on with
  | empty => simp [PiTensorProduct.map_id]
  | insert a s ha ih =>
    have e : (fun j => if j ∈ insert a s then p j else (LinearMap.id : Module.End ℂ (K j))) =
        fun j => Function.update (fun j => (LinearMap.id : K j →ₗ[ℂ] K j)) a (p a) j ∘ₗ
          (if j ∈ s then p j else LinearMap.id) := by
      funext j
      by_cases hj : j = a
      · subst hj
        simp [ha]
      · simp [hj]
    rw [e, PiTensorProduct.map_comp, LinearMap.comp_apply, ih]
    exact h a

theorem map_eq_self (p : ∀ j, Module.End ℂ (K j)) (x : ⨂[ℂ] j, K j) (h : ∀ i, intersection_update_fsHerm_neg_one i (p i) x = x) :
    PiTensorProduct.map p x = x := by
  simpa using piTensorProduct_map_ite_eq_self_of_slot_fixed p x h Finset.univ

theorem mem_range_map (ι : Type) [Fintype ι] (K : ι → Type) [∀ i, AddCommGroup (K i)] [∀ i, Module ℂ (K i)]
    (N : ∀ i, Submodule ℂ (K i)) (x : ⨂[ℂ] i, K i)
    (h : ∀ (i : ι) (L : (⨂[ℂ] j, K j) →ₗ[ℂ] K i), (∀ f : Module.End ℂ (K i), L ∘ₗ intersection_update_fsHerm_neg_one i f = f ∘ₗ L) → L x ∈ N i) :
    x ∈ LinearMap.range (PiTensorProduct.map fun i => (N i).subtype) := by

  have hN : ∀ i, ∀ φ : ∀ j, K j →ₗ[ℂ] ℂ, contrL φ i x ∈ N i :=
    fun i φ => h i (contrL φ i) (contrL_comp_mapFactor φ i)

  choose g hg using fun i => LinearMap.exists_leftInverse_of_injective (N i).subtype (N i).ker_subtype
  let P : ∀ i, Module.End ℂ (K i) := fun i => (N i).subtype ∘ₗ g i
  have hP : ∀ i, ∀ v ∈ N i, P i v = v := fun i v hv => by
    have := congrArg (fun f => (N i).subtype (f ⟨v, hv⟩)) (hg i)
    simpa [P] using this

  have hfix : ∀ i, intersection_update_fsHerm_neg_one i (P i) x = x := fun i =>
    eq_of_contrL i _ _ fun φ => by
      rw [← LinearMap.comp_apply (contrL φ i), contrL_comp_mapFactor, LinearMap.comp_apply, hP i _ (hN i φ)]
  rw [LinearMap.mem_range]
  refine ⟨PiTensorProduct.map g x, ?_⟩
  rw [← LinearMap.comp_apply, ← PiTensorProduct.map_comp]
  exact map_eq_self P x hfix

end GlobalTheory.TensorContraction

end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix MeasureTheory GlobalTheory.Chain GlobalTheory.Chain.RealIt
open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension (kFin KVec KMap maxCpt rep_mem_kFin)
open scoped TensorProduct InnerProductSpace Classical
open GlobalTheory.Chain.IoLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain.IoLift

theorem mem_range_map_subtype_of_contr (ι : Type) [Fintype ι] (K : ι → Type) [∀ i, AddCommGroup (K i)]
    [∀ i, Module ℂ (K i)] (N : ∀ i, Submodule ℂ (K i)) (x : ⨂[ℂ] i, K i)
    (h : ∀ i (L : (⨂[ℂ] j, K j) →ₗ[ℂ] K i), (∀ f : Module.End ℂ (K i), L ∘ₗ intersection_update_fsHerm_neg_one i f = f ∘ₗ L) → L x ∈ N i) :
    x ∈ LinearMap.range (PiTensorProduct.map fun i => (N i).subtype) := by
  first
  | exact @_root_.GlobalTheory.TensorContraction.mem_range_map
  | exact _root_.GlobalTheory.TensorContraction.mem_range_map
  | (apply _root_.GlobalTheory.TensorContraction.mem_range_map <;> assumption)
  | (intros; apply _root_.GlobalTheory.TensorContraction.mem_range_map <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TensorContraction.mem_range_map <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TensorContraction.mem_range_map ..)

end GlobalTheory.Chain.IoLift
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix MeasureTheory GlobalTheory.Chain GlobalTheory.Chain.RealIt
open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension (kFin KVec KMap maxCpt rep_mem_kFin)
open scoped TensorProduct InnerProductSpace Classical
open GlobalTheory.Chain.IoLift

namespace GlobalTheory.Chain.IoLift.Factor

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem kerLe_finset {A B Z₁ Z₂ σ : Type} [AddCommMonoid Z₁] [AddCommMonoid Z₂] {q₁ : A → B → Z₁} {q₂ : A → B → Z₂}
    (h : KerLe q₁ q₂) (s : Finset σ) (a : σ → A) (b : σ → B) (h0 : ∑ r ∈ s, q₁ (a r) (b r) = 0) :
    ∑ r ∈ s, q₂ (a r) (b r) = 0 := by
  have e := s.equivFin.symm
  rw [← Finset.sum_coe_sort s, ← e.sum_comp] at h0 ⊢
  exact h _ (fun k => a (e k)) (fun k => b (e k)) h0

theorem section_eq {ι : Type} [Fintype ι] {N K : ι → Type} [∀ i, AddCommGroup (K i)] [∀ i, Module ℂ (K i)]
    [∀ i, AddCommGroup (N i)] [∀ i, Module ℂ (N i)] {Z : Type} [AddCommGroup Z] [Module ℂ Z]
    (α : ∀ i, N i →ₗ[ℂ] K i) (s : ∀ i, K i →ₗ[ℂ] N i) (hs : ∀ i x, α i (s i x) = x)
    (M : MultilinearMap ℂ N Z) (hM : ∀ n i z, α i z = 0 → M (Function.update n i z) = 0) (n : ∀ i, N i) :
    M (fun i => s i (α i (n i))) = M n := by
  have key : ∀ S : Finset ι, M (S.piecewise (fun i => s i (α i (n i))) n) = M n := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | insert j S hj ih =>
      rw [Finset.piecewise_insert, ← ih]
      have h1 := hM (S.piecewise (fun i => s i (α i (n i))) n) j (s j (α j (n j)) - n j) (by simp [hs])
      rw [MultilinearMap.map_update_sub, sub_eq_zero] at h1
      rw [h1]
      congr 1
      rw [Function.update_eq_self_iff, Finset.piecewise_eq_of_notMem _ _ _ hj]
  simpa using key Finset.univ

theorem factor :
    ∀ (ι : Type) [Fintype ι] (K : ι → Type) [∀ i, AddCommGroup (K i)] [∀ i, Module ℂ (K i)] (P Y : ι → Type) [∀ i, AddCommGroup (P i)] [∀ i, Module ℂ (P i)] [∀ i, AddCommGroup (Y i)] [∀ i, Module ℂ (Y i)] (A : ∀ i, P i →ₗ[ℂ] Y i →ₗ[ℂ] K i), (∀ i, Submodule.span ℂ {x | ∃ p y, A i p y = x} = ⊤) → Submodule.span ℂ {x : ⨂[ℂ] i, K i | ∃ (p : ∀ i, P i) (y : ∀ i, Y i), PiTensorProduct.tprod ℂ (fun i => A i (p i) (y i)) = x} = ⊤ ∧ ∀ (Z : Type) [AddCommGroup Z] [Module ℂ Z] (B : MultilinearMap ℂ P (MultilinearMap ℂ Y Z)), (∀ i p y, KerLe (fun x z => A i x z) fun x z => B (Function.update p i x) (Function.update y i z)) → ∃ T : (⨂[ℂ] i, K i) →ₗ[ℂ] Z, ∀ p y, T (PiTensorProduct.tprod ℂ fun i => A i (p i) (y i)) = B p y := by
  intro ι _ K _ _ P Y _ _ _ _ A hA
  let α : ∀ i, (P i × Y i →₀ ℂ) →ₗ[ℂ] K i := fun i => Finsupp.linearCombination ℂ fun r => A i r.1 r.2
  have hα : ∀ i, LinearMap.range (α i) = ⊤ := by
    intro i
    rw [Finsupp.range_linearCombination, ← hA i]
    congr 1
    ext x
    simp
  choose s hs using fun i => (α i).exists_rightInverse_of_surjective (hα i)
  have hs' : ∀ i x, α i (s i x) = x := fun i x => LinearMap.congr_fun (hs i) x
  let b0 : ∀ i, Module.Basis (P i × Y i) ℂ (P i × Y i →₀ ℂ) := fun i => Finsupp.basisSingleOne
  have hb0 : ∀ i r, α i (b0 i r) = A i r.1 r.2 := by
    intro i r
    simp [α, b0]
  let b := Basis.piTensorProduct b0
  refine ⟨?_, ?_⟩
  · have hsurj : LinearMap.range (PiTensorProduct.map α) = ⊤ := by
      rw [LinearMap.range_eq_top]
      intro t
      refine ⟨PiTensorProduct.map s t, ?_⟩
      rw [← LinearMap.comp_apply, ← PiTensorProduct.map_comp]
      simp [hs]
    rw [LinearMap.range_eq_map, ← b.span_eq, Submodule.map_span] at hsurj
    rw [eq_top_iff, ← hsurj]
    apply Submodule.span_mono
    rintro _ ⟨_, ⟨q, rfl⟩, rfl⟩
    refine ⟨fun i => (q i).1, fun i => (q i).2, ?_⟩
    simp [b, hb0]
  · intro Z _ _ B hB
    let M : MultilinearMap ℂ (fun i => P i × Y i →₀ ℂ) Z :=
      (b.constr ℂ fun q => B (fun i => (q i).1) (fun i => (q i).2)).compMultilinearMap (PiTensorProduct.tprod ℂ)
    have hMb : ∀ q : ∀ i, P i × Y i, M (fun i => b0 i (q i)) = B (fun i => (q i).1) (fun i => (q i).2) := by
      intro q
      simp only [M, LinearMap.compMultilinearMap_apply]
      rw [← Basis.piTensorProduct_apply b0 q]
      exact b.constr_basis ℂ _ q
    have hM0 : ∀ (q : ∀ i, P i × Y i) i z, α i z = 0 → M (Function.update (fun i => b0 i (q i)) i z) = 0 := by
      intro q i z hz
      have h1 : ∀ r, M (Function.update (fun i => b0 i (q i)) i (b0 i r)) =
          B (Function.update (fun i => (q i).1) i r.1) (Function.update (fun i => (q i).2) i r.2) := by
        intro r
        have := hMb (Function.update q i r)
        convert this using 2 <;> [skip; congr 1; skip] <;> funext j <;> by_cases h : j = i <;>
          first | (subst h; simp) | simp [h]
      have h2 : M (Function.update (fun i => b0 i (q i)) i z) = ∑ r ∈ z.support,
          B (Function.update (fun i => (q i).1) i (z r • r.1)) (Function.update (fun i => (q i).2) i r.2) := by
        have hz' : z = ∑ r ∈ z.support, z r • b0 i r := by
          conv_lhs => rw [← Finsupp.sum_single z]
          simp [Finsupp.sum, b0]
        conv_lhs => rw [hz']
        rw [MultilinearMap.map_update_sum]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [MultilinearMap.map_update_smul, MultilinearMap.map_update_smul, h1]
        rfl
      rw [h2]
      refine kerLe_finset (hB i (fun i => (q i).1) (fun i => (q i).2)) z.support (fun r => z r • r.1)
        (fun r => r.2) ?_
      simpa [α, Finsupp.linearCombination_apply, Finsupp.sum] using hz
    have hM : ∀ n i z, α i z = 0 → M (Function.update n i z) = 0 := by
      intro n i z hz
      let φ : (P i × Y i →₀ ℂ) →ₗ[ℂ] (P i × Y i →₀ ℂ) := Finsupp.linearCombination ℂ fun _ => z
      have hφ : ∀ r, φ (b0 i r) = z := by
        intro r
        simp [φ, b0]
      let f : ∀ j, (P j × Y j →₀ ℂ) →ₗ[ℂ] (P j × Y j →₀ ℂ) := Function.update (fun j => LinearMap.id) i φ
      have hf : ∀ m : ∀ j, (P j × Y j →₀ ℂ), (fun j => f j (m j)) = Function.update m i (φ (m i)) := by
        intro m
        funext j
        by_cases h : j = i
        · subst h; simp [f]
        · simp [f, h]
      have h0 : M.compLinearMap f = 0 := by
        refine Module.Basis.ext_multilinear b0 fun q => ?_
        rw [MultilinearMap.compLinearMap_apply, hf, hφ]
        exact hM0 q i z hz
      have := congrArg (fun F => F (Function.update n i (b0 i 0))) h0
      simpa [hf, hφ] using this
    refine ⟨PiTensorProduct.lift (M.compLinearMap s), fun p y => ?_⟩
    rw [PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply, ← hMb fun i => (p i, y i),
      ← section_eq α s hs' M hM fun i => b0 i (p i, y i)]
    simp only [hb0]

end GlobalTheory.Chain.IoLift.Factor

end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix MeasureTheory GlobalTheory.Chain GlobalTheory.Chain.RealIt
open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension (kFin KVec KMap maxCpt rep_mem_kFin)
open scoped TensorProduct InnerProductSpace Classical
open GlobalTheory.Chain.IoLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain.IoLift

theorem adjZ_eq_neg_of_mem_upq {p q : ℕ} {Z : Mat p q} (h : Z ∈ upq p q) : adjZ Z = -Z := by
  have h0 : Zᴴ * Jm p q + Jm p q * Z = 0 := h
  have h1 : Zᴴ * Jm p q = -(Jm p q * Z) := eq_neg_of_add_eq_zero_left h0
  rw [adjZ, Matrix.mul_assoc, h1, Matrix.mul_neg, ← Matrix.mul_assoc,
    GlobalTheory.InvPairingTensor.Jm_mul_self, Matrix.one_mul]

theorem finiteSupport_of_admissible :
    ∀ (p q r s : ℕ) (T : GrpData r s) (R : DSRep T), Formalism.MainNotions.SchurIrreducible.AdmGK R.HK → FiniteSupport p q R := by
  intro p q r s T R hA A _ _ B hB P
  refine GlobalTheory.InvPairingTensor.exists_finiteDimensional_kill R hA B (fun Z hZ Q y => ?_) P
  rw [hB Z Q y, adjZ_eq_neg_of_mem_upq hZ, map_neg, LinearMap.neg_apply, map_neg, neg_add_cancel]

end GlobalTheory.Chain.IoLift
end

section
noncomputable section

open scoped TensorProduct InnerProductSpace Classical

namespace GlobalTheory.Chain.IoLift.TensorFormProof

open GlobalTheory.Chain.IoLift

variable {A V H : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup V] [Module ℂ V] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H]

theorem contr_tmul (ι : V →ₗ[ℂ] H) (y : V) (a : A) (v : V) :
    contr ι y (a ⊗ₜ[ℂ] v) = ⟪ι y, ι v⟫_ℂ • a := by
  unfold contr
  rw [LinearMap.comp_apply, LinearMap.lTensor_tmul, LinearMap.comp_apply, innerₛₗ_apply_apply]
  exact TensorProduct.rid_tmul _ _

theorem dual_contr (ι : V →ₗ[ℂ] H) (y : V) (l : A →ₗ[ℂ] ℂ) (t : A ⊗[ℂ] V) :
    l (contr ι y t) = ⟪ι y, ι (TensorProduct.lid ℂ V (LinearMap.rTensor V l t))⟫_ℂ := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a v =>
    rw [contr_tmul, map_smul, LinearMap.rTensor_tmul, TensorProduct.lid_tmul, map_smul, inner_smul_right,
      smul_eq_mul, mul_comm]
  | add s u hs hu => simp only [map_add, inner_add_right, hs, hu]

theorem eq_zero_of_contr (ι : V →ₗ[ℂ] H) (hι : Function.Injective ι) (t : A ⊗[ℂ] V)
    (h : ∀ y, contr ι y t = 0) : t = 0 := by

  have hl : ∀ l : A →ₗ[ℂ] ℂ, LinearMap.rTensor V l t = 0 := by
    intro l
    set w := TensorProduct.lid ℂ V (LinearMap.rTensor V l t) with hw
    have h0 : ⟪ι w, ι w⟫_ℂ = 0 := by
      have := dual_contr ι w l t
      rw [h w, map_zero] at this
      exact this.symm
    have hw0 : w = 0 := hι ((inner_self_eq_zero.mp h0).trans (map_zero ι).symm)
    rw [hw] at hw0
    exact (LinearEquiv.map_eq_zero_iff _).mp hw0

  let e := (Module.Basis.ofVectorSpace ℂ A).repr
  have hs : TensorProduct.finsuppScalarLeft ℂ V _ (LinearMap.rTensor V e.toLinearMap t) = 0 := by
    ext i
    rw [TensorProduct.finsuppScalarLeft_apply, ← LinearMap.rTensor_comp_apply, hl, map_zero]
    rfl
  have h2 : LinearMap.rTensor V e.toLinearMap t = 0 := (LinearEquiv.map_eq_zero_iff _).mp hs
  have h3 := congrArg (LinearMap.rTensor V e.symm.toLinearMap) h2
  rwa [← LinearMap.rTensor_comp_apply, LinearEquiv.symm_comp, LinearMap.rTensor_id_apply, map_zero] at h3

theorem exists_tensor (ι : V →ₗ[ℂ] H) (β : V →ₛₗ[starRingEnd ℂ] A) (E : Submodule ℂ V) [FiniteDimensional ℂ E]
    (h : ∀ y, (∀ e ∈ E, ⟪ι y, ι e⟫_ℂ = 0) → β y = 0) : ∃ t : A ⊗[ℂ] V, ∀ y, contr ι y t = β y := by

  set F : Submodule ℂ H := E.map ι with hF
  haveI : FiniteDimensional ℂ F := by rw [hF]; infer_instance
  let b := stdOrthonormalBasis ℂ F
  have hpre : ∀ k, ∃ e : V, e ∈ E ∧ ι e = (b k : H) := fun k => Submodule.mem_map.mp (b k).2
  choose e heE he using hpre
  refine ⟨∑ k, β (e k) ⊗ₜ[ℂ] e k, fun y => ?_⟩
  rw [map_sum]
  simp only [contr_tmul, he]

  set z : V := ∑ k, ⟪(b k : H), ι y⟫_ℂ • e k with hz
  have hperp : ∀ x ∈ E, ⟪ι (y - z), ι x⟫_ℂ = 0 := by
    intro x hx
    have hxF : ι x ∈ F := Submodule.mem_map_of_mem hx
    have hx' : ι x = ∑ j, ⟪(b j : H), ι x⟫_ℂ • (b j : H) := by
      have := congrArg Subtype.val (b.sum_repr' ⟨ι x, hxF⟩)
      simpa [Submodule.coe_inner] using this.symm
    have key : ⟪ι y, ι x⟫_ℂ = ∑ j, ⟪ι y, (b j : H)⟫_ℂ * ⟪(b j : H), ι x⟫_ℂ := by
      conv_lhs => rw [hx']
      rw [inner_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [inner_smul_right, mul_comm]
    simp only [hz, map_sub, map_sum, map_smul, he, inner_sub_left, sum_inner, inner_smul_left, inner_conj_symm]
    rw [key, sub_self]
  have hyz := h (y - z) hperp
  rw [map_sub, sub_eq_zero] at hyz
  rw [hyz, hz, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [LinearMap.map_smulₛₗ, inner_conj_symm]

theorem tensorForm : TensorForm := by
  intro U A V H _ _ _ _ _ _ _ _ ι hι
  have sep : ∀ s u : A ⊗[ℂ] V, (∀ y, contr ι y s = contr ι y u) → s = u := fun s u hsu =>
    sub_eq_zero.mp (eq_zero_of_contr ι hι _ fun y => by rw [map_sub, hsu, sub_self])
  refine ⟨fun t ht => eq_zero_of_contr ι hι t ht, fun B hB => ?_⟩
  have hex : ∀ P, ∃ t : A ⊗[ℂ] V, ∀ y, contr ι y t = B P y := by
    intro P
    obtain ⟨E, hE, hk⟩ := hB P
    exact exists_tensor ι (B P) E hk
  choose g hg using hex
  exact ⟨{ toFun := g
           map_add' := fun P Q => sep _ _ fun y => by simp [hg]
           map_smul' := fun c P => sep _ _ fun y => by simp [hg] }, hg⟩

end GlobalTheory.Chain.IoLift.TensorFormProof

end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix MeasureTheory GlobalTheory.Chain GlobalTheory.Chain.RealIt
open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension (kFin KVec KMap maxCpt rep_mem_kFin)
open scoped TensorProduct InnerProductSpace Classical
open GlobalTheory.Chain.IoLift GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix GlobalTheory.Chain.RealIt.LocalFromCover

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain.IoLift.KerTransfer

theorem locKer_of_coverKer (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S')
    (τ : D.what₂.Tau) (p q r s : ℕ) (T₁ : GrpData p q) (T₂ : GrpData r s) (R₁ : DSRep T₁) (R₂ : DSRep T₂)
    (e : Ix p q ≃ Fin V.rank) (e' : Ix r s ≃ Fin W.rank) (m m' : ℤ) (aS aT : ℚ) (U : M.H τ → R₁.U.H)
    (U' : M'.H τ ≃ₗᵢ⋆[ℂ] R₂.U.H) (κ : LPol W.rank V.rank ≃ₗ[ℂ] Pol p q r s)
    (a' : Matrix (Fin W.rank) (Fin W.rank) ℂ → Module.End ℂ (kFin M' τ)) (hm' : (m' : ℚ) = 2 * aS)
    (h₁ : Matches R₁ M τ (barMat e) m U) (h₂ : Matches R₂ M' τ (plainMat e') m' U')
    (hκ : IsPolyIso (M.ε τ) (M'.ε τ) e e' κ) (ha : IsKAct M' τ a') (hC : CoverKer p q R₂.HK) :
    LocKer M M' τ aS aT a' := by
  have hmC' : (m' : ℂ) = 2 * (aS : ℂ) := by exact_mod_cast hm'
  have hmem : ∀ v, U'.symm (R₂.ι v) ∈ kFin M' τ := fun v =>
    (h₂.kfin _).2 ⟨v, (U'.apply_symm_apply _).symm⟩
  let j : R₂.HK.V →ₛₗ[starRingEnd ℂ] kFin M' τ :=
    { toFun := fun v => ⟨U'.symm (R₂.ι v), hmem v⟩
      map_add' := fun v w => Subtype.ext (by simp)
      map_smul' := fun c v => Subtype.ext (by simp [LinearIsometryEquiv.map_smulₛₗ]) }
  have hj : ∀ v, U' (j v : M'.H τ) = R₂.ι v := fun v => U'.apply_symm_apply _
  have hsurj : Function.Surjective j := fun y => by
    obtain ⟨v, hv⟩ := (h₂.kfin y).1 y.2
    exact ⟨v, Subtype.ext (U'.injective (by rw [hj, hv]))⟩
  have key : ∀ (Z : Type) [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
      (B : LPol W.rank V.rank →ₗ[ℂ] kFin M' τ →ₗ[ℂ] Z), IsLocPair M M' τ aS aT a' B →
      ∃ B' : Pol p q r s →ₗ[ℂ] R₂.HK.V →ₛₗ[starRingEnd ℂ] Z, IsCoverPair R₂.HK B' ∧
        ∀ P v, B' (κ P) v = B P (j v) := by
    intro Z _ _ B hB
    let B' : Pol p q r s →ₗ[ℂ] R₂.HK.V →ₛₗ[starRingEnd ℂ] Z :=
      { toFun := fun P => (B (κ.symm P)).comp j
        map_add' := fun P Q => by ext v; simp
        map_smul' := fun c P => by ext v; simp }
    have hB' : ∀ P v, B' (κ P) v = B P (j v) := fun P v => by simp [B']
    refine ⟨B', ⟨fun X hX P P' y y' => ?_, fun Y hY P y => ?_⟩, hB'⟩
    · obtain ⟨P, rfl⟩ := κ.surjective P
      obtain ⟨P', rfl⟩ := κ.surjective P'
      have hX' : toFrame M τ (barMat e X) ∈ lieAt V τ := h₁.lie ▸ ⟨X, hX, rfl⟩
      have h3 : (barMat e X).map (starRingEnd ℂ) = Matrix.reindex e e X := by ext a b; simp [barMat]
      have h4 : (barMat e X).trace = -X.trace := by
        rw [barMat, trace_reindex', ← trace_conj hX]
        simp [Matrix.trace]
      have h := hB.skew _ hX' P P' (j y) (j y')
      simp only [sOp, fr_toFrame, trace_toFrame, h3, h4, LinearMap.add_apply, LinearMap.smul_apply,
        Module.End.one_apply, map_add, map_smul, inner_add_left, inner_add_right, inner_smul_left,
        inner_smul_right, map_neg, map_mul, map_ratCast, trace_conj hX] at h
      rw [← hκ.1, ← hκ.1, hB', hB', hB', hB']
      linear_combination h
    · obtain ⟨P, rfl⟩ := κ.surjective P
      have hY' : toFrame M' τ (plainMat e' Y) ∈ lieAt W τ := h₂.lie ▸ ⟨Y, hY, rfl⟩
      have h4 : (plainMat e' Y).trace = Y.trace := trace_reindex' e' Y
      have h5 : a' (toFrame M' τ (plainMat e' Y)) (j y) = j (R₂.HK.act Y y) - ((aS : ℂ) * Y.trace) • j y := by
        have h6 : a' (toFrame M' τ (plainMat e' Y)) (j y) =
            j (R₂.HK.act Y y + ((m' : ℂ) / 2 * Y.trace) • y) := by
          refine Subtype.ext (U'.injective ?_)
          rw [hj, ← h₂.der Y hY y _ (hj y), dRep, (ha.der _ hY' (j y)).deriv]
        rw [h6, map_add, LinearMap.map_smulₛₗ, map_mul, map_div₀, map_intCast, map_ofNat, trace_conj hY, hmC',
          sub_eq_add_neg, ← neg_smul]
        congr 2
        ring
      have h := hB.inv _ hY' P (j y)
      rw [h5, tOp, fr_toFrame, trace_toFrame, h4] at h
      rw [← hκ.2, hB', hB', ← h]
      simp [plainMat]
  intro Z₁ Z₂ _ _ _ _ B₁ B₂ hB₁ hB₂ hne n a b hs
  obtain ⟨C₁, hC₁, e₁⟩ := key Z₁ B₁ hB₁
  obtain ⟨C₂, hC₂, e₂⟩ := key Z₂ B₂ hB₂
  choose g hg using hsurj
  have hne' : C₁ ≠ 0 := fun h0 => hne (LinearMap.ext fun P => LinearMap.ext fun y => by
    rw [← hg y, ← e₁, h0]; rfl)
  have h := hC Z₁ Z₂ C₁ C₂ hC₁ hC₂ hne' n (fun i => κ (a i)) (fun i => g (b i)) (by simpa [e₁, hg] using hs)
  simpa [e₂, hg] using h

end GlobalTheory.Chain.IoLift.KerTransfer

end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix MeasureTheory GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace Classical
open GlobalTheory.Chain.IoLift

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain.CuspL2

theorem exists_toLp_ext {G : Type} [MeasurableSpace G] (ν : Measure G) :
    ∃ E : (G → ℂ) →ₗ[ℂ] Lp ℂ 2 ν, ∀ φ, MemLp φ 2 ν → E φ =ᵐ[ν] φ := by
  classical
  let S : Submodule ℂ (G → ℂ) :=
    { carrier := {φ | MemLp φ 2 ν}
      add_mem' := fun ha hb => ha.add hb
      zero_mem' := by
        first
          | exact MemLp.zero
          | exact MemLp.zero'
          | exact zero_memLp
          | simp
      smul_mem' := fun c _ h => h.const_smul c }
  let f : S →ₗ[ℂ] Lp ℂ 2 ν :=
    { toFun := fun φ => MemLp.toLp (φ : G → ℂ) φ.2
      map_add' := fun φ ψ => MemLp.toLp_add φ.2 ψ.2
      map_smul' := fun c φ => MemLp.toLp_const_smul c φ.2 }
  obtain ⟨E, hE⟩ := LinearMap.exists_extend f
  refine ⟨E, fun φ hφ => ?_⟩
  have hval : E φ = f ⟨φ, hφ⟩ := LinearMap.congr_fun hE ⟨φ, hφ⟩
  rw [hval]
  exact MemLp.coeFn_toLp hφ

theorem inner_eq {G : Type} [MeasurableSpace G] {ν : Measure G} {f f' : Lp ℂ 2 ν} {φ φ' : G → ℂ}
    (h : f =ᵐ[ν] φ) (h' : f' =ᵐ[ν] φ') : ⟪f, f'⟫_ℂ = ∫ g, (starRingEnd ℂ) (φ g) * φ' g ∂ν := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [h, h'] with g hg hg'
  rw [hg, hg']
  first
    | (rw [RCLike.inner_apply]; try ring)
    | simp [mul_comm]

variable {D : D7} {θ : InfFam D} {V : HSp D}

theorem bounded (hP : GlobalTheory.Published.CuspDecaySobolev) (hθ : IsInfFam θ) {φ : GA D V → ℂ} (h : IsCuspGrow θ V φ) :
    ∃ B : ℝ, ∀ g, ‖φ g‖ ≤ B := by
  obtain ⟨ha, hs, hc, hg⟩ := h
  obtain ⟨-, -, hd⟩ := GlobalTheory.Size.rapidDec_of_cuspDecaySobolev hP hθ ha hs hg hc
  obtain ⟨C, hC⟩ := hd 0
  exact ⟨C, fun g => by simpa using hC g⟩

theorem conj_mul {G : Type} [TopologicalSpace G] {φ φ' : G → ℂ} (c : Continuous φ) (c' : Continuous φ')
    (b : ∃ B : ℝ, ∀ g, ‖φ g‖ ≤ B) (b' : ∃ B : ℝ, ∀ g, ‖φ' g‖ ≤ B) :
    Continuous (fun g => (starRingEnd ℂ) (φ g) * φ' g) ∧ ∃ B : ℝ, ∀ g, ‖(starRingEnd ℂ) (φ g) * φ' g‖ ≤ B := by
  obtain ⟨B, hB⟩ := b
  obtain ⟨B', hB'⟩ := b'
  refine ⟨(Complex.continuous_conj.comp c).mul c', max B 0 * max B' 0, fun g => ?_⟩
  calc ‖(starRingEnd ℂ) (φ g) * φ' g‖ = ‖φ g‖ * ‖φ' g‖ := by simp [norm_mul]
    _ ≤ max B 0 * max B' 0 :=
      mul_le_mul ((hB g).trans (le_max_left _ _)) ((hB' g).trans (le_max_left _ _)) (norm_nonneg _)
        (le_max_right _ _)

theorem exists_embedding_skew : GlobalTheory.Published.CuspDecaySobolev → ∀ (D : D7) (θ : InfFam D) (V : HSp D) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), IsInfFam θ → μ.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 μ → ∃ E : (GA D V → ℂ) →ₗ[ℂ] Lp ℂ 2 (μ.restrict 𝓕), (∀ φ, IsCuspGrow θ V φ → MemLp φ 2 (μ.restrict 𝓕) ∧ (E φ = 0 → φ = 0)) ∧ ∀ τ, ∀ X ∈ lieAt V τ, ∀ φ φ', IsCuspGrow θ V φ → IsCuspGrow θ V φ' → IsCuspGrow θ V (Rder θ V τ X φ) → IsCuspGrow θ V (Rder θ V τ X φ') → ⟪E (Rder θ V τ X φ), E φ'⟫_ℂ + ⟪E φ, E (Rder θ V τ X φ')⟫_ℂ = 0 := by
  intro hP D θ V μ 𝓕 hθ hμ h𝓕
  haveI := hμ
  obtain ⟨-, -, -, iB, iT, -, iC⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  haveI := iB
  haveI := iT
  haveI := iC
  haveI := (GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D V μ hμ).1
  have hfin : μ 𝓕 ≠ ⊤ := (GlobalTheory.Mem.QuotVol.quot_volume_ne_zero_ne_top D V μ 𝓕 (And.intro hμ h𝓕)).2
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ]; exact hfin.lt_top⟩
  have hmem : ∀ φ, IsCuspGrow θ V φ → MemLp φ 2 (μ.restrict 𝓕) := by
    intro φ hφ
    obtain ⟨B, hB⟩ := bounded hP hθ hφ
    exact MemLp.of_bound hφ.1.cont.aestronglyMeasurable B (Filter.Eventually.of_forall hB)
  have hint : ∀ F : GA D V → ℂ, Continuous F → (∃ B : ℝ, ∀ g, ‖F g‖ ≤ B) → Integrable F (μ.restrict 𝓕) := by
    rintro F hF ⟨B, hB⟩
    exact memLp_one_iff_integrable.1 (MemLp.of_bound hF.aestronglyMeasurable B (Filter.Eventually.of_forall hB))
  obtain ⟨E, hE⟩ := exists_toLp_ext (μ.restrict 𝓕)
  refine ⟨E, fun φ hφ => ⟨hmem φ hφ, fun h0 => ?_⟩, ?_⟩
  · have h1 := hE φ (hmem φ hφ)
    rw [h0] at h1
    have hz : ⇑(0 : Lp ℂ 2 (μ.restrict 𝓕)) =ᵐ[μ.restrict 𝓕] (0 : GA D V → ℂ) := Lp.coeFn_zero ..
    have hae : ∀ᵐ g ∂(μ.restrict 𝓕), φ g = 0 := by
      filter_upwards [h1, hz] with g a b
      rw [← a, b]
      rfl
    have hopen : IsOpen {g | φ g ≠ 0} := isOpen_ne_fun hφ.1.cont continuous_const
    haveI : SMulInvariantMeasure (GQ V) (GA D V) μ := by
      first
        | exact inferInstance
        | exact ⟨fun γ s _ => measure_preimage_mul μ (γ : GA D V) s⟩
    open Pointwise in
    have hinv : ∀ γ : GQ V, γ • {g | φ g ≠ 0} = {g | φ g ≠ 0} := by
      intro γ
      ext x
      rw [Set.mem_smul_set_iff_inv_smul_mem]
      show φ ((γ⁻¹ : GQ V) * x) ≠ 0 ↔ φ x ≠ 0
      rw [hφ.1.left _ (γ⁻¹).2 x]
    have hnull : μ {g | φ g ≠ 0} = 0 := by
      refine h𝓕.measure_zero_of_invariant _ hinv ?_
      rw [← Measure.restrict_apply hopen.measurableSet]
      exact ae_iff.1 hae
    have hempty := (hopen.measure_eq_zero_iff μ).1 hnull
    funext g
    by_contra hne
    have hg : g ∈ {g | φ g ≠ 0} := hne
    rw [hempty] at hg
    exact hg
  · intro τ X hX φ φ' h1 h2 h3 h4
    rw [inner_eq (hE _ (hmem _ h3)) (hE _ (hmem _ h2)), inner_eq (hE _ (hmem _ h1)) (hE _ (hmem _ h4))]
    obtain ⟨c1, B1, b1⟩ := conj_mul h3.1.cont h2.1.cont (bounded hP hθ h3) (bounded hP hθ h2)
    obtain ⟨c2, B2, b2⟩ := conj_mul h1.1.cont h4.1.cont (bounded hP hθ h1) (bounded hP hθ h4)
    obtain ⟨c0, B0, b0⟩ := conj_mul h1.1.cont h2.1.cont (bounded hP hθ h1) (bounded hP hθ h2)
    rw [← integral_add (hint _ c1 ⟨B1, b1⟩) (hint _ c2 ⟨B2, b2⟩)]
    have key : ∀ ψ : GA D V → ℂ, ψ ∈ GlobalTheory.Mem.AutSpace.SmFun θ V → ∀ g t,
        HasDerivAt (fun s : ℝ => ψ (g * oneP θ V τ X s)) (Rder θ V τ X ψ (g * oneP θ V τ X t)) t := by
      intro ψ hψ g t
      have d0 : HasDerivAt (fun u : ℝ => ψ (g * oneP θ V τ X t * oneP θ V τ X u))
          (Rder θ V τ X ψ (g * oneP θ V τ X t)) 0 :=
        ((GlobalTheory.Mem.AutSpace.differentiable_oneP hψ hX (g * oneP θ V τ X t)) 0).hasDerivAt
      have d1 : HasDerivAt (fun s : ℝ => ψ (g * oneP θ V τ X t * oneP θ V τ X (s - t)))
          (Rder θ V τ X ψ (g * oneP θ V τ X t)) t :=
        HasDerivAt.comp_sub_const (f := fun u : ℝ => ψ (g * oneP θ V τ X t * oneP θ V τ X u)) t t
          (by rw [sub_self]; exact d0)
      refine d1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
      show ψ (g * oneP θ V τ X s) = ψ (g * oneP θ V τ X t * oneP θ V τ X (s - t))
      rw [mul_assoc, ← GlobalTheory.Mem.Lift.oneP_add hθ hX, show t + (s - t) = s by ring]
    have hd : ∀ g t, HasDerivAt
        (fun s : ℝ => (starRingEnd ℂ) (φ (g * oneP θ V τ X s)) * φ' (g * oneP θ V τ X s))
        ((starRingEnd ℂ) (Rder θ V τ X φ (g * oneP θ V τ X t)) * φ' (g * oneP θ V τ X t) +
          (starRingEnd ℂ) (φ (g * oneP θ V τ X t)) * Rder θ V τ X φ' (g * oneP θ V τ X t)) t := by
      intro g t
      exact ((key φ h1.2.1 g t).star).mul (key φ' h2.2.1 g t)
    exact GlobalTheory.Mem.IntByParts.setIntegral_deriv_eq_zero (GQ V) μ h𝓕 hfin
      (Φ := fun g => (starRingEnd ℂ) (φ g) * φ' g)
      (Φ' := fun g => (starRingEnd ℂ) (Rder θ V τ X φ g) * φ' g + (starRingEnd ℂ) (φ g) * Rder θ V τ X φ' g)
      (fun γ hγ g => by
        show (starRingEnd ℂ) (φ (γ * g)) * φ' (γ * g) = (starRingEnd ℂ) (φ g) * φ' g
        rw [h1.1.left γ hγ g, h2.1.left γ hγ g])
      c0 (c1.add c2) b0
      (fun g => (norm_add_le _ _).trans (add_le_add (b1 g) (b2 g)))
      (GlobalTheory.Mem.Lift.oneP_zero hθ) hd

end GlobalTheory.Chain.CuspL2

end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix MeasureTheory GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace Classical
open GlobalTheory.Chain.IoLift

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain.CuspGrowSpace

variable {D : D7} {θ : InfFam D} {V : HSp D} {φ ψ : GA D V → ℂ}

theorem isCuspGrow_add (h : IsCuspGrow θ V φ) (h' : IsCuspGrow θ V ψ) : IsCuspGrow θ V (φ + ψ) := by
  obtain ⟨a, s, c, g⟩ := h
  obtain ⟨a', s', c', g'⟩ := h'
  refine ⟨⟨fun γ hγ g => by rw [Pi.add_apply, Pi.add_apply, a.left γ hγ, a'.left γ hγ], ?_, a.cont.add a'.cont⟩,
    add_mem s s', GlobalTheory.MultMem.isCuspFun_add a a' c c', ?_⟩
  · obtain ⟨U, hU, e⟩ := a.level
    obtain ⟨U', hU', e'⟩ := a'.level
    exact ⟨U ⊓ U', hU.inter hU', fun k hk hf g => by
      rw [Pi.add_apply, Pi.add_apply, e k hk.1 hf, e' k hk.2 hf]⟩
  · obtain ⟨N, hN⟩ := GlobalTheory.Size.unifModGrowth_iff.1 g
    obtain ⟨N', hN'⟩ := GlobalTheory.Size.unifModGrowth_iff.1 g'
    refine GlobalTheory.Size.unifModGrowth_iff.2 ⟨max N N', fun l hl => ?_⟩
    rw [(GlobalTheory.Size.linOnSm_rWord hl).add _ s _ s']
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.2
      ⟨ne_top_of_le_ne_top (hN l hl) (GlobalTheory.Size.growthSize_anti (le_max_left _ _)),
        ne_top_of_le_ne_top (hN' l hl) (GlobalTheory.Size.growthSize_anti (le_max_right _ _))⟩) GlobalTheory.Size.growthSize_add_le

theorem isCuspGrow_smul (z : ℂ) (h : IsCuspGrow θ V φ) : IsCuspGrow θ V (z • φ) := by
  obtain ⟨a, s, c, g⟩ := h
  refine ⟨⟨fun γ hγ g => by rw [Pi.smul_apply, Pi.smul_apply, a.left γ hγ], ?_, a.cont.const_smul z⟩,
    Submodule.smul_mem _ z s, GlobalTheory.MultMem.isCuspFun_smul z c, ?_⟩
  · obtain ⟨U, hU, e⟩ := a.level
    exact ⟨U, hU, fun k hk hf g => by rw [Pi.smul_apply, Pi.smul_apply, e k hk hf]⟩
  · obtain ⟨N, hN⟩ := GlobalTheory.Size.unifModGrowth_iff.1 g
    refine GlobalTheory.Size.unifModGrowth_iff.2 ⟨N, fun l hl => ?_⟩
    rw [(GlobalTheory.Size.linOnSm_rWord hl).smul, GlobalTheory.Size.growthSize_smul]
    exact ENNReal.mul_ne_top enorm_ne_top (hN l hl)

theorem isCuspGrow_zero : IsCuspGrow θ V 0 := by
  refine ⟨(isAutFunSm_const θ V 0).toIsAutFun, zero_mem _, fun _ _ _ _ _ _ _ _ => by simp,
    GlobalTheory.Size.unifModGrowth_iff.2 ⟨0, fun l hl => ?_⟩⟩
  have := (GlobalTheory.Size.linOnSm_rWord (θ := θ) hl).smul 0 0
  rw [zero_smul, zero_smul] at this
  rw [this]
  exact (GlobalTheory.Size.growthSize_const (0 : ℂ)).trans_ne enorm_ne_top

theorem isCuspGrow_of_mem_span : ∀ (D : D7) (θ : InfFam D) (V : HSp D),
    ∀ φ ∈ Submodule.span ℂ {φ | IsCuspGrow θ V φ}, IsCuspGrow θ V φ := by
  intro D θ V φ h
  induction h using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact isCuspGrow_zero
  | add x y _ _ hx hy => exact isCuspGrow_add hx hy
  | smul c x _ hx => exact isCuspGrow_smul c hx

end GlobalTheory.Chain.CuspGrowSpace

end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix MeasureTheory GlobalTheory.Chain GlobalTheory.Chain.RealIt
open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension (kFin KVec KMap maxCpt rep_mem_kFin)
open scoped TensorProduct InnerProductSpace Classical
open GlobalTheory.Chain.IoLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Chain.IoLift.FockOrbit

open GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators GlobalTheory.PointAtPlaceHom

section General

variable {G σ : Type} [TopologicalSpace G]

def CoefCont (F : G → MvPolynomial σ ℂ) : Prop := ∀ m, Continuous fun k => MvPolynomial.coeff m (F k)

theorem CoefCont.const (P : MvPolynomial σ ℂ) : CoefCont fun _ : G => P := fun _ => continuous_const

theorem CoefCont.add {F F' : G → MvPolynomial σ ℂ} (h : CoefCont F) (h' : CoefCont F') :
    CoefCont fun k => F k + F' k := fun m => by
  simp only [MvPolynomial.coeff_add]
  exact (h m).add (h' m)

theorem CoefCont.mul {F F' : G → MvPolynomial σ ℂ} (h : CoefCont F) (h' : CoefCont F') :
    CoefCont fun k => F k * F' k := fun m => by
  simp only [MvPolynomial.coeff_mul]
  exact continuous_finset_sum _ fun p _ => (h _).mul (h' _)

theorem CoefCont.smul {s : G → ℂ} {F : G → MvPolynomial σ ℂ} (hs : Continuous s) (h : CoefCont F) :
    CoefCont fun k => s k • F k := fun m => by
  simp only [MvPolynomial.coeff_smul, smul_eq_mul]
  exact hs.mul (h m)

theorem CoefCont.sum {ι : Type} [Fintype ι] {F : ι → G → MvPolynomial σ ℂ} (h : ∀ i, CoefCont (F i)) :
    CoefCont fun k => ∑ i, F i k := fun m => by
  simp only [MvPolynomial.coeff_sum]
  exact continuous_finset_sum _ fun i _ => h i m

theorem CoefCont.aeval {τ : Type} {g : G → τ → MvPolynomial σ ℂ} (h : ∀ v, CoefCont fun k => g k v)
    (P : MvPolynomial τ ℂ) : CoefCont fun k => MvPolynomial.aeval (g k) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa using CoefCont.const _
  | add p q hp hq => simpa using hp.add hq
  | mul_X p v hp => simpa using hp.mul (h v)

theorem exists_monomials [Finite σ] (N : ℕ) : ∃ (n : ℕ) (e : Fin n → σ →₀ ℕ), ∀ P : MvPolynomial σ ℂ,
    P.totalDegree ≤ N → P = ∑ i, MvPolynomial.coeff (e i) P • MvPolynomial.monomial (e i) (1 : ℂ) := by
  let T := (Finsupp.finite_of_degree_le (σ := σ) N).toFinset
  refine ⟨T.card, fun i => (T.equivFin.symm i : σ →₀ ℕ), fun P hP => ?_⟩
  rw [T.equivFin.symm.sum_comp (fun d : T => MvPolynomial.coeff (d : σ →₀ ℕ) P •
    MvPolynomial.monomial (d : σ →₀ ℕ) (1 : ℂ)),
    Finset.sum_coe_sort T fun d => MvPolynomial.coeff d P • MvPolynomial.monomial d (1 : ℂ)]
  simp only [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  conv_lhs => rw [P.as_sum]
  refine Finset.sum_subset (fun d hd => ?_) fun d _ hd => ?_
  · simp only [T, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    exact (MvPolynomial.le_totalDegree hd).trans hP
  · rw [MvPolynomial.notMem_support_iff.1 hd, map_zero]

theorem exists_coefFam [Group G] [Finite σ] (ρ : G → Module.End ℂ (MvPolynomial σ ℂ))
    (hm : ∀ a b P, ρ (a * b) P = ρ a (ρ b P)) (hd : ∀ a P, (ρ a P).totalDegree ≤ P.totalDegree)
    (hc : ∀ P, CoefCont fun k => ρ k P) (φ : MvPolynomial σ ℂ) :
    ∃ (n : ℕ) (φs : Fin n → MvPolynomial σ ℂ) (c : Fin n → G → ℂ), IsCoefFam c ∧ ∀ k, ρ k φ = ∑ i, c i k • φs i := by
  obtain ⟨n, e, he⟩ := exists_monomials (σ := σ) φ.totalDegree
  refine ⟨n, fun i => MvPolynomial.monomial (e i) 1, fun i k => MvPolynomial.coeff (e i) (ρ k φ),
    ⟨fun i => hc φ _, fun k₀ i => ⟨fun j => MvPolynomial.coeff (e i) (ρ k₀ (MvPolynomial.monomial (e j) 1)),
      fun k => ?_⟩⟩, fun k => he _ (hd k φ)⟩
  beta_reduce
  rw [hm]
  conv_lhs => rw [he _ (hd k φ)]
  simp only [map_sum, map_smul, MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, smul_eq_mul]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

end General

theorem signBlockDeterminant_ne_zero_of_mem_maxCompact {n : ℕ} {ε : Fin n → Bool} (e : Bool) {k : Matrix (Fin n) (Fin n) ℂ}
    (hk : k ∈ Formalism.REAL.Kset ε) : signBlockDeterminant ε e k ≠ 0 := by
  have hd : k.det ≠ 0 := (Matrix.isUnit_iff_isUnit_det k).1 (Unitary.isUnit_coe (U := ⟨k, hk.1⟩)) |>.ne_zero
  rw [Matrix.twoBlockTriangular_det k (fun i => ε i = e) (fun i hi j hj => by
    have h := congrFun (congrFun hk.2 i) j
    simp only [Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    cases e <;> simp only [Bool.not_eq_true, Bool.not_eq_false] at hi <;> simp [hi, hj] at h <;>
      first | linear_combination (1 / 2 : ℂ) * h | linear_combination (-1 / 2 : ℂ) * h)] at hd
  have := left_ne_zero_of_mul hd
  unfold signBlockDeterminant
  convert this
  rfl

theorem continuous_signBlockDeterminant {n : ℕ} (ε : Fin n → Bool) (e : Bool) : Continuous (signBlockDeterminant ε e) :=
  (continuous_id.matrix_submatrix _ _).matrix_det

theorem continuous_toMK {n : ℕ} (ε : Fin n → Bool) : Continuous fun k : Formalism.REAL.KG ε => Formalism.REAL.toMK k :=
  ((Formalism.REAL.isClosedEmbeddingMatrix n ε).1.isEmbedding.comp Topology.IsEmbedding.subtypeVal).continuous

variable {D : D7}

theorem unframe_mem {W : HSp D} {S' : D.what₂.Tau → SPar} (M' : DSModel W S') (τ : D.what₂.Tau)
    {k : Matrix (Fin W.rank) (Fin W.rank) ℂ} (hk : k ∈ Formalism.REAL.Kset (M'.ε τ)) :
    (M'.fr τ)⁻¹ * k * M'.fr τ ∈ Formalism.QuantumDeterminants.UH (gramAt D W τ) := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M'.fr_unit τ)
  have hJ : kᴴ * Formalism.REAL.Jm (M'.ε τ) * k = Formalism.REAL.Jm (M'.ε τ) := (Formalism.REAL.maximal_compact_facts _ _).1 k hk
  have hJ' : ∀ A : Matrix (Fin W.rank) (Fin W.rank) ℂ,
      kᴴ * (Formalism.REAL.Jm (M'.ε τ) * (k * A)) = Formalism.REAL.Jm (M'.ε τ) * A := fun A => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hJ]
  have e1 : ((M'.fr τ)⁻¹)ᴴ * (M'.fr τ)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hd]; simp
  have e2 : ∀ A : Matrix (Fin W.rank) (Fin W.rank) ℂ, ((M'.fr τ)⁻¹)ᴴ * ((M'.fr τ)ᴴ * A) = A := fun A => by
    rw [← Matrix.mul_assoc, e1, Matrix.one_mul]
  change ((M'.fr τ)⁻¹ * k * M'.fr τ)ᴴ * gramAt D W τ * ((M'.fr τ)⁻¹ * k * M'.fr τ) = gramAt D W τ
  rw [← M'.fr_gram τ]
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc, e2, Matrix.mul_nonsing_inv_cancel_left _ _ hd, hJ']

theorem elt_mul {θ : InfFam D} (hθ : IsInfFam θ) {W : HSp D} {S' : D.what₂.Tau → SPar} (M' : DSModel W S')
    (τ : D.what₂.Tau) {a b : Matrix (Fin W.rank) (Fin W.rank) ℂ} (ha : a ∈ Formalism.REAL.Kset (M'.ε τ))
    (hb : b ∈ Formalism.REAL.Kset (M'.ε τ)) : elt θ M' τ (a * b) = elt θ M' τ a * elt θ M' τ b := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M'.fr_unit τ)
  rw [elt, elt, elt, ← atTau_mul hθ W τ (unframe_mem M' τ ha) (unframe_mem M' τ hb)]
  simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hd]

theorem elt_one' {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)
    (τ : D.what₂.Tau) : elt θ M τ 1 = 1 := by
  rw [elt, Matrix.mul_one, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)), atTau_one hθ]

theorem coefCont_subst {G : Type} [TopologicalSpace G] {a b : ℕ} (τ : D.what₂.Tau) (ε : Fin a → Bool)
    (ε' : Fin b → Bool) (g : Matrix (Fin a) (Fin a) ℂ) {k : G → Matrix (Fin b) (Fin b) ℂ} (hk : Continuous k)
    (P : PolF D b a) : CoefCont fun x => subst τ ε ε' g (k x) P := by
  unfold subst
  refine CoefCont.aeval (fun v => ?_) P
  split_ifs
  all_goals first
    | exact CoefCont.const _
    | refine CoefCont.sum fun l => CoefCont.sum fun m => CoefCont.smul ?_ (CoefCont.const _)
  · exact (hk.matrix_elem _ _).mul continuous_const
  · exact ((hk.matrix_elem _ _).mul continuous_const).star

theorem fock_orbit_coefFam : ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (f : WO V W → ℂ) (τ : D.what₂.Tau) (aS aT : ℚ), IsInfFam θ → Function.Injective (ptOf ψ θ M M' f) → GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.CompactFock ψ θ M M' ω f τ aS aT → ∀ φ : PolF D W.rank V.rank, ∃ (n : ℕ) (φs : Fin n → PolF D W.rank V.rank) (c : Fin n → Formalism.REAL.KG (M'.ε τ) → ℂ), IsCoefFam c ∧ ∀ k, ω (1, GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.elt θ M' τ (Formalism.REAL.toMK k)) (ptOf ψ θ M M' f φ) = ptOf ψ θ M M' f (∑ i, c i k • φs i) := by
  intro D V W S S' M M' θ ψ ω f τ aS aT hθ hpt hC φ
  obtain ⟨x, y, -, -, hc⟩ := hC
  let pt : PolF D W.rank V.rank →ₗ[ℂ] (WO V W → ℂ) := pureTensorO ψ θ V W (cart M) (cart M') (onb M) (onb M') f
  have hp : ptOf ψ θ M M' f = pt := rfl
  rw [hp] at hpt hc ⊢
  let s : Formalism.REAL.KG (M'.ε τ) → ℂ := fun k => signBlockDeterminant (M.ε τ) true 1 ^ x true * signBlockDeterminant (M.ε τ) false 1 ^ x false *
    (signBlockDeterminant (M'.ε τ) true (Formalism.REAL.toMK k) ^ y true * signBlockDeterminant (M'.ε τ) false (Formalism.REAL.toMK k) ^ y false)
  let ρ : Formalism.REAL.KG (M'.ε τ) → Module.End ℂ (PolF D W.rank V.rank) := fun k =>
    s k • (subst τ (M.ε τ) (M'.ε τ) ((1 : Matrix (Fin V.rank) (Fin V.rank) ℂ).map (starRingEnd ℂ))
      (Formalism.REAL.toMK k)).toLinearMap
  have key : ∀ k P, ω (1, elt θ M' τ (Formalism.REAL.toMK k)) (pt P) = pt (ρ k P) := fun k P => by
    have := hc 1 ⟨one_mem _, by rw [Matrix.one_mul, Matrix.mul_one]⟩ (Formalism.REAL.toMK k) k.2 P
    rw [elt_one' hθ, ← map_smul] at this
    exact this
  have hz : ∀ e, Continuous fun k : Formalism.REAL.KG (M'.ε τ) => signBlockDeterminant (M'.ε τ) e (Formalism.REAL.toMK k) ^ y e := fun e =>
    ((continuous_signBlockDeterminant _ e).comp (continuous_toMK _)).zpow₀ _ fun k => Or.inl (signBlockDeterminant_ne_zero_of_mem_maxCompact e k.2)
  have hs : Continuous s := continuous_const.mul ((hz true).mul (hz false))
  obtain ⟨n, φs, c, h1, h2⟩ := exists_coefFam ρ (fun a b P => hpt (by
      have e : Formalism.REAL.toMK (a * b) = Formalism.REAL.toMK a * Formalism.REAL.toMK b := rfl
      rw [← key, ← key, ← key, e, elt_mul hθ M' τ a.2 b.2, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk,
        mul_one]))
    (fun a P => (MvPolynomial.totalDegree_smul_le _ _).trans
      (GlobalTheory.Chain.RealIt.SubstDeg.totalDegree_subst_le _ _ _ _ _ _ _ _ _))
    (fun P => CoefCont.smul hs (coefCont_subst τ _ _ _ (continuous_toMK _) P)) φ
  exact ⟨n, φs, c, h1, fun k => by rw [key, h2]⟩

end GlobalTheory.Chain.IoLift.FockOrbit

end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix MeasureTheory GlobalTheory.Chain GlobalTheory.Chain.RealIt
open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension (kFin KVec KMap maxCpt rep_mem_kFin)
open scoped TensorProduct InnerProductSpace Classical
open GlobalTheory.Chain.IoLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain.IoLift

open Formalism.REAL in

theorem kMean_translate {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) {n : ℕ}
    (c : Fin n → KG (M.ε τ) → ℂ) (hc : IsCoefFam c) (w : M.H τ) (i : Fin n) (k₀ : KG (M.ε τ)) :
    ∃ d : Fin n → ℂ, M.σ τ (toMK k₀) (kMean M τ (c i) w) = ∑ j, d j • kMean M τ (c j) w := by
  have hds := M.ds τ
  have : CompleteSpace (M.H τ) := hds.1
  obtain ⟨⟨-, hmul⟩, -, hcont⟩ := hds.2.2.1
  have hmem : ∀ k : KG (M.ε τ), toMK k ∈ Formalism.MainNotions.S.UJset (M.ε τ) := fun k => (k : UJ (M.ε τ)).2
  have hcK : Continuous fun k : KG (M.ε τ) => M.σ τ (toMK k) w :=
    (hcont w).comp_continuous (Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)) hmem
  have hint : ∀ j, Integrable (fun k => c j k • M.σ τ (toMK k) w) (muK (M.ε τ)) := fun j =>
    ((hc.1 j).smul hcK).integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (Set.subset_univ _))
  have hm : ∀ k : KG (M.ε τ), M.σ τ (toMK (k₀ * k)) = (M.σ τ (toMK k₀)).comp (M.σ τ (toMK k)) :=
    fun k => hmul _ (hmem k₀) _ (hmem k)
  obtain ⟨d, hd⟩ := hc.2 k₀⁻¹ i
  refine ⟨d, ?_⟩
  unfold kMean
  calc M.σ τ (toMK k₀) (∫ k, c i k • M.σ τ (toMK k) w ∂muK (M.ε τ))
      = ∫ k, M.σ τ (toMK k₀) (c i k • M.σ τ (toMK k) w) ∂muK (M.ε τ) :=
        (ContinuousLinearMap.integral_comp_comm _ (hint i)).symm
    _ = ∫ k, (fun x => c i (k₀⁻¹ * x) • M.σ τ (toMK x) w) (k₀ * k) ∂muK (M.ε τ) := by
        congr 1
        funext k
        simp only [inv_mul_cancel_left, ContinuousLinearMap.map_smul, hm k]
        rfl
    _ = ∫ k, c i (k₀⁻¹ * k) • M.σ τ (toMK k) w ∂muK (M.ε τ) :=
        integral_mul_left_eq_self (μ := muK (M.ε τ)) (fun x => c i (k₀⁻¹ * x) • M.σ τ (toMK x) w) k₀
    _ = ∑ j, d j • ∫ k, c j k • M.σ τ (toMK k) w ∂muK (M.ε τ) := by
        simp only [hd, Finset.sum_smul, mul_smul]
        have hs : ∀ j ∈ (Finset.univ : Finset (Fin n)),
            Integrable (fun k => d j • c j k • M.σ τ (toMK k) w) (muK (M.ε τ)) := fun j _ => (hint j).smul (d j)
        rw [integral_finsetSum _ hs]
        simp only [integral_smul]

theorem kMean_mem_kFin_of_coefFam : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau)
    (n : ℕ) (c : Fin n → Formalism.REAL.KG (M.ε τ) → ℂ), IsCoefFam c → ∀ (w : M.H τ) (i : Fin n),
    kMean M τ (c i) w ∈ kFin M τ := by
  intro D V S M τ n c hc w i
  unfold GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin
  rw [GlobalTheory.KFiniteVectors.mem_kFiniteVectors]
  refine ⟨Submodule.span ℂ (Set.range fun j => kMean M τ (c j) w),
    FiniteDimensional.span_of_finite ℂ (Set.finite_range _), Submodule.subset_span ⟨i, rfl⟩, ?_⟩
  intro g hg x hx
  rw [← Formalism.REAL.range_toMK] at hg
  obtain ⟨k₀, rfl⟩ := hg
  have hle : Submodule.span ℂ (Set.range fun j => kMean M τ (c j) w) ≤
      (Submodule.span ℂ (Set.range fun j => kMean M τ (c j) w)).comap
        (M.σ τ (Formalism.REAL.toMK k₀) : M.H τ →ₗ[ℂ] M.H τ) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    obtain ⟨d, hd⟩ := kMean_translate M τ c hc w j k₀
    change M.σ τ (Formalism.REAL.toMK k₀) (kMean M τ (c j) w) ∈ Submodule.span ℂ (Set.range fun j => kMean M τ (c j) w)
    rw [hd]
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)
  exact hle hx

end GlobalTheory.Chain.IoLift
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix MeasureTheory GlobalTheory.Chain GlobalTheory.Chain.RealIt
open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension (kFin KVec KMap maxCpt rep_mem_kFin)
open scoped TensorProduct InnerProductSpace Classical
open GlobalTheory.Chain.IoLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Chain.IoLift

theorem it_eq_sum_kMean : ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (pt : PolF D W.rank V.rank → WO V W → ℂ) (It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M), IsItW θ M M' ω pt It → ∀ (τ : D.what₂.Tau) (n : ℕ) (c : Fin n → Formalism.REAL.KG (M'.ε τ) → ℂ) (φ : PolF D W.rank V.rank) (φs : Fin n → PolF D W.rank V.rank) (v : M'.Vec) (u : Fin n → M'.sm τ), (∀ i, Continuous (c i)) → (∀ k, ω (1, GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.elt θ M' τ (Formalism.REAL.toMK k)) (pt φ) = pt (∑ i, c i k • φs i)) → (∀ i, (u i : M'.H τ) = kMean M' τ (c i) (v τ)) → It φ (PiTensorProduct.tprod ℂ v) = ∑ i, It (φs i) (PiTensorProduct.tprod ℂ (Function.update v τ (u i))) := by
  intro D V W S S' M M' θ ω pt It hIt τ n c φ φs v u hc hω hu
  have := (M'.ds τ).1
  have hU := (M'.ds τ).2.2.1
  rw [← sub_eq_zero]
  refine inclT_injective M ?_
  rw [map_zero]
  refine ellT_separates M _ fun w => ?_
  let l : Fin n → (M'.sm τ →ₗ[ℂ] ℂ) := fun i => ellT M w ∘ₗ inclT M ∘ₗ It (φs i) ∘ₗ
    (PiTensorProduct.tprod ℂ (s := fun ρ => M'.sm ρ)).toLinearMap v τ
  have hl : ∀ i x, l i x = ellT M w (inclT M (It (φs i) (PiTensorProduct.tprod ℂ (Function.update v τ x)))) :=
    fun _ _ => rfl
  have hb : ∀ i, ∃ C : ℝ, ∀ x, ‖l i x‖ ≤ C * ‖x‖ := fun i => by
    obtain ⟨C, hC⟩ := hIt.bdd (φs i) w
    refine ⟨C * ∏ ρ ∈ Finset.univ.erase τ, ‖(v ρ : M'.H ρ)‖, fun x => ?_⟩
    rw [hl]
    refine (hC _).trans (le_of_eq ?_)
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ τ), mul_assoc, Function.update_self]
    congr 2
    refine Finset.prod_congr rfl fun ρ hρ => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hρ)]
  choose L hL _ using fun i => exists_extension_norm_eq (M'.sm τ) ((l i).mkContinuousOfExistsBound (hb i))
  have hL' : ∀ i (x : M'.sm τ), L i x = l i x := hL
  have hk : ∀ k : Formalism.REAL.KG (M'.ε τ), Formalism.REAL.toMK k ∈ Formalism.MainNotions.S.UJset (M'.ε τ) :=
    fun k => (Formalism.REAL.maximal_compact_facts _ _).1 _ k.2
  have hcm : Continuous fun k : Formalism.REAL.KG (M'.ε τ) => Formalism.REAL.toMK k :=
    Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hx : Continuous fun k : Formalism.REAL.KG (M'.ε τ) => M'.σ τ (Formalism.REAL.toMK k) (v τ) :=
    (hU.2.2 _).comp_continuous hcm hk
  have hint : ∀ i, Integrable (fun k : Formalism.REAL.KG (M'.ε τ) => c i k • M'.σ τ (Formalism.REAL.toMK k) (v τ))
      (Formalism.REAL.muK (M'.ε τ)) := fun i =>
    integrableOn_univ.1 (((hc i).smul hx).continuousOn.integrableOn_compact isCompact_univ)
  have key : ∀ k : Formalism.REAL.KG (M'.ε τ), ∑ i, L i (c i k • M'.σ τ (Formalism.REAL.toMK k) (v τ)) =
      ellT M w (inclT M (It φ (PiTensorProduct.tprod ℂ v))) := fun k => by
    have hs : M'.σ τ (Formalism.REAL.toMK k) (v τ) ∈ M'.sm τ :=
      (GlobalTheory.SmVec.sm_eq M' τ).ge
        (GlobalTheory.SmVec.sigma_mem (M'.fr_unit τ) (M'.fr_gram τ) hU ((GlobalTheory.SmVec.sm_eq M' τ).le (v τ).2) (hk k))
    have hr : M'.rep τ ((M'.fr τ)⁻¹ * Formalism.REAL.toMK k * M'.fr τ) = M'.σ τ (Formalism.REAL.toMK k) :=
      GlobalTheory.SmVec.trRep_conj (σ := M'.σ τ) (M'.fr_unit τ) _
    have h1 := hIt.invK τ _ (GlobalTheory.SmVec.conj_mem_UH (M'.fr_unit τ) (M'.fr_gram τ) (hk k)) φ _
      (PiTensorProduct.tprod ℂ v) (PiTensorProduct.tprod ℂ (Function.update v τ ⟨_, hs⟩)) (hω k).symm (by
        unfold inclT
        rw [PiTensorProduct.map_tprod, PiTensorProduct.map_tprod, actT_pure, hr]
        congr 1
        funext ρ
        by_cases h : ρ = τ
        · subst h; simp
        · simp [Function.update_of_ne h])
    rw [← h1, map_sum, LinearMap.sum_apply, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, map_smul, LinearMap.smul_apply, map_smul, map_smul, ← hl, ← hL']
  rw [map_sub, map_sub, map_sum, map_sum, sub_eq_zero]
  have h2 : ∀ i, ellT M w (inclT M (It (φs i) (PiTensorProduct.tprod ℂ (Function.update v τ (u i))))) =
      ∫ k, L i (c i k • M'.σ τ (Formalism.REAL.toMK k) (v τ)) ∂(Formalism.REAL.muK (M'.ε τ)) := fun i => by
    rw [← hl, ← hL', hu, kMean, (L i).integral_comp_comm (hint i)]
  simp only [h2]
  rw [← integral_finsetSum _ fun i _ => (L i).integrable_comp (hint i)]
  simp only [key]
  simp

end GlobalTheory.Chain.IoLift

end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix MeasureTheory GlobalTheory.Chain GlobalTheory.Chain.RealIt
open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension (kFin KVec KMap maxCpt rep_mem_kFin)
open scoped TensorProduct InnerProductSpace Classical

namespace GlobalTheory.Chain.IoLift

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Algebra

variable {ι : Type} {P Y K : ι → Type} [∀ i, AddCommGroup (P i)] [∀ i, Module ℂ (P i)] [∀ i, AddCommGroup (Y i)]
  [∀ i, Module ℂ (Y i)] [∀ i, AddCommGroup (K i)] [∀ i, Module ℂ (K i)] {Z : Type} [AddCommGroup Z] [Module ℂ Z]

def slice (B : MultilinearMap ℂ P (MultilinearMap ℂ Y Z)) (i : ι) (p : ∀ j, P j) (y : ∀ j, Y j) :
    P i →ₗ[ℂ] Y i →ₗ[ℂ] Z :=
  LinearMap.mk₂ ℂ (fun x z => B (Function.update p i x) (Function.update y i z)) (fun _ _ _ => by simp)
    (fun _ _ _ => by simp) (fun _ _ _ => by simp) fun _ _ _ => by simp

theorem slice_apply (B : MultilinearMap ℂ P (MultilinearMap ℂ Y Z)) (i : ι) (p : ∀ j, P j) (y : ∀ j, Y j) (x : P i)
    (z : Y i) : slice B i p y x z = B (Function.update p i x) (Function.update y i z) := rfl

def IsContr (i : ι) (L : (⨂[ℂ] j, K j) →ₗ[ℂ] K i) : Prop := ∀ f : Module.End ℂ (K i), L ∘ₗ intersection_update_fsHerm_neg_one i f = f ∘ₗ L

variable [Fintype ι]

theorem eq_zero_of_isContr (i : ι) {x : ⨂[ℂ] j, K j} (h : ∀ L, IsContr i L → L x = 0) : x = 0 := by
  obtain ⟨z, rfl⟩ := GlobalTheory.Chain.IoLift.mem_range_map_subtype_of_contr ι K (fun j => if j = i then ⊥ else ⊤) x fun j L hL => by
    by_cases e : j = i
    · subst e; rw [if_pos rfl, h L hL]; exact zero_mem _
    · rw [if_neg e]; trivial
  refine LinearMap.congr_fun (g := 0) (PiTensorProduct.ext (MultilinearMap.ext fun v => ?_)) z
  have := (v i).2
  simp only [if_true, Submodule.mem_bot] at this
  simp only [LinearMap.compMultilinearMap_apply, PiTensorProduct.map_tprod, LinearMap.zero_apply]
  exact MultilinearMap.map_coord_zero _ i this

theorem exists_factor {G : ι → Type} (c : ∀ i, G i → Module.End ℂ (P i)) (a : ∀ i, G i → Module.End ℂ (K i))
    (ha : ∀ i, AbsIrr (a i)) (I : MultilinearMap ℂ P (MultilinearMap ℂ Y (⨂[ℂ] j, K j)))
    (B : MultilinearMap ℂ P (MultilinearMap ℂ Y Z)) (h0 : ∃ p y, I p y ≠ 0)
    (he : ∀ i g p y, I (Function.update p i (c i g (p i))) y = intersection_update_fsHerm_neg_one i (a i g) (I p y))
    (hk : ∀ i L, IsContr i L → ∀ p y, (slice I i p y).compr₂ L ≠ 0 →
      (∀ L', IsContr i L' → ∀ p' y', KerLe (fun x z => (slice I i p y).compr₂ L x z)
        fun x z => (slice I i p' y').compr₂ L' x z) ∧
      ∀ p' y', KerLe (fun x z => (slice I i p y).compr₂ L x z) fun x z => slice B i p' y' x z) :
    (∃ T : (⨂[ℂ] j, K j) →ₗ[ℂ] Z, ∀ p y, T (I p y) = B p y) ∧ Submodule.span ℂ {x | ∃ p y, I p y = x} = ⊤ := by
  obtain ⟨p₀, y₀, h0⟩ := h0
  have h1 : ∀ i, ∃ L, IsContr i L ∧ L (I p₀ y₀) ≠ 0 := fun i => by
    by_contra hn
    exact h0 (eq_zero_of_isContr i fun L hL => by_contra fun h => hn ⟨L, hL, h⟩)
  choose L hL hL0 using h1
  let A : ∀ i, P i →ₗ[ℂ] Y i →ₗ[ℂ] K i := fun i => (slice I i p₀ y₀).compr₂ (L i)
  have hA0 : ∀ i, A i (p₀ i) (y₀ i) ≠ 0 := fun i => by
    simpa only [A, LinearMap.compr₂_apply, slice_apply, Function.update_eq_self] using hL0 i
  have hA : ∀ i, A i ≠ 0 := fun i e => hA0 i (by rw [e]; rfl)
  have hAe : ∀ i g x z, A i (c i g x) z = a i g (A i x z) := fun i g x z => by
    have := he i g (Function.update p₀ i x) (Function.update y₀ i z)
    rw [Function.update_idem, Function.update_self] at this
    simp only [A, LinearMap.compr₂_apply, slice_apply, this]
    exact LinearMap.congr_fun (hL i (a i g)) _
  have hAs : ∀ i, Submodule.span ℂ {x | ∃ p y, A i p y = x} = ⊤ := fun i => by
    refine ((ha i).1 _ fun g x hx => ?_).resolve_left fun e => hA0 i (Submodule.span_eq_bot.1 e _ ⟨_, _, rfl⟩)
    refine Submodule.mem_comap.1 ((Submodule.span_le (p := Submodule.comap (a i g) _)).2 ?_ hx)
    rintro _ ⟨p, y, rfl⟩
    exact Submodule.subset_span ⟨_, _, hAe i g p y⟩
  obtain ⟨hs, hf⟩ := GlobalTheory.Chain.IoLift.Factor.factor ι K P Y A hAs
  obtain ⟨T, hT⟩ := hf Z B fun i => (hk i (L i) (hL i) p₀ y₀ (hA i)).2
  obtain ⟨Φ, hΦ⟩ := hf _ I fun i p y n x z h => eq_zero_of_isContr i fun L' hL' => by
    rw [map_sum]
    exact (hk i (L i) (hL i) p₀ y₀ (hA i)).1 L' hL' p y n x z h
  obtain ⟨r, hr⟩ := GlobalTheory.Chain.IoLift.Scal.scalar_of_comm ι K G a ha Φ fun i g => by
    refine LinearMap.ext_on hs ?_
    rintro _ ⟨p, y, rfl⟩
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hΦ, ← he, ← hΦ, position_tprod]
    congr 2
    funext j
    by_cases e : j = i
    · subst e; simp [hAe]
    · simp [e]
  have hI : ∀ p y, I p y = r • PiTensorProduct.tprod ℂ fun i => A i (p i) (y i) := fun p y => by
    rw [← hΦ, hr]; rfl
  have hr0 : r ≠ 0 := fun e => h0 (by rw [hI, e, zero_smul])
  refine ⟨⟨r⁻¹ • T, fun p y => ?_⟩, eq_top_iff.2 (hs ▸ Submodule.span_le.2 ?_)⟩
  · rw [hI, map_smul, LinearMap.smul_apply, smul_smul, mul_inv_cancel₀ hr0, one_smul, hT]
  · rintro _ ⟨p, y, rfl⟩
    rw [SetLike.mem_coe, ← Submodule.smul_mem_iff _ hr0, ← hI]
    exact Submodule.subset_span ⟨p, y, rfl⟩

end Algebra

open GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix GlobalTheory.PointAtPlaceHom

variable {D : D7} {V W : HSp D} {S S' : D.what₂.Tau → SPar}

theorem exists_local {X : ProvA} (hX : ChosenSeries X) (h3 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisUpDownLine X) (h5 : GlobalTheory.Published.HarishChandraModules)
    (hB : ModelsAreCoverSeries D) (M : DSModel V S) (M' : DSModel W S') (τ : D.what₂.Tau) {t : ℕ}
    {al be ga de : List ℚ} (hd : Formalism.MainNotions.SchurIrreducible.DataAR t al be ga de) {aS aT : ℚ}
    (hS : S τ = dualPar (signed (al ++ be) (ga ++ de) aT))
    (hS' : S' τ = dualPar (signed (al ++ block t ++ de) (ga ++ be) aS)) :
    (kFin M τ ≤ M.sm τ ∧ kFin M' τ ≤ M'.sm τ) ∧ ∃ a a', IsKAct M τ a ∧ IsKAct M' τ a' ∧
      AbsIrr (fun X : lieAt V τ => a X) ∧ LocKer M M' τ aS aT a' := by
  obtain ⟨-, p1, p2, -⟩ := GlobalTheory.LowestTypes.lowest_types t al be ga de hd.1
  have ht := hd.1.1
  have hn := hd.1.2.1
  obtain ⟨⟨e, he⟩, m, hm, hU⟩ := hB.1 X V S M τ (al.length + be.length) (ga.length + de.length) _ _ aT
    ⟨by omega, by simp, by simp, p1, hX _ _ _ p1, hS⟩
  obtain ⟨⟨e', he'⟩, m', hm', hU'⟩ := hB.2 X W S' M' τ (al.length + de.length + t) (ga.length + be.length) _ _ aS
    ⟨by omega, by simp [block]; omega, by simp, p2, hX _ _ _ p2, hS'⟩
  obtain ⟨U, hU⟩ := hU e he
  obtain ⟨U', hU'⟩ := hU' e' he'
  obtain ⟨κ, hκ⟩ := PolyIso.exists_isPolyIso _ _ _ _ _ _ _ _ e e' he he'
  obtain ⟨s, a, ha⟩ := GlobalTheory.Chain.IoLift.kFin_smooth_isKAct D V S M τ _ _ _ _ _ _ _ hU
  obtain ⟨s', a', ha'⟩ := GlobalTheory.Chain.IoLift.kFin_smooth_isKAct D W S' M' τ _ _ _ _ _ _ _ hU'
  have i1 := GlobalTheory.SmallerSource.discrete_series_gk_admissible_irreducible X (h5.admQ5_of_harishChandraModules X) (by omega) (lamA al be ga de)
  have i2 := GlobalTheory.SmallerSource.discrete_series_gk_admissible_irreducible X (h5.admQ5_of_harishChandraModules X) (by omega) (lamA' t al be ga de)
  refine ⟨⟨s, s'⟩, a, a', ha, ha', GlobalTheory.KFinIrr.absIrr_kFin D V S M τ _ _ _ _ _ m U.toLinearEquiv a hU i1.2 i1.1 ha, ?_⟩
  exact GlobalTheory.Chain.IoLift.KerTransfer.locKer_of_coverKer D V W S S' M M' τ _ _ _ _ _ _ _ _ e e' m m' aS aT U U' κ a' hm' hU hU' hκ ha'
    (GlobalTheory.Chain.IoLift.CoverKernel.coverKer_of_down X _ _ _ _ _ _ (h3.1 t al be ga de hd).2.1 i1.2 (GlobalTheory.Chain.IoLift.UImg.unitaryImage _ _ _ _)
      (GlobalTheory.Chain.IoLift.finiteSupport_of_admissible _ _ _ _ _ _ i2.1) GlobalTheory.Chain.IoLift.TensorFormProof.tensorForm)

variable {M : DSModel V S} {M' : DSModel W S'}

theorem frame_mem (M : DSModel V S) (τ : D.what₂.Tau) {k : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hk : k ∈ Formalism.REAL.Kset (M.ε τ)) : (M.fr τ)⁻¹ * k * M.fr τ ∈ maxCpt M τ := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  change M.fr τ * ((M.fr τ)⁻¹ * k * M.fr τ) * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ)
  rwa [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ hd, Matrix.mul_nonsing_inv_cancel_left _ _ hd]

theorem mem_range_inclK (h : KSm M) (x : SmT M)
    (hx : ∀ τ, ∃ E : Submodule ℂ (⨂[ℂ] τ, M.H τ), FiniteDimensional ℂ E ∧
      ∀ k ∈ maxCpt M τ, actT M τ k (inclT M x) ∈ E) : x ∈ LinearMap.range (inclK h) := by
  obtain ⟨z, hz⟩ := GlobalTheory.Chain.IoLift.mem_range_map_subtype_of_contr _ M.H (kFin M) (inclT M x) fun τ L hL => by
    obtain ⟨E, hE, hk⟩ := hx τ
    have hle : Submodule.span ℂ ((fun k => M.σ τ k (L (inclT M x))) '' Formalism.REAL.Kset (M.ε τ)) ≤ E.map L := by
      rw [Submodule.span_le]
      rintro _ ⟨k, hk', rfl⟩
      refine ⟨_, hk _ (frame_mem M τ hk'), (LinearMap.congr_fun (hL (M.rep τ _ : M.H τ →ₗ[ℂ] M.H τ)) _).trans ?_⟩
      exact congrArg (fun A : M.H τ →L[ℂ] M.H τ => A _) (GlobalTheory.SmVec.trRep_conj (σ := M.σ τ) (M.fr_unit τ) k)
    have hσ := (M.ds τ).2.2.1
    have hJ := (Formalism.REAL.maximal_compact_facts _ (M.ε τ)).1
    refine ⟨_, Submodule.finiteDimensional_of_le hle, Submodule.subset_span ⟨1, ⟨one_mem _, by simp⟩, ?_⟩,
      fun g hg v hv => ?_⟩
    · simp only [hσ.1.1]; rfl
    · refine Submodule.mem_comap.1 ((Submodule.span_le (p := Submodule.comap (M.σ τ g : M.H τ →ₗ[ℂ] M.H τ) _)).2 ?_ hv)
      rintro _ ⟨k, hk', rfl⟩
      refine Submodule.subset_span ⟨g * k, Formalism.REAL.Kset_mul _ hg hk', ?_⟩
      simp only [hσ.1.2 g (hJ g hg) k (hJ k hk')]; rfl
  refine ⟨z, (tensorLaw D V S M).inj (Eq.trans ?_ hz)⟩
  rw [inclT, inclK, ← LinearMap.comp_apply, ← PiTensorProduct.map_comp]
  rfl

theorem derT_unique {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} {x y y' : SmT M} (h : DerT M τ X x y)
    (h' : DerT M τ X x y') : y = y' := by
  refine (tensorLaw D V S M).inj (sub_eq_zero.1 ((tensorLaw D V S M).sep _ fun w => ?_))
  rw [map_sub, (h w).unique (h' w), sub_self]

theorem mem_span_of_average {P Z : Type} [AddCommGroup P] [Module ℂ P] [AddCommGroup Z] [Module ℂ Z]
    (G : P →ₗ[ℂ] SmT M →ₗ[ℂ] Z) (h : KSm M)
    (hs : ∀ τ φ (v : M.Vec), ∃ (n : ℕ) (φs : Fin n → P) (u : Fin n → M.sm τ), (∀ i, (u i : M.H τ) ∈ kFin M τ) ∧
      G φ (PiTensorProduct.tprod ℂ v) = ∑ i, G (φs i) (PiTensorProduct.tprod ℂ (Function.update v τ (u i))))
    (φ : P) (x : SmT M) : G φ x ∈ Submodule.span ℂ {z | ∃ φ y, G φ (inclK h y) = z} := by
  have key : ∀ (s : Finset D.what₂.Tau) φ (v : M.Vec), (∀ τ ∉ s, (v τ : M.H τ) ∈ kFin M τ) →
      G φ (PiTensorProduct.tprod ℂ v) ∈ Submodule.span ℂ {z | ∃ φ y, G φ (inclK h y) = z} := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      refine fun φ v hv => Submodule.subset_span ⟨φ, PiTensorProduct.tprod ℂ fun τ => ⟨v τ, hv τ (by simp)⟩, ?_⟩
      rw [inclK, PiTensorProduct.map_tprod]
      rfl
    | insert τ s _ ih =>
      intro φ v hv
      obtain ⟨n, φs, u, hu, e⟩ := hs τ φ v
      rw [e]
      refine sum_mem fun i _ => ih _ _ fun ρ hρ => ?_
      by_cases e : ρ = τ
      · subst e; rw [Function.update_self]; exact hu i
      · rw [Function.update_of_ne e]; exact hv ρ (by simp [e, hρ])
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r v => rw [map_smul]; exact Submodule.smul_mem _ _ (key Finset.univ φ v (by simp))
  | add a b ha hb => rw [map_add]; exact add_mem ha hb

def glueM (D : D7) (a b : ℕ) : MultilinearMap ℂ (fun _ : D.what₂.Tau => LPol b a) (PolF D b a) :=
  (MultilinearMap.mkPiAlgebra ℂ D.what₂.Tau (PolF D b a)).compLinearMap fun τ =>
    (MvPolynomial.rename (fun s => (τ, s)) : LPol b a →ₐ[ℂ] PolF D b a).toLinearMap

theorem glueM_apply {a b : ℕ} (p : D.what₂.Tau → LPol b a) : glueM D a b p = glue p := rfl

theorem srcOp_glue (τ : D.what₂.Tau) (aT : ℚ) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (p : D.what₂.Tau → LPol W.rank V.rank) :
    srcOp M M' τ aT X (glue p) = glue (Function.update p τ (sOp M M' τ aT X (p τ))) := by
  simp only [srcOp, sOp, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
    ((GlueProof.glueLaw D _ _).2 τ _ _ p).1]
  simp only [← glueM_apply, MultilinearMap.map_update_add,
    MultilinearMap.map_update_smul, Function.update_eq_self]

theorem tgtOp_glue (τ : D.what₂.Tau) (aS : ℚ) (Y : Matrix (Fin W.rank) (Fin W.rank) ℂ)
    (p : D.what₂.Tau → LPol W.rank V.rank) :
    tgtOp M M' τ aS Y (glue p) = glue (Function.update p τ (tOp M M' τ aS Y (p τ))) := by
  simp only [tgtOp, tOp, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
    ((GlueProof.glueLaw D _ _).2 τ _ _ p).2]
  simp only [← glueM_apply, MultilinearMap.map_update_add,
    MultilinearMap.map_update_smul, Function.update_eq_self]

def multi {Z : Type} [AddCommGroup Z] [Module ℂ Z] (A : PolF D W.rank V.rank →ₗ[ℂ] KT M' →ₗ[ℂ] Z) :
    MultilinearMap ℂ (fun _ : D.what₂.Tau => LPol W.rank V.rank) (MultilinearMap ℂ (fun τ => kFin M' τ) Z) :=
  (PiTensorProduct.lift.symm.toLinearMap ∘ₗ A).compMultilinearMap (glueM D _ _)

theorem multi_apply {Z : Type} [AddCommGroup Z] [Module ℂ Z] (A : PolF D W.rank V.rank →ₗ[ℂ] KT M' →ₗ[ℂ] Z)
    (p : D.what₂.Tau → LPol W.rank V.rank) (y : KVec M') : multi A p y = A (glue p) (PiTensorProduct.tprod ℂ y) := rfl

theorem span_multi {Z : Type} [AddCommGroup Z] [Module ℂ Z] (A : PolF D W.rank V.rank →ₗ[ℂ] KT M' →ₗ[ℂ] Z)
    (h : ∀ p y, A (glue p) (PiTensorProduct.tprod ℂ y) = 0) : A = 0 :=
  LinearMap.ext_on (GlueProof.glueLaw D _ _).1 (by
    rintro _ ⟨p, rfl⟩
    exact PiTensorProduct.ext (MultilinearMap.ext (h p)))

theorem inclK_injective (h : KSm M) : Function.Injective (inclK h) := by
  choose g hg using fun τ => LinearMap.exists_leftInverse_of_injective _ (Submodule.ker_inclusion _ _ (h τ))
  refine Function.LeftInverse.injective (g := PiTensorProduct.map g) fun x => ?_
  rw [inclK, ← LinearMap.comp_apply, ← PiTensorProduct.map_comp, funext hg, PiTensorProduct.map_id]
  rfl

theorem inclK_tprod (h : KSm M) (u : KVec M) :
    inclK h (PiTensorProduct.tprod ℂ u) = PiTensorProduct.tprod ℂ fun τ => (⟨u τ, h τ (u τ).2⟩ : M.sm τ) := by
  rw [inclK, PiTensorProduct.map_tprod]
  rfl

theorem inclK_update (h : KSm M) (u : KVec M) (τ : D.what₂.Tau) (w : kFin M τ) :
    inclK h (PiTensorProduct.tprod ℂ (Function.update u τ w)) = PiTensorProduct.tprod ℂ
      (Function.update (fun τ => (⟨u τ, h τ (u τ).2⟩ : M.sm τ)) τ ⟨w, h τ w.2⟩) := by
  rw [inclK_tprod]
  congr 1
  funext ρ
  by_cases e : ρ = τ
  · subst e; simp
  · simp [e]

theorem exists_factor_kFin (hdec : GlobalTheory.Published.CuspDecaySobolev) {θ : InfFam D} (hθ : IsInfFam θ)
    {aS aT : D.what₂.Tau → ℚ} {a : ∀ τ, Matrix (Fin V.rank) (Fin V.rank) ℂ → Module.End ℂ (kFin M τ)}
    {a' : ∀ τ, Matrix (Fin W.rank) (Fin W.rank) ℂ → Module.End ℂ (kFin M' τ)} (ha : ∀ τ, IsKAct M τ (a τ))
    (hirr : ∀ τ, AbsIrr fun X : lieAt V τ => a τ X) (hker : ∀ τ, LocKer M M' τ (aS τ) (aT τ) (a' τ))
    (I : PolF D W.rank V.rank →ₗ[ℂ] KT M' →ₗ[ℂ] KT M) (B : PolF D W.rank V.rank →ₗ[ℂ] KT M' →ₗ[ℂ] (GA D V → ℂ))
    (h0 : I ≠ 0) (hIs : ∀ τ, ∀ X ∈ lieAt V τ, ∀ φ y, I (srcOp M M' τ (aT τ) X φ) y = intersection_update_fsHerm_neg_one τ (a τ X) (I φ y))
    (hIt : ∀ τ, ∀ Y ∈ lieAt W τ, ∀ φ y, I (tgtOp M M' τ (aS τ) Y φ) y + I φ (intersection_update_fsHerm_neg_one τ (a' τ Y) y) = 0)
    (hBg : ∀ φ y, IsCuspGrow θ V (B φ y))
    (hBs : ∀ τ, ∀ X ∈ lieAt V τ, ∀ φ y, B (srcOp M M' τ (aT τ) X φ) y = Rder θ V τ X (B φ y))
    (hBt : ∀ τ, ∀ Y ∈ lieAt W τ, ∀ φ (y : KVec M'), B (tgtOp M M' τ (aS τ) Y φ) (PiTensorProduct.tprod ℂ y) +
      B φ (intersection_update_fsHerm_neg_one τ (a' τ Y) (PiTensorProduct.tprod ℂ y)) = 0) :
    (∃ T : KT M →ₗ[ℂ] (GA D V → ℂ), ∀ φ y, T (I φ y) = B φ y) ∧ Submodule.span ℂ {x | ∃ φ y, I φ y = x} = ⊤ := by
  obtain ⟨μ, 𝓕, hμ, h𝓕⟩ := GlobalTheory.Ker.HypModel.exists_haar_fundDom D V
  obtain ⟨E, hE0, hE⟩ := GlobalTheory.Chain.CuspL2.exists_embedding_skew hdec D θ V μ 𝓕 hθ hμ h𝓕
  have s1 : ∀ τ X (p : D.what₂.Tau → LPol W.rank V.rank) x, glue (Function.update p τ (sOp M M' τ (aT τ) X x)) =
      srcOp M M' τ (aT τ) X (glue (Function.update p τ x)) := fun τ X p x => by
    rw [srcOp_glue, Function.update_idem, Function.update_self]
  have s2 : ∀ τ Y (p : D.what₂.Tau → LPol W.rank V.rank) x, glue (Function.update p τ (tOp M M' τ (aS τ) Y x)) =
      tgtOp M M' τ (aS τ) Y (glue (Function.update p τ x)) := fun τ X p x => by
    rw [tgtOp_glue, Function.update_idem, Function.update_self]
  have s3 : ∀ τ (A : Module.End ℂ (kFin M' τ)) (y : KVec M') z, PiTensorProduct.tprod ℂ (Function.update y τ (A z)) =
      intersection_update_fsHerm_neg_one τ A (PiTensorProduct.tprod ℂ (Function.update y τ z)) := fun τ A y z => by
    rw [position_tprod, Function.update_idem, Function.update_self]
  have pI : ∀ τ L, IsContr τ L → ∀ p y,
      IsLocPair M M' τ (aS τ) (aT τ) (a' τ) ((slice (multi I) τ p y).compr₂ L) := fun τ L hL p y => by
    refine ⟨fun X hX P P' z z' => ?_, fun Y hY P z => ?_⟩
    · have hL' := fun x => LinearMap.congr_fun (hL (a τ X)) x
      simp only [LinearMap.comp_apply] at hL'
      simp only [LinearMap.compr₂_apply, slice_apply, multi_apply, s1, hIs τ X hX, hL']
      exact (ha τ).skew X hX _ _
    · simp only [LinearMap.compr₂_apply, slice_apply, multi_apply, s2, s3]
      rw [← map_add, hIt τ Y hY, map_zero]
  have pB : ∀ τ p y, IsLocPair M M' τ (aS τ) (aT τ) (a' τ) ((slice (multi B) τ p y).compr₂ E) := fun τ p y => by
    refine ⟨fun X hX P P' z z' => ?_, fun Y hY P z => ?_⟩
    · simp only [LinearMap.compr₂_apply, slice_apply, multi_apply, s1, hBs τ X hX]
      exact hE τ X hX _ _ (hBg _ _) (hBg _ _) (hBs τ X hX _ _ ▸ hBg _ _) (hBs τ X hX _ _ ▸ hBg _ _)
    · simp only [LinearMap.compr₂_apply, slice_apply, multi_apply, s2, s3]
      rw [← map_add, hBt τ Y hY, map_zero]
  obtain ⟨⟨T, hT⟩, hs⟩ := exists_factor (fun τ (X : lieAt V τ) => sOp M M' τ (aT τ) X) _ hirr (multi I) (multi B)
    (by by_contra hn; exact h0 (span_multi I fun p y => by_contra fun h => hn ⟨p, y, h⟩))
    (fun τ X p y => by rw [multi_apply, multi_apply, ← srcOp_glue, hIs τ X X.2])
    fun τ L hL p y hne => ⟨fun L' hL' p' y' => hker τ _ _ _ _ (pI τ L hL p y) (pI τ L' hL' p' y') hne,
      fun p' y' n x z h => by
        refine (hE0 _ (GlobalTheory.Chain.CuspGrowSpace.isCuspGrow_of_mem_span D θ V _ (sum_mem fun i _ => Submodule.subset_span (hBg _ _)))).2 ?_
        rw [map_sum]
        exact hker τ _ _ _ _ (pI τ L hL p y) (pB τ p' y') hne n x z h⟩
  refine ⟨⟨T, fun φ y => ?_⟩, eq_top_iff.2 (hs ▸ Submodule.span_mono ?_)⟩
  · have := span_multi (I.compr₂ T - B) fun p y => sub_eq_zero.2 (hT p y)
    exact sub_eq_zero.1 (LinearMap.congr_fun₂ this φ y)
  · rintro _ ⟨p, y, rfl⟩
    exact ⟨_, _, rfl⟩

theorem exists_mult (hG : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.ExtExists D) (hdec : GlobalTheory.Published.CuspDecaySobolev) {θ : InfFam D}
    (hθ : IsInfFam θ) (h : KSm M) (h' : KSm M')
    {aS aT : D.what₂.Tau → ℚ} {a : ∀ τ, Matrix (Fin V.rank) (Fin V.rank) ℂ → Module.End ℂ (kFin M τ)}
    {a' : ∀ τ, Matrix (Fin W.rank) (Fin W.rank) ℂ → Module.End ℂ (kFin M' τ)} (ha : ∀ τ, IsKAct M τ (a τ))
    (ha' : ∀ τ, IsKAct M' τ (a' τ))
    (hirr : ∀ τ, AbsIrr fun X : lieAt V τ => a τ X) (hker : ∀ τ, LocKer M M' τ (aS τ) (aT τ) (a' τ))
    (It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M) (B : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] (GA D V → ℂ))
    {J : Set (GA D V)} {χ : GA D V → ℂ} (h0 : ∃ φ y, It φ (inclK h' y) ≠ 0)
    (hK : ∀ τ (φ : PolF D W.rank V.rank), ∀ k ∈ maxCpt M τ, ∃ φ' : PolF D W.rank V.rank,
      φ'.totalDegree ≤ φ.totalDegree ∧ ∀ v, inclT M (It φ' v) = actT M τ k (inclT M (It φ v)) ∧
        B φ' v = rTr V (atTau θ V τ k) (B φ v))
    (hIs : ∀ τ, ∀ X ∈ lieAt V τ, ∀ φ v, DerT M τ X (It φ v) (It (srcOp M M' τ (aT τ) X φ) v))
    (hIt : ∀ τ, ∀ Y ∈ lieAt W τ, ∀ φ v v', DerT M' τ Y v v' → It (tgtOp M M' τ (aS τ) Y φ) v + It φ v' = 0)
    (hBg : ∀ φ v, IsCuspGrow θ V (B φ v))
    (hBs : ∀ τ, ∀ X ∈ lieAt V τ, ∀ φ v, B (srcOp M M' τ (aT τ) X φ) v = Rder θ V τ X (B φ v))
    (hBt : ∀ τ, ∀ Y ∈ lieAt W τ, ∀ φ (v : M'.Vec) (w : M'.sm τ), (w : M'.H τ) = dRep (M'.rep τ) Y (v τ) →
      B (tgtOp M M' τ (aS τ) Y φ) (PiTensorProduct.tprod ℂ v) +
        B φ (PiTensorProduct.tprod ℂ (Function.update v τ w)) = 0)
    (hlev : ∀ φ v, ∀ k ∈ J, ∀ g, B φ v (g * k) = χ k * B φ v g) :
    ∃ u ∈ MultT θ M J χ, ∀ φ y, u (It φ (inclK h' y)) = B φ (inclK h' y) := by
  have inj := inclK_injective h
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ (LinearMap.ker_eq_bot.2 inj)
  let I := (It.compl₂ (inclK h')).compr₂ g
  have hI : ∀ φ y, inclK h (I φ y) = It φ (inclK h' y) := fun φ y => by
    obtain ⟨z, hz⟩ := mem_range_inclK h (It φ (inclK h' y)) fun τ =>
      ⟨(MvPolynomial.restrictTotalDegree _ ℂ φ.totalDegree).map (inclT M ∘ₗ It.flip (inclK h' y)), inferInstance,
        fun k hk => by
          obtain ⟨φ', h1, h2⟩ := hK τ φ k hk
          exact ⟨φ', (MvPolynomial.mem_restrictTotalDegree _ _ _).2 h1, (h2 _).1⟩⟩
    change inclK h (g (It φ (inclK h' y))) = _
    rw [← hz, ← LinearMap.comp_apply g, hg, LinearMap.id_apply]
  have hIs' : ∀ τ, ∀ X ∈ lieAt V τ, ∀ φ y, I (srcOp M M' τ (aT τ) X φ) y = intersection_update_fsHerm_neg_one τ (a τ X) (I φ y) :=
    fun τ X hX φ y => inj (by
      rw [hI]
      exact derT_unique (hIs τ X hX φ _) (hI φ y ▸ (GlobalTheory.Chain.IoLift.FinTensor.kFinTensor D V S M τ h).2.1 _ (ha τ) X hX _))
  obtain ⟨⟨T, hT⟩, hs⟩ := exists_factor_kFin hdec hθ ha hirr hker I (B.compl₂ (inclK h'))
    (fun e => by
      obtain ⟨φ, y, h0⟩ := h0
      exact h0 (by rw [← hI, e]; simp)) hIs'
    (fun τ Y hY φ y => inj (by
      rw [map_add, hI, hI, map_zero]
      exact hIt τ Y hY φ _ _ ((GlobalTheory.Chain.IoLift.FinTensor.kFinTensor D W S' M' τ h').2.1 _ (ha' τ) Y hY _)))
    (fun φ y => hBg _ _) (fun τ X hX φ y => hBs τ X hX _ _) fun τ Y hY φ y => by
      rw [LinearMap.compl₂_apply, LinearMap.compl₂_apply, position_tprod, inclK_update, inclK_tprod]
      exact hBt τ Y hY φ _ _ ((ha' τ).der Y hY _).deriv.symm
  simp only [LinearMap.compl₂_apply] at hT
  have hind : ∀ p : KT M → Prop, (∀ φ y, p (I φ y)) → (∀ x y, p x → p y → p (x + y)) → ∀ y, p y := by
    intro p h1 h3 y
    have hy : y ∈ Submodule.span ℂ {x | ∃ φ y, I φ y = x} := hs ▸ Submodule.mem_top
    suffices ∀ c : ℂ, p (c • y) by simpa using this 1
    induction hy using Submodule.span_induction with
    | mem _ h => obtain ⟨P, x, rfl⟩ := h; intro c; rw [← map_smul]; exact h1 _ _
    | zero => intro c; simpa using h1 0 0
    | add _ _ _ _ a b => intro c; rw [smul_add]; exact h3 _ _ (a c) (b c)
    | smul a _ _ h => intro c; rw [smul_smul]; exact h _
  have hg : ∀ x, IsCuspGrow θ V (T x) := fun x => GlobalTheory.Chain.CuspGrowSpace.isCuspGrow_of_mem_span D θ V _ (hind (fun x => T x ∈ _)
    (fun φ y => Submodule.subset_span (hT φ y ▸ hBg _ _)) (fun x y a b => by rw [map_add]; exact add_mem a b) x)
  obtain ⟨μ, 𝓕, hμ, h𝓕⟩ := GlobalTheory.Ker.HypModel.exists_haar_fundDom D V
  obtain ⟨E, hE0, -⟩ := GlobalTheory.Chain.CuspL2.exists_embedding_skew hdec D θ V μ 𝓕 hθ hμ h𝓕
  obtain ⟨U, ⟨hU, hUe⟩, -⟩ := hG θ hθ V S M J χ μ 𝓕 hμ h𝓕 (T.compMultilinearMap (PiTensorProduct.tprod ℂ))
    ⟨fun u => (hg _).1, fun u => (hg _).2.1, fun u => (hg _).2.2.1, fun u => (hE0 _ (hg _)).1, fun u => (hg _).2.2.2,
      fun u => hind (fun x => ∀ k ∈ J, ∀ g, T x (g * k) = χ k * T x g) (fun φ y => hT φ y ▸ hlev _ _)
        (fun x y a b k hk g => by simp only [map_add, Pi.add_apply, a k hk g, b k hk g, mul_add]) _,
      fun τ k hk u w hw => by
        obtain rfl : w = kOp M τ hk (u τ) := Subtype.ext hw
        rw [LinearMap.compMultilinearMap_apply, ← position_tprod]
        refine hind (fun x => T (intersection_update_fsHerm_neg_one τ (kOp M τ hk) x) = rTr V (atTau θ V τ k) (T x)) (fun φ y => ?_)
          (fun x y a b => by rw [map_add, map_add, map_add, a, b]; rfl) _
        obtain ⟨φ', -, h2⟩ := hK τ φ k hk
        rw [hT, ← (h2 _).2, ← hT]
        refine congrArg T (inj ((tensorLaw D V S M).inj ?_))
        rw [(GlobalTheory.Chain.IoLift.FinTensor.kFinTensor D V S M τ h).2.2, hI, hI, (h2 _).1],
      fun τ X hX u w hw => by
        obtain rfl : w = a τ X (u τ) := Subtype.ext (hw.trans ((ha τ).der X hX _).deriv)
        rw [LinearMap.compMultilinearMap_apply, ← position_tprod]
        refine hind (fun x => T (intersection_update_fsHerm_neg_one τ (a τ X) x) = Rder θ V τ X (T x)) (fun φ y => ?_)
          (fun x y a b => by
            rw [map_add, map_add, map_add, a, b, (GlobalTheory.Mem.AutSpace.linOnSm_Rder hX).add _ (hg _).2.1 _ (hg _).2.1]) _
        rw [← hIs' τ X hX, hT, hT, hBs τ X hX]⟩
  refine ⟨PiTensorProduct.lift U, ⟨U, Submodule.subset_span hU, rfl⟩, fun φ y => ?_⟩
  have e : PiTensorProduct.lift U ∘ₗ inclK h = T := PiTensorProduct.ext (MultilinearMap.ext fun u => by
    rw [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, inclK_tprod, PiTensorProduct.lift.tprod]
    exact hUe _ u fun _ => rfl)
  rw [← hI, ← hT, ← e, LinearMap.comp_apply]

theorem exists_integralForm {X : Type} [MeasurableSpace X] (μ : Measure X) :
    ∃ I : (X → ℂ) →ₗ[ℂ] ℂ, ∀ φ, Integrable φ μ → I φ = ∫ x, φ x ∂μ := by
  let U : Submodule ℂ (X → ℂ) :=
    { carrier := {φ | Integrable φ μ}
      add_mem' := fun ha hb => Integrable.add ha hb
      zero_mem' := integrable_zero _ _ _
      smul_mem' := fun c _ h => Integrable.smul c h }
  let l : U →ₗ[ℂ] ℂ :=
    { toFun := fun φ => ∫ x, φ.1 x ∂μ
      map_add' := fun a b => integral_add a.2 b.2
      map_smul' := fun c a => integral_smul c a.1 }
  obtain ⟨I, hI⟩ := LinearMap.exists_extend l
  exact ⟨I, fun φ h => LinearMap.congr_fun hI ⟨φ, h⟩⟩

theorem exists_trilinear {G H S P Ds : Type} [MeasurableSpace H] [AddCommGroup S] [Module ℂ S] [AddCommGroup P] [Module ℂ P]
    [AddCommGroup Ds] [Module ℂ Ds] (ν : Measure H) (𝓕 : Set H) (th : G → H → S →ₗ[ℂ] ℂ) (pt : P →ₗ[ℂ] S)
    (C : Submodule ℂ (Ds →ₗ[ℂ] (H → ℂ)))
    (hint : ∀ F : C, ∀ φ v g, IntegrableOn (fun h => th g h (pt φ) * (F : Ds →ₗ[ℂ] (H → ℂ)) v h) 𝓕 ν) :
    ∃ B : P →ₗ[ℂ] Ds →ₗ[ℂ] C →ₗ[ℂ] (G → ℂ), ∀ φ v F,
      B φ v F = Lift.liftInt ν 𝓕 (fun g h s => th g h s) (pt φ) ((F : Ds →ₗ[ℂ] (H → ℂ)) v) := by
  obtain ⟨I, hI⟩ := exists_integralForm (ν.restrict 𝓕)
  let b : P → Ds → C →ₗ[ℂ] (G → ℂ) := fun φ v =>
    { toFun := fun F g => I fun h => th g h (pt φ) * (F : Ds →ₗ[ℂ] (H → ℂ)) v h
      map_add' := fun F F' => funext fun g => by
        rw [Pi.add_apply, ← map_add]; congr 1; funext h; simp [mul_add]
      map_smul' := fun c F => funext fun g => by
        rw [Pi.smul_apply, ← map_smul]; congr 1; funext h; simp [mul_left_comm] }
  refine ⟨LinearMap.mk₂ ℂ b ?_ ?_ ?_ ?_, fun φ v F => funext fun g => hI _ (hint F φ v g)⟩
  · refine fun φ φ' v => LinearMap.ext fun F => funext fun g => ?_
    show I _ = I _ + I _
    rw [← map_add]; congr 1; funext h; simp [add_mul]
  · refine fun c φ v => LinearMap.ext fun F => funext fun g => ?_
    show I _ = c • I _
    rw [← map_smul]; congr 1; funext h; simp [mul_assoc]
  · refine fun φ v v' => LinearMap.ext fun F => funext fun g => ?_
    show I _ = I _ + I _
    rw [← map_add]; congr 1; funext h; simp [mul_add]
  · refine fun c φ v => LinearMap.ext fun F => funext fun g => ?_
    show I _ = c • I _
    rw [← map_smul]; congr 1; funext h; simp [mul_left_comm]

theorem ioExists_of_forall {G H S P Ds Dt : Type} [MeasurableSpace H] [AddCommGroup P] [Module ℂ P]
    [AddCommGroup Ds] [Module ℂ Ds] [AddCommGroup Dt] [Module ℂ Dt] {ν : Measure H} {𝓕 : Set H} {th : G → H → S → ℂ}
    {pt : P → S} {T : P →ₗ[ℂ] Ds →ₗ[ℂ] Dt} {C : Submodule ℂ (Ds →ₗ[ℂ] (H → ℂ))} {C' : Submodule ℂ (Dt →ₗ[ℂ] (G → ℂ))}
    (hint : ∀ F : C, ∀ φ v g, IntegrableOn (fun h => th g h (pt φ) * (F : Ds →ₗ[ℂ] (H → ℂ)) v h) 𝓕 ν)
    (B : P →ₗ[ℂ] Ds →ₗ[ℂ] C →ₗ[ℂ] (G → ℂ))
    (hB : ∀ φ v F, B φ v F = Lift.liftInt ν 𝓕 th (pt φ) ((F : Ds →ₗ[ℂ] (H → ℂ)) v))
    (hex : ∀ F : C, ∃ u ∈ C', ∀ φ v, u (T φ v) = B φ v F) (hun : ∀ u ∈ C', (∀ φ v, u (T φ v) = 0) → u = 0) :
    Lift.IoExists ν 𝓕 th pt T C C' := by
  choose u hu he using hex
  refine ⟨LinearMap.codRestrict C' ⟨⟨u, fun F F' => ?_⟩, fun c F => ?_⟩ hu, hint, fun F φ v g => ?_⟩
  · refine sub_eq_zero.1 (hun _ (sub_mem (hu _) (add_mem (hu _) (hu _))) fun φ v => ?_)
    simp only [LinearMap.sub_apply, LinearMap.add_apply, he, map_add, sub_self]
  · refine sub_eq_zero.1 (hun _ (sub_mem (hu _) (C'.smul_mem _ (hu _))) fun φ v => ?_)
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, he, map_smul, RingHom.id_apply, sub_self]
  · exact congrFun ((hB φ v F).symm.trans (he F φ v).symm) g

theorem elt_one {θ : InfFam D} (hθ : IsInfFam θ) (M : DSModel V S) (τ : D.what₂.Tau) : elt θ M τ 1 = 1 := by
  rw [elt, Matrix.mul_one, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)), atTau_one hθ]

theorem apply_kMean {θ : InfFam D} {J : Set (GA D V)} {χ : GA D V → ℂ} {T : MMap M} (hT : IsMultMap θ M J χ T)
    (τ : D.what₂.Tau) {e : Formalism.REAL.KG (M.ε τ) → ℂ} (he : Continuous e) (v : M.Vec) (u : M.sm τ)
    (hu : (u : M.H τ) = kMean M τ e (v τ)) (x : GA D V) : T (Function.update v τ u) x =
      ∫ k, e k * T v (x * elt θ M τ (Formalism.REAL.toMK k)) ∂(Formalism.REAL.muK (M.ε τ)) := by
  obtain ⟨ℓ, hℓ, hl⟩ := hT.cont τ v x
  rw [← hl, hu, ((GlobalTheory.SmoothAverage.kMean_smooth D V S M τ e he _ (v τ).2).2 ℓ hℓ).2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  have hk := (Formalism.REAL.maximal_compact_facts _ (M.ε τ)).1 _ k.2
  have hw : M.σ τ (Formalism.REAL.toMK k) (v τ) ∈ M.sm τ := (GlobalTheory.MultGelf.mem_sm M τ).2
    (GlobalTheory.SmVec.sigma_mem (M.fr_unit τ) (M.fr_gram τ) (M.ds τ).2.2.1 ((GlobalTheory.MultGelf.mem_sm M τ).1 (v τ).2) hk)
  beta_reduce
  rw [hl ⟨_, hw⟩, hT.equiv τ _ (GlobalTheory.SmVec.conj_mem_UH (M.fr_unit τ) (M.fr_gram τ) hk) v ⟨_, hw⟩
    (congrArg (fun L : M.H τ →L[ℂ] M.H τ => L (v τ)) (GlobalTheory.SmVec.trRep_conj (σ := M.σ τ) (M.fr_unit τ) _)).symm]
  rfl

end GlobalTheory.Chain.IoLift

end
end
