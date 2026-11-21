import Formalism.SatakeDualWeyl.StatementC

section
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.UG.P
open Formalism.UG

section Adele
variable {F : Type} [Field F] [NumberField F]

local notation "𝔸" => FiniteAdeleRing (𝓞 F) F

theorem afsplit_add_apply (a b : 𝔸) (w : HeightOneSpectrum (𝓞 F)) : (a + b) w = a w + b w := rfl
theorem afsplit_mul_apply (a b : 𝔸) (w : HeightOneSpectrum (𝓞 F)) : (a * b) w = a w * b w := rfl
theorem afsplit_sub_apply (a b : 𝔸) (w : HeightOneSpectrum (𝓞 F)) : (a - b) w = a w - b w := rfl
theorem afsplit_one_apply (w : HeightOneSpectrum (𝓞 F)) : (1 : 𝔸) w = 1 := rfl
theorem afsplit_zero_apply (w : HeightOneSpectrum (𝓞 F)) : (0 : 𝔸) w = 0 := rfl
theorem afsplit_smul_apply (c : F) (a : 𝔸) (w : HeightOneSpectrum (𝓞 F)) :
    (c • a) w = c • a w := by
  rw [Algebra.smul_def, afsplit_mul_apply, Algebra.smul_def]; rfl

def afsplitF (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) : 𝔸 := by
  classical
  exact ⟨Pi.single v x, by
    filter_upwards [show ({v}ᶜ : Set (HeightOneSpectrum (𝓞 F))) ∈ Filter.cofinite by simp] with w hw
    rw [Set.mem_compl_singleton_iff] at hw
    rw [Pi.single_eq_of_ne hw]
    exact zero_mem _⟩

theorem afsplitF_self (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) : afsplitF v x v = x := by
  classical
  show Pi.single v x v = x
  convert Pi.single_eq_same v x

theorem afsplitF_ne (v w : HeightOneSpectrum (𝓞 F)) (h : w ≠ v) (x : v.adicCompletion F) :
    afsplitF v x w = 0 := by
  classical
  show Pi.single v x w = 0
  convert Pi.single_eq_of_ne h x

def afsplitI (v : HeightOneSpectrum (𝓞 F)) : v.adicCompletion F →ₗ[F] 𝔸 where
  toFun := afsplitF v
  map_add' x y := by
    ext w
    by_cases h : w = v
    · subst h; simp only [afsplit_add_apply, afsplitF_self]
    · simp only [afsplit_add_apply, afsplitF_ne v w h, add_zero]
  map_smul' c x := by
    ext w
    by_cases h : w = v
    · subst h; simp only [afsplit_smul_apply, afsplitF_self, RingHom.id_apply]
    · simp only [afsplit_smul_apply, afsplitF_ne v w h, smul_zero, RingHom.id_apply]

theorem afsplitI_self (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) : afsplitI v x v = x :=
  afsplitF_self v x

theorem afsplitI_ne (v w : HeightOneSpectrum (𝓞 F)) (h : w ≠ v) (x : v.adicCompletion F) :
    afsplitI v x w = 0 := afsplitF_ne v w h x

theorem afsplitI_mul (v : HeightOneSpectrum (𝓞 F)) (x y : v.adicCompletion F) :
    afsplitI v (x * y) = afsplitI v x * afsplitI v y := by
  ext w
  by_cases h : w = v
  · subst h; simp only [afsplit_mul_apply, afsplitI_self]
  · simp only [afsplit_mul_apply, afsplitI_ne v w h, mul_zero]

theorem afsplitI_eval (v : HeightOneSpectrum (𝓞 F)) (a : 𝔸) :
    afsplitI v (a v) = afsplitI v 1 * a := by
  ext w
  by_cases h : w = v
  · subst h; simp only [afsplit_mul_apply, afsplitI_self, one_mul]
  · simp only [afsplit_mul_apply, afsplitI_ne v w h, zero_mul]

theorem afsplitI_mem_intAd (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F)
    (hx : x ∈ v.adicCompletionIntegers F) : afsplitI v x ∈ intAd F := by
  intro w
  by_cases h : w = v
  · subst h; rw [afsplitI_self]; exact hx
  · rw [afsplitI_ne v w h]; exact zero_mem _

end Adele
end Formalism.UG.P
end
end

section
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.UG.P
open Formalism.UG

section Tens
variable {F : Type} [Field F] [NumberField F] {E : Type} [CommRing E] [Algebra F E]

local notation "𝔸" => FiniteAdeleRing (𝓞 F) F

def afsplitIE (v : HeightOneSpectrum (𝓞 F)) : E ⊗[F] v.adicCompletion F →ₙ+* E ⊗[F] 𝔸 where
  toFun := LinearMap.lTensor E (afsplitI v)
  map_zero' := map_zero _
  map_add' := map_add _
  map_mul' x y := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x x' hx hx' => simp only [add_mul, map_add, hx, hx']
    | tmul a b =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y y' hy hy' => simp only [mul_add, map_add, hy, hy']
      | tmul c d =>
        simp only [Algebra.TensorProduct.tmul_mul_tmul, LinearMap.lTensor_tmul, afsplitI_mul]

theorem afsplitIE_tmul (v : HeightOneSpectrum (𝓞 F)) (a : E) (x : v.adicCompletion F) :
    afsplitIE v (a ⊗ₜ[F] x) = a ⊗ₜ[F] afsplitI v x := rfl

theorem afsplit_prV_tmul (w : HeightOneSpectrum (𝓞 F)) (a : E) (b : 𝔸) :
    prV (E := E) w (a ⊗ₜ[F] b) = a ⊗ₜ[F] (b w) := rfl

theorem afsplit_prV_IE (v : HeightOneSpectrum (𝓞 F)) (x : E ⊗[F] v.adicCompletion F) :
    prV (E := E) v (afsplitIE v x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a b => rw [afsplitIE_tmul, afsplit_prV_tmul, afsplitI_self]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem afsplit_prV_IE_ne (v w : HeightOneSpectrum (𝓞 F)) (h : w ≠ v)
    (x : E ⊗[F] v.adicCompletion F) : prV (E := E) w (afsplitIE v x) = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a b => rw [afsplitIE_tmul, afsplit_prV_tmul, afsplitI_ne v w h, TensorProduct.tmul_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]

theorem afsplit_sigR_IE (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (x : E ⊗[F] v.adicCompletion F) :
    sigR σ 𝔸 (afsplitIE v x) = afsplitIE v (sigR σ (v.adicCompletion F) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b => simp [sigR, afsplitIE_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

def afsplitEps (E : Type) [CommRing E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) : E ⊗[F] 𝔸 :=
  afsplitIE v 1

theorem afsplit_decomp (v : HeightOneSpectrum (𝓞 F)) (x : E ⊗[F] 𝔸) :
    afsplitIE v (prV (E := E) v x) = afsplitEps E v * x := by
  have he : afsplitEps E v = (1 : E) ⊗ₜ[F] afsplitI v 1 := by
    rw [afsplitEps, Algebra.TensorProduct.one_def, afsplitIE_tmul]
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, mul_zero]
  | tmul a b =>
    rw [afsplit_prV_tmul, afsplitIE_tmul, afsplitI_eval, he, Algebra.TensorProduct.tmul_mul_tmul,
      one_mul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, mul_add]

theorem afsplit_eps_mul_IE (v : HeightOneSpectrum (𝓞 F)) (x : E ⊗[F] v.adicCompletion F) :
    afsplitEps E v * afsplitIE v x = afsplitIE v x := by
  have he : afsplitEps E v = (1 : E) ⊗ₜ[F] afsplitI v 1 := by
    rw [afsplitEps, Algebra.TensorProduct.one_def, afsplitIE_tmul]
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, mul_zero]
  | tmul a b =>
    rw [he, afsplitIE_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← afsplitI_mul, one_mul]
  | add x y hx hy => rw [map_add, mul_add, hx, hy]

theorem afsplit_eps_idem (v : HeightOneSpectrum (𝓞 F)) :
    afsplitEps E v * afsplitEps E v = afsplitEps E v := by
  exact afsplit_eps_mul_IE (E := E) v 1

theorem afsplit_sigR_eps (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) :
    sigR σ 𝔸 (afsplitEps E v) = afsplitEps E v := by
  rw [afsplitEps, afsplit_sigR_IE, map_one]

theorem afsplit_prV_eps (v : HeightOneSpectrum (𝓞 F)) : prV (E := E) v (afsplitEps E v) = 1 := by
  exact afsplit_prV_IE (E := E) v 1

theorem afsplit_prV_eps_ne (v w : HeightOneSpectrum (𝓞 F)) (h : w ≠ v) :
    prV (E := E) w (afsplitEps E v) = 0 := by
  exact afsplit_prV_IE_ne (E := E) v w h 1

theorem afsplit_prV_inclE (v : HeightOneSpectrum (𝓞 F)) (e : E) :
    prV (E := E) v (inclE (F := F) 𝔸 e) = inclE (F := F) (v.adicCompletion F) e := rfl

theorem afsplit_prV_comp_sigR (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) :
    (prV (E := E) v).comp (sigR σ 𝔸) = (sigR σ (v.adicCompletion F)).comp (prV (E := E) v) := by
  refine RingHom.ext fun y => ?_
  simp only [RingHom.comp_apply]
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

end Tens

section Inj
variable {F : Type} [Field F] [NumberField F] {E : Type} [CommRing E] [Algebra F E]

local notation "𝔸" => FiniteAdeleRing (𝓞 F) F

theorem afsplit_coord_prV (b : Module.Basis (Module.Free.ChooseBasisIndex F E) F E)
    (i : Module.Free.ChooseBasisIndex F E) (w : HeightOneSpectrum (𝓞 F)) (y : E ⊗[F] 𝔸) :
    TensorProduct.lid F (w.adicCompletion F) ((b.coord i).rTensor _ (prV (E := E) w y)) =
      (TensorProduct.lid F 𝔸 ((b.coord i).rTensor _ y)) w := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]; rfl
  | tmul a b =>
    rw [afsplit_prV_tmul]
    simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, afsplit_smul_apply]
  | add x y hx hy => simp only [map_add, hx, hy, afsplit_add_apply]

theorem afsplit_inj (y : E ⊗[F] 𝔸) (hy : ∀ w : HeightOneSpectrum (𝓞 F), prV (E := E) w y = 0) :
    y = 0 := by
  classical
  set b := Module.Free.chooseBasis F E
  have hc : ∀ i, TensorProduct.lid F 𝔸 ((b.coord i).rTensor _ y) = 0 := by
    intro i
    ext w
    rw [← afsplit_coord_prV b i w y, hy w]
    simp only [map_zero]
    rfl
  have hcoord : ∀ (z : E ⊗[F] 𝔸) (i : Module.Free.ChooseBasisIndex F E),
      TensorProduct.equivFinsuppOfBasisLeft b z i = TensorProduct.lid F 𝔸 ((b.coord i).rTensor _ z) := by
    intro z i
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul m n => simp [TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]
    | add x y hx hy => simp [hx, hy]
  apply (TensorProduct.equivFinsuppOfBasisLeft (N := 𝔸) b).injective
  rw [map_zero]
  ext i
  rw [hcoord, hc i]
  rfl

end Inj
end Formalism.UG.P
end
end
