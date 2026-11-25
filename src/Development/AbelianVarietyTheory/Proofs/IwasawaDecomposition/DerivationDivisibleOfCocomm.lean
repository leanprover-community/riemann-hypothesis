module

public import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.IsOpenPart
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.MemPrimitiveTensorsIffIsPrimitiveElem
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsIntegralOfDivisibleCharacters
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormSmulLeOneOfPrimitiveBoundedPowers
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt

@[expose] public section

noncomputable section

open Formalism.MainNotions.DIV.Cons (intO)
open TensorProduct Coalgebra WithConv

namespace GlobalTheory.GroupLikeDerivation

section Norm

variable {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C]
  {M : Type} [AddCommGroup M] [Module ↥(intO C) M]

def supNorm (f : WithConv (M →ₗ[↥(intO C)] C)) : ℝ := ⨆ m, ‖f.ofConv m‖

end Norm

section Conv

variable {R C A : Type} [CommRing R] [CommRing C] [Algebra R C] [CommRing A] [Bialgebra R A]

def extProd (f g : WithConv (A →ₗ[R] C)) : WithConv (A ⊗[R] A →ₗ[R] C) :=
  toConv ((Algebra.TensorProduct.lmul' R (S := C)).toLinearMap ∘ₗ TensorProduct.map f.ofConv g.ofConv)

@[simp] theorem extProd_tmul (f g : WithConv (A →ₗ[R] C)) (a b : A) :
    (extProd f g).ofConv (a ⊗ₜ b) = f.ofConv a * g.ofConv b := by
  simp [extProd]

theorem extProd_mul (f g h k : WithConv (A →ₗ[R] C)) :
    extProd f g * extProd h k = extProd (f * h) (g * k) := by
  have h1 := TensorProduct.map_convMul_map (f := f) (h := h) (g := g) (k := k)
  have h2 := LinearMap.algHom_comp_convMul_distrib (Algebra.TensorProduct.lmul' R (S := C))
    (toConv (TensorProduct.map f.ofConv g.ofConv)) (toConv (TensorProduct.map h.ofConv k.ofConv))
  rw [h1] at h2
  exact (congrArg toConv h2).symm

theorem tensor_ext {f g : WithConv (A ⊗[R] A →ₗ[R] C)}
    (h : ∀ a b, f.ofConv (a ⊗ₜ b) = g.ofConv (a ⊗ₜ b)) : f = g :=
  WithConv.ext (TensorProduct.ext' h)

theorem extProd_one : extProd (1 : WithConv (A →ₗ[R] C)) 1 = 1 :=
  tensor_ext fun a b => by simp [mul_comm]

variable (R C A) in
def inlHom : WithConv (A →ₗ[R] C) →ₐ[C] WithConv (A ⊗[R] A →ₗ[R] C) :=
  AlgHom.ofLinearMap
    { toFun := fun f => extProd f 1
      map_add' := fun f g => tensor_ext fun a b => by simp [add_mul]
      map_smul' := fun c f => tensor_ext fun a b => by simp [mul_assoc] }
    extProd_one fun f g => by simp [extProd_mul]

variable (R C A) in
def inrHom : WithConv (A →ₗ[R] C) →ₐ[C] WithConv (A ⊗[R] A →ₗ[R] C) :=
  AlgHom.ofLinearMap
    { toFun := fun f => extProd 1 f
      map_add' := fun f g => tensor_ext fun a b => by simp [mul_add]
      map_smul' := fun c f => tensor_ext fun a b => by simp [mul_left_comm] }
    extProd_one fun f g => by simp [extProd_mul]

variable (R C A) in
def mulHom : WithConv (A →ₗ[R] C) →ₐ[C] WithConv (A ⊗[R] A →ₗ[R] C) :=
  AlgHom.ofLinearMap
    { toFun := fun f => toConv (f.ofConv ∘ₗ (Bialgebra.mulCoalgHom R A).toLinearMap)
      map_add' := fun f g => rfl
      map_smul' := fun c f => rfl }
    (tensor_ext fun a b => by simp [mul_comm])
    fun f g => congrArg toConv (LinearMap.convMul_comp_coalgHom_distrib f g _)

variable (R C A) in
def extendHom : WithConv (A →ₗ[R] R) →ₐ[R] WithConv (A →ₗ[R] C) :=
  AlgHom.ofLinearMap
    { toFun := fun f => toConv ((Algebra.ofId R C).toLinearMap ∘ₗ f.ofConv)
      map_add' := fun f g => WithConv.ext (LinearMap.ext fun a => by simp)
      map_smul' := fun c f => WithConv.ext (LinearMap.ext fun a =>
        map_smul (Algebra.ofId R C).toLinearMap c (f.ofConv a)) }
    (WithConv.ext (LinearMap.ext fun a => by simp))
    fun f g => congrArg toConv (LinearMap.algHom_comp_convMul_distrib _ f g)

theorem inlHom_mul_inrHom (f g : WithConv (A →ₗ[R] C)) :
    inlHom R C A f * inrHom R C A g = extProd f g := by
  change extProd f 1 * extProd 1 g = _
  rw [extProd_mul, mul_one, one_mul]

end Conv

theorem exists_isGroupLikeElem {R A : Type} [CommRing R] [CommRing A] [Bialgebra R A]
    [Module.Finite R A] [Module.Projective R A] (χ : CartierDual R A →ₐ[R] R) :
    ∃ u : A, IsGroupLikeElem R u ∧ ∀ φ : CartierDual R A, φ.ofConv u = χ φ := by
  have h : ∀ φ : CartierDual R A,
      φ.ofConv ((CartierDual.bidual R A).symm (toConv χ.toLinearMap)) = χ φ :=
    fun φ => CartierDual.apply_bidual_symm _ φ
  refine ⟨_, (CartierDual.isGroupLikeElem_iff_mul _).2 ⟨?_, fun φ ψ => ?_⟩, h⟩
  · rw [h]; exact map_one χ
  · rw [h, h, h]; exact map_mul χ φ ψ

end GlobalTheory.GroupLikeDerivation
