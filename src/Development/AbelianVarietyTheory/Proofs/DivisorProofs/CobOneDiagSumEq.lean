import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsCharZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BialgebraPullbackTwoConvMulSymmetricCocycle

section
set_option autoImplicit false

noncomputable section

open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv

namespace GlobalTheory

namespace PDiv

variable {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Bialgebra R A] [Bialgebra R B]
  [IsCocomm R A] [IsCocomm R B]

variable (R A) in

abbrev multDiag (i : ℕ) : A ⊗[R] A →ₐ[R] A :=
  Algebra.TensorProduct.lift (mulBy R A i : A →ₐ[R] A) (AlgHom.id R _) (fun _ _ ↦ Commute.all _ _)

variable (R A) in

abbrev valZero : A ⊗[R] A →ₐ[R] R :=
  Algebra.TensorProduct.lift (counitAlgHom R A) (counitAlgHom R A) (fun _ _ ↦ Commute.all _ _)

theorem map_multDiag (f : A →ₐc[R] B) (i : ℕ) (c : A ⊗[R] A) :
    f (multDiag R A i c) = multDiag R B i (pullbackTwo f c) := by
  induction c with
  | zero => simp
  | add s t hs ht => simp only [map_add, hs, ht]
  | tmul a b => simp [map_mulBy]

omit [IsCocomm R A] [IsCocomm R B] in

theorem valZero_pullTwo (f : A →ₐc[R] B) (c : A ⊗[R] A) :
    valZero R B (pullbackTwo f c) = valZero R A c := by
  induction c with
  | zero => simp
  | add s t hs ht => simp only [map_add, hs, ht]
  | tmul a b => simp


theorem pullTwo_mulBy_eq (c : A ⊗[R] A) (hc : c ∈ symCocycles R A) (k : ℕ) :
    pullbackTwo (mulBy R A k) c = algebraMap R _ (valZero R A c) + k • c +
      cobOne R A (∑ i ∈ Finset.range k, multDiag R A i c) := by
  induction k with
  | zero =>
    have h0 : ∀ a : A, mulBy R A 0 a = algebraMap R A (counit a) := fun _ => rfl
    rw [Finset.sum_range_zero, map_zero, zero_smul, add_zero, add_zero]
    generalize c = t
    induction t with
    | zero => simp
    | add s t hs ht => simp only [map_add, hs, ht]
    | tmul a b =>
      simp [h0, Algebra.algebraMap_eq_smul_one, Algebra.TensorProduct.one_def, smul_tmul',
        smul_smul, mul_comm]
  | succ k ih =>
    have h := pullTwo_convMul (mulBy R A k) (BialgHom.id R A) c hc
    have e : (toConv (mulBy R A k) * toConv (BialgHom.id R A)).ofConv = mulBy R A (k + 1) := by
      rw [mulBy, mulBy, pow_succ]
    have e2 : ∀ t : A ⊗[R] A, LinearMap.mul' R A (TensorProduct.map (mulBy R A k : A →ₗ[R] A)
        (BialgHom.id R A : A →ₗ[R] A) t) = multDiag R A k t := fun t => by
      induction t with
      | zero => simp
      | add s t hs ht => simp only [map_add, hs, ht]
      | tmul a b => simp
    rw [e, e2, pullTwo_id, ih] at h
    rw [h, Finset.sum_range_succ, map_add, succ_nsmul]
    abel

end PDiv

namespace PDivGroup

open PDiv


end PDivGroup

end GlobalTheory
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem cobOne_diagSum_eq (p : ℕ) (R : Type) [CommRing R] (G : PDivGroup p R) (n m : ℕ) (hm : (m : R) = 0) :
    ∀ c ∈ symCocycles R (G.A n), cobOne R (G.A n) (diagSum R (G.A n) m c) = pullbackTwo (mulBy R (G.A n) m) c -
      (Algebra.TensorProduct.lift (Bialgebra.counitAlgHom R (G.A n)) (Bialgebra.counitAlgHom R (G.A n))
        (fun _ _ ↦ Commute.all _ _) c) • (1 : G.A n ⊗[R] G.A n) := by
  intro c hc
  have hd : diagSum R (G.A n) m c = ∑ i ∈ Finset.range m, multDiag R (G.A n) i c := by
    simp [diagSum, LinearMap.sum_apply]
  have hz : m • c = 0 := by rw [← Nat.cast_smul_eq_nsmul R, hm, zero_smul]
  rw [pullTwo_mulBy_eq c hc m, hz, add_zero, hd, Algebra.algebraMap_eq_smul_one]
  abel

end GlobalTheory.PtExt
end
end
