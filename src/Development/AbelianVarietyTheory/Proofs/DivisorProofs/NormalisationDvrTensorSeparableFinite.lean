module

public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteIntegralClosureOfFormallyUnramified
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open IsLocalRing
open scoped TensorProduct



namespace GlobalTheory.NormFin

theorem main : ∀ (S K L D : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Field K] [Algebra S K] [IsFractionRing S K] [Field L] [Algebra K L] [Algebra S L] [IsScalarTower S K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] [CommRing D] [IsDomain D] [IsDiscreteValuationRing D]
    [Algebra S D] [Module.Finite S D] [FaithfulSMul S D],
    Module.Finite D (integralClosure D (TensorProduct S D L)) := by
  intro S K L D _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  classical
  let K' := FractionRing D
  haveI : IsScalarTower S D K' := inferInstance
  have hSK' : Function.Injective (algebraMap S K') :=
    by
      rw [IsScalarTower.algebraMap_eq S D K']
      exact (IsFractionRing.injective D K').comp (FaithfulSMul.algebraMap_injective S D)
  letI : Algebra K K' := (IsFractionRing.lift hSK' : K →+* K').toAlgebra
  haveI : IsScalarTower S K K' :=
    IsScalarTower.of_algebraMap_eq (fun x => (IsFractionRing.lift_algebraMap hSK' x).symm)
  haveI : SMulCommClass K D K' := ⟨fun a b c => by simp only [Algebra.smul_def]; ring⟩
  haveI : Algebra.FormallyUnramified K L := Algebra.FormallyUnramified.of_isSeparable K L
  haveI : Algebra.FormallyUnramified K' (K' ⊗[K] L) := inferInstance
  haveI : FiniteDimensional K' (K' ⊗[K] L) := inferInstance
  haveI : IsScalarTower D K' (K' ⊗[K] L) := inferInstance
  have hfinC : Module.Finite D (integralClosure D (K' ⊗[K] L)) :=
    GlobalTheory.AbhFin.finite_integralClosure_of_formallyUnramified D K' (K' ⊗[K] L)
  haveI : Module.Flat S K := IsLocalization.flat K (nonZeroDivisors S)
  haveI : Module.Flat S L := Module.Flat.trans S K L
  let f : D →ₐ[S] K' := IsScalarTower.toAlgHom S D K'
  let Φ : D ⊗[S] L →ₐ[S] K' ⊗[S] L := Algebra.TensorProduct.map f (AlgHom.id S L)
  have hΦ : Function.Injective Φ := by
    have h1 : Function.Injective (f.toLinearMap.rTensor L) :=
      Module.Flat.rTensor_preserves_injective_linearMap _ (IsFractionRing.injective D K')
    have h2 : (Φ : D ⊗[S] L → K' ⊗[S] L) = f.toLinearMap.rTensor L := by
      funext x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => rfl
      | add x y hx hy => simp only [map_add (f := _), hx, hy]
    rw [h2]; exact h1
  let ι : K' ⊗[S] L ≃ₐ[K] K' ⊗[K] L := (IsLocalization.algebraTensorEquiv (nonZeroDivisors S) K K' L).symm
  have hι : ∀ (a : K') (b : L), ι (a ⊗ₜ[S] b) = a ⊗ₜ[K] b := by
    intro a b
    rw [AlgEquiv.symm_apply_eq]
    rfl
  let Ψ : D ⊗[S] L →ₐ[D] K' ⊗[K] L :=
    { (ι.toRingEquiv.toRingHom.comp Φ.toRingHom) with
      commutes' := fun d => by
        show ι (Φ (d ⊗ₜ[S] 1)) = (algebraMap D K' d) ⊗ₜ[K] 1
        rw [Algebra.TensorProduct.map_tmul]
        exact hι _ _ }
  have hΨ : Function.Injective Ψ := ι.injective.comp hΦ
  let M := integralClosure D (D ⊗[S] L)
  let lin : M →ₗ[D] integralClosure D (K' ⊗[K] L) :=
    { toFun := fun x => ⟨Ψ (x : D ⊗[S] L), (show IsIntegral D (x : D ⊗[S] L) from x.2).map Ψ⟩
      map_add' := fun x y => Subtype.ext (map_add Ψ (x : D ⊗[S] L) y)
      map_smul' := fun r x => Subtype.ext (map_smul Ψ r (x : D ⊗[S] L)) }
  exact Module.Finite.of_injective lin (fun x y h => Subtype.ext (hΨ (congrArg Subtype.val h)))

end GlobalTheory.NormFin
