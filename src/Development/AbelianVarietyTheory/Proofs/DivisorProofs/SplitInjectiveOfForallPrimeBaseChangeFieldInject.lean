module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Spectrum.Prime.Defs
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndKerBaseChangeOfForallResidueField
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open TensorProduct

namespace GlobalTheory

theorem split_injective_of_forall_prime_baseChange_field_injective :
    ∀ (R : Type) [CommRing R] (M : Type 1) [AddCommGroup M] [Module R M] [Module.Finite R M]
      [Module.Projective R M] (N : Type 1) [AddCommGroup N] [Module R N] [Module.Finite R N]
      [Module.Projective R N] (f : M →ₗ[R] N),
      (∀ P : PrimeSpectrum R, ∃ (k : Type) (_ : Field k) (_ : Algebra R k),
        RingHom.ker (algebraMap R k) = P.asIdeal ∧ Function.Injective (f.baseChange k)) →
      ∃ g : N →ₗ[R] M, g ∘ₗ f = LinearMap.id := by
  intro R _ M _ _ _ _ N _ _ _ _ f h
  refine split_injective_of_forall_lTensor_residueField_injective f fun m hm => ?_
  obtain ⟨k, _, _, hk, hinj⟩ := h ⟨m, hm.isPrime⟩
  simp only at hk
  let φ : m.ResidueField →ₐ[R] k := Ideal.ResidueField.liftₐ m (Algebra.ofId R k) hk.ge (by
    intro x hx
    simp only [Submonoid.mem_comap, IsUnit.mem_submonoid_iff, isUnit_iff_ne_zero]
    intro h0
    exact hx (hk ▸ h0))
  letI : Algebra m.ResidueField k := φ.toRingHom.toAlgebra
  haveI : IsScalarTower R m.ResidueField k :=
    IsScalarTower.of_algebraMap_eq fun x => (φ.commutes x).symm
  have e : (AlgebraTensorModule.cancelBaseChange R m.ResidueField m.ResidueField k N) ∘
        ((f.baseChange m.ResidueField).lTensor k) =
      (f.lTensor k) ∘ (AlgebraTensorModule.cancelBaseChange R
        m.ResidueField m.ResidueField k M) := by
    funext x
    exact (LinearMap.congr_fun (AlgebraTensorModule.lTensor_comp_cancelBaseChange R
      m.ResidueField m.ResidueField (M := k) f) x).symm
  have h1 : Function.Injective ((f.baseChange m.ResidueField).lTensor k) :=
    Function.Injective.of_comp (e ▸ (hinj.comp (LinearEquiv.injective _)))
  exact (Module.FaithfullyFlat.lTensor_injective_iff_injective m.ResidueField k _).1 h1

end GlobalTheory
