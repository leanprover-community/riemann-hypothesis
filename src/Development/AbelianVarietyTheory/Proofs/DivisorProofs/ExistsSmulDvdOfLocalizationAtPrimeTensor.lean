module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
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
import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.LinearAlgebra.TensorProduct.Tower

@[expose] public section

open scoped TensorProduct
open TensorProduct

namespace GlobalTheory

theorem exists_smul_dvd_of_localization_atPrime_tensor :
    ∀ (R C O : Type) [CommRing R] [CommRing C] [Algebra R C] [CommRing O] [Algebra R O]
    (Q : Ideal O) [Q.IsPrime] (b : R) (m : O ⊗[R] C),
    (∃ m' : Localization.AtPrime Q ⊗[R] C,
      (IsScalarTower.toAlgHom R O (Localization.AtPrime Q)).toLinearMap.rTensor C m = algebraMap R (Localization.AtPrime Q) b • m') →
    ∃ s ∉ Q, ∃ m' : O ⊗[R] C, s • m = algebraMap R O b • m' := by
  intro R C O _ _ _ _ _ Q _ b m ⟨m', hm'⟩
  let f := AlgebraTensorModule.rTensor R C (Algebra.linearMap O (Localization.AtPrime Q))
  haveI : IsLocalizedModule Q.primeCompl f := inferInstance
  have hf : ∀ x, (IsScalarTower.toAlgHom R O (Localization.AtPrime Q)).toLinearMap.rTensor C x = f x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a c => simp [f]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  rw [hf, algebraMap_smul] at hm'
  obtain ⟨⟨m'', t⟩, rfl⟩ := IsLocalizedModule.mk'_surjective Q.primeCompl f m'
  simp only [Function.uncurry_apply_pair] at hm'
  have h2 : f ((t : O) • m) = f (b • m'') := by
    rw [LinearMap.map_smul, hm', smul_comm (t : O) b, ← Submonoid.smul_def, IsLocalizedModule.mk'_cancel',
      LinearMap.map_smul_of_tower]
  obtain ⟨u, hu⟩ := IsLocalizedModule.exists_of_eq (S := Q.primeCompl) h2
  refine ⟨(u : O) * t, (Q.primeCompl.mul_mem u.2 t.2 : _), (u : O) • m'', ?_⟩
  rw [algebraMap_smul, mul_smul]
  simpa [Submonoid.smul_def, smul_comm (u : O) b] using hu

end GlobalTheory
