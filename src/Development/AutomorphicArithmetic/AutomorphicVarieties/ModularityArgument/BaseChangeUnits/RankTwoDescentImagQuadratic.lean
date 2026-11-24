module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.IsAlgChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.RatTorsionFree
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BlochKatoSelmerVanishes

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.Base UpperTheory.V.Af
open scoped Matrix

private theorem kills_pow {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {C : Type} [CommGroup C] {M : ℕ} (hM : 1 ≤ M)
    {χ : G ℚ Ω →* C} (hχ : KillsMu M χ) : ∃ k : ℕ, 0 < k ∧ ∀ s, χ s ^ k = 1 := by
  haveI : NeZero M := ⟨by omega⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨μ, hμ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω M
  refine ⟨Fintype.card (ZMod M)ˣ, Fintype.card_pos, fun s => ?_⟩
  rw [← map_pow]
  refine hχ _ fun ζ h => ?_
  have h1 := hμ.autToPow_spec ℚ (s ^ Fintype.card (ZMod M)ˣ)
  rw [map_pow, pow_card_eq_one, Units.val_one, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod _ hμ.pow_eq_one, pow_one] at h1
  obtain ⟨i, -, rfl⟩ := hμ.eq_pow_of_pow_eq_one h
  rw [map_pow, ← h1]

private theorem pair2 {k : Type} [Field k] (A : Matrix (Fin 2) (Fin 2) k) :
    Aᵀ * !![0, 1; -1, 0] * A = A.det • (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) k) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.det_fin_two] <;> ring

private theorem pairing2 {F Ω k : Type} [Field F] [Field Ω] [Algebra F Ω] [Field k] (r : G F Ω →* GL (Fin 2) k) (c : G F Ω) :
    ∃ P, IsPairing c r ((Matrix.GeneralLinearGroup.det.comp r).comp (resG F F Ω)) P := by
  let J : GL (Fin 2) k := Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; -1, 0] (by simp [Matrix.det_fin_two])
  refine ⟨J * r c⁻¹, fun s s' h => ?_⟩
  have h' : s' = c * s * c⁻¹ := h
  have e : r c⁻¹ * r s' = r s * r c⁻¹ := by rw [h', ← map_mul, ← map_mul]; congr 1; group
  have e' : (r c⁻¹).val * (r s').val = (r s).val * (r c⁻¹).val := congrArg Units.val e
  have hp : (r s).valᵀ * J.val * (r s).val = (r s).val.det • J.val := pair2 _
  have hd : (((Matrix.GeneralLinearGroup.det.comp r).comp (resG F F Ω) s : kˣ) : k) = (r s).val.det := rfl
  rw [hd, Units.val_mul, ← Matrix.smul_mul, ← hp]
  simp only [Matrix.mul_assoc, e']

private theorem tf (L Ω : Type) [Field L] [Field Ω] [Algebra L Ω] : Module.IsTorsionFree L Ω :=
  DivisionSemiring.to_moduleIsTorsionFree

attribute [local instance] tf

end
