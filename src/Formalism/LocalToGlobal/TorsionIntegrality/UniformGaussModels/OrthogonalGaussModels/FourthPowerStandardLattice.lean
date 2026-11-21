import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.UniformGaussModelConditionEquivalent
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharacterIdentityReformulated2
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.StdDataCmProof
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.HasCMByStable

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.Top.Inh

open Formalism.L2.Th1.D
open Formalism.L2.Th1.Top
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.H (cmL CmOK matH stdH stdLat blk4 pow4 imgLat relIdx IsIsom IsSelfDual)

theorem block_diag_smul_one {n : Type} [Fintype n] [DecidableEq n] (c : ℂ) :
    blk4 (c • (1 : Matrix n n ℂ)) = c • (1 : Matrix (Fin 4 × n) (Fin 4 × n) ℂ) := by
  ext ⟨a, i⟩ ⟨a', i'⟩
  simp only [blk4, Matrix.smul_apply, Matrix.one_apply, Prod.mk.injEq, smul_eq_mul]
  by_cases h1 : a = a' <;> by_cases h2 : i = i' <;> simp [h1, h2]

theorem fourth_power_standard_lattice (L : PeriodPair) (n : Type) [Fintype n] :
    pow4 (stdLat L n) = stdLat L (Fin 4 × n) := by
  ext z
  rw [Formalism.L2.Th1.H.mem_stdLat]
  constructor
  · intro hz w
    exact (Formalism.L2.Th1.H.mem_stdLat L n _).1 (hz w.1) w.2
  · intro hz a
    exact (Formalism.L2.Th1.H.mem_stdLat L n _).2 fun i => hz (a, i)


theorem relIdx_self {V : Type} [AddCommGroup V] [Module ℂ V] (Λ : AddSubgroup V) : relIdx Λ Λ = 1 := by
  simp [relIdx]



theorem unitary_one {K : Type} [NormedField K] (σ : K →+* K) {m : Type} [Fintype m] [DecidableEq m] :
    IsUnitaryK σ (1 : Matrix m m K) := by
  refine ⟨fun a b => ?_, fun a b => ?_⟩
  · by_cases h : a = b
    · subst h; simp
    · simp [Matrix.one_apply_ne h]
  · by_cases h : a = b
    · subst h
      rw [Finset.sum_eq_single a]
      · simp
      · intro k _ hk; simp [Matrix.one_apply_ne hk]
      · intro h; exact absurd (Finset.mem_univ a) h
    · rw [if_neg h]
      refine Finset.sum_eq_zero fun k _ => ?_
      by_cases hk : k = a
      · subst hk; simp [Matrix.one_apply_ne h]
      · simp [Matrix.one_apply_ne hk]



end Formalism.L2.Th1.Top.Inh
