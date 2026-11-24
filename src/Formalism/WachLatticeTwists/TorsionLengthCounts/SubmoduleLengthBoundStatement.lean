module

public import Formalism.WachLatticeTwists.Statement
public import Formalism.CharacterColumnKernels.IdempotentNormalForms.LengthKerOfDetEqZero
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Module IsDiscreteValuationRing Matrix

noncomputable section

namespace Formalism.RepresentationBoundsCohomology

theorem submoduleLengthBound_statement : Formalism.RepresentationBoundsCohomology.SubmoduleLengthBound := by
  intro O _ _ _ d _ N ℓ c hN
  classical

  let e : d ≃ Fin (Fintype.card d) := Fintype.equivFin d
  let A : Matrix (Fin (Fintype.card d)) (Fin (Fintype.card d)) O :=
    Matrix.diagonal (fun _ => (ℓ : O) ^ c)
  have hA : ∀ v : Fin (Fintype.card d) → Formalism.NG.KO O,
      Formalism.NG.matQ O A v = ((ℓ : O) ^ c) • v := by
    intro v
    funext i
    simp [Formalism.NG.matQ, Formalism.NG.relMap, A, Matrix.diagonal_apply, ite_smul]
  let g : (d → Formalism.NG.KO O) →ₗ[O] (Fin (Fintype.card d) → Formalism.NG.KO O) :=
    LinearMap.funLeft O (Formalism.NG.KO O) e.symm
  have hg : Function.Injective g :=
    LinearMap.funLeft_injective_of_surjective _ _ _ e.symm.surjective
  let f : N →ₗ[O] LinearMap.ker (Formalism.NG.matQ O A) :=
    LinearMap.codRestrict _ (g.comp N.subtype) (by
      intro x
      rw [LinearMap.mem_ker, hA]
      simp only [LinearMap.comp_apply, Submodule.subtype_apply]
      rw [← map_smul, hN x x.2, map_zero])
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply hg
    have := congrArg Subtype.val hxy
    simpa [f] using this
  have h1 := Module.length_le_of_injective f hf
  rw [Formalism.NG.lenKer O (Fin (Fintype.card d)) A] at h1
  have hdet : A.det = ((ℓ : O) ^ c) ^ Fintype.card d := by
    simp [A, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ]
  rw [hdet, IsDiscreteValuationRing.addVal_pow, IsDiscreteValuationRing.addVal_pow] at h1
  rw [Formalism.NG.IdempotentNormalFormsLenFacts.length_quot_span]
  simpa [nsmul_eq_mul] using h1

end Formalism.RepresentationBoundsCohomology
