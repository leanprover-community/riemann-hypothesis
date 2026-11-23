module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IncludeLInjective
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.ConjugateSelfDual.Statement
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Objects
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

namespace GlobalTheory.CMExt

def tinv {n : ℕ} {K : Type} [Field K] (A : GL (Fin n) K) : GL (Fin n) K :=
  ⟨Matrix.transpose ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K),
   Matrix.transpose ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K),
   by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one],
   by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]⟩

theorem coe_tinv {n : ℕ} {K : Type} [Field K] (A : GL (Fin n) K) :
    ((tinv A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      Matrix.transpose ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := rfl

theorem coe_tinv_inv {n : ℕ} {K : Type} [Field K] (A : GL (Fin n) K) :
    (((tinv A)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      Matrix.transpose ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := rfl

theorem comp_conj_conj {L : Type} [Field L] [NumberField L] [IsCMField L] {K : Type} [Field K] (σ : L →+* K) :
    (σ.comp (IsCMField.complexConj L : L →+* L)).comp (IsCMField.complexConj L : L →+* L) = σ := by
  ext x
  simp [IsCMField.complexConj_apply_apply]

noncomputable def cmExtend {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {ι : Type} {K : Type} [Field K]
    (emb : ι → L →+* K) (g : ι → GL (Fin n) K) (σ : L →+* K) : GL (Fin n) K := by
  classical
  exact if h : ∃ τ, σ = emb τ then g h.choose
    else if h' : ∃ τ, σ = (emb τ).comp (IsCMField.complexConj L : L →+* L) then tinv (g h'.choose) else 1

end GlobalTheory.CMExt

open GlobalTheory.CMExt in
theorem GlobalTheory.cmType_family_extend : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (ι : Type) [Fintype ι] (K : Type) [Field K]
    (emb : ι → L →+* K), GlobalTheory.AlgWtF.CMDist emb → ∀ g : ι → GL (Fin n) K, ∃ B : (L →+* K) → GL (Fin n) K,
    (∀ σ : L →+* K, ((B (σ.comp (IsCMField.complexConj L : L →+* L)) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        Matrix.transpose (((B σ)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ∧ ∀ τ, B (emb τ) = g τ := by
  intro L _ _ _ n ι _ K _ emb hd g
  classical
  have hinj2 : ∀ τ τ', (emb τ).comp (IsCMField.complexConj L : L →+* L) = (emb τ').comp (IsCMField.complexConj L : L →+* L) → τ = τ' := by
    intro τ τ' h
    apply hd.1
    have := congrArg (fun s : L →+* K => s.comp (IsCMField.complexConj L : L →+* L)) h
    simpa [comp_conj_conj] using this
  have v1 : ∀ τ, cmExtend emb g (emb τ) = g τ := by
    intro τ
    have h : ∃ τ', emb τ = emb τ' := ⟨τ, rfl⟩
    simp only [cmExtend, dif_pos h]
    rw [hd.1 h.choose_spec.symm]
  have v2 : ∀ τ, cmExtend emb g ((emb τ).comp (IsCMField.complexConj L : L →+* L)) = tinv (g τ) := by
    intro τ
    have h : ¬ ∃ τ', (emb τ).comp (IsCMField.complexConj L : L →+* L) = emb τ' := by
      rintro ⟨τ', h⟩
      exact hd.2 τ' τ h.symm
    have h' : ∃ τ', (emb τ).comp (IsCMField.complexConj L : L →+* L) = (emb τ').comp (IsCMField.complexConj L : L →+* L) := ⟨τ, rfl⟩
    simp only [cmExtend, dif_neg h, dif_pos h']
    rw [hinj2 _ _ h'.choose_spec.symm]
  have v3 : ∀ σ, (¬ ∃ τ, σ = emb τ) → (¬ ∃ τ, σ = (emb τ).comp (IsCMField.complexConj L : L →+* L)) → cmExtend emb g σ = 1 := by
    intro σ h h'
    simp only [cmExtend, dif_neg h, dif_neg h']
  refine ⟨cmExtend emb g, ?_, v1⟩
  intro σ
  by_cases h : ∃ τ, σ = emb τ
  · obtain ⟨τ, rfl⟩ := h
    rw [v2, v1, coe_tinv]
  · by_cases h' : ∃ τ, σ = (emb τ).comp (IsCMField.complexConj L : L →+* L)
    · obtain ⟨τ, rfl⟩ := h'
      rw [comp_conj_conj, v1, v2, coe_tinv_inv, Matrix.transpose_transpose]
    · have e1 : ¬ ∃ τ, σ.comp (IsCMField.complexConj L : L →+* L) = emb τ := by
        rintro ⟨τ, hτ⟩
        apply h'
        refine ⟨τ, ?_⟩
        rw [← hτ, comp_conj_conj]
      have e2 : ¬ ∃ τ, σ.comp (IsCMField.complexConj L : L →+* L) = (emb τ).comp (IsCMField.complexConj L : L →+* L) := by
        rintro ⟨τ, hτ⟩
        apply h
        refine ⟨τ, ?_⟩
        have := congrArg (fun s : L →+* K => s.comp (IsCMField.complexConj L : L →+* L)) hτ
        simpa [comp_conj_conj] using this
      rw [v3 _ e1 e2, v3 _ h h']
      simp
