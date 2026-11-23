module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylCharacterRegularity.AlgInfCharIff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.IrrSub
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.QdetRect
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylCharacterRegularity.IsRegConj
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.ConjugateCuspidalReps.IsConjRepRefl

@[expose] public section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.WeylC UpperTheory.V.Cj.R

theorem UpperTheory.exists_algRep_qdet_eq_smul_one_of_isReg :
    ∀ (E : Type) [Field E] [NumberField E] (a D : ℕ), 0 < D → ∀ (ρ : GL (Fin a) (Cinf E) →* Matrix (Fin D) (Fin D) ℂ), IsReg ρ → ∀ s : (E →+* ℂ) → ℂ → ℂ, (∀ τ u, Formalism.REAL.qdet (eOf ρ τ) u = s τ u • 1) → ∃ Ξ : AlgRep E a, ∀ τ u, Formalism.REAL.qdet (eOf Ξ.mat τ) u = s τ u • 1 := by
  intro E _ _ a D hD ρ hreg s hs
  obtain ⟨d, A, B, σ, hd, -, hBA, hσ, hint, hirr⟩ := UpperTheory.V.Weyl.irrSub _ D ρ hD
  have hσreg : IsReg σ := by simpa only [← hσ] using isReg_conj hreg B A
  refine ⟨⟨d, σ, hσreg, hd, hirr⟩, fun τ u => ?_⟩
  have hlie : ∀ i j, eOf ρ τ i j * A = A * eOf σ τ i j := by
    intro i j
    have l := eOf_conj hreg (1 : Matrix (Fin D) (Fin D) ℂ) A τ i j
    have r := eOf_conj hσreg A (1 : Matrix (Fin d) (Fin d) ℂ) τ i j
    simp only [Matrix.one_mul, Matrix.mul_one, hint] at l r
    exact l.symm.trans r
  have hq := UpperTheory.V.Weyl.qdetRect a D d _ _ A hlie u
  calc Formalism.REAL.qdet (eOf σ τ) u = B * (A * Formalism.REAL.qdet (eOf σ τ) u) := by
        rw [← Matrix.mul_assoc, hBA, Matrix.one_mul]
    _ = s τ u • 1 := by
        rw [← hq, hs, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, hBA]
