module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Matrix Formalism.L2.Theta
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SquareAgree



theorem kapX_surjective : ∀ (D : D7) (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (hJ : J = D.host.xi0 • Matrix.reindex e e X.gramᵀ), Function.Surjective (GlobalTheory.SquareAgree.kapX X e hJ) := by
  intro D X d e J hJ y
  obtain ⟨u, hu⟩ : ∃ u : GL (Fin X.rank) (AE D), u.1 = (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat y).submatrix e e :=
    ⟨Units.map (Matrix.reindexAlgEquiv (AE D) (AE D) e.symm).toMonoidHom y.1, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin d) (Fin d) (AE D), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat y = M := ⟨_, rfl⟩
  obtain ⟨Gt, hGt⟩ : ∃ Gt : Matrix (Fin X.rank) (Fin X.rank) (AE D), GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gramᵀ = Gt := ⟨_, rfl⟩
  have hy : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat y)ᵀ * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM J * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat y).map (cA D) =
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM J := y.2
  have e1 : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM (reindex e e X.gramᵀ) = reindex e e Gt := by rw [← hGt]; rfl
  rw [hM, hJ, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM_smul, Matrix.mul_smul, Matrix.smul_mul, e1] at hy
  have hx : incA D D.host.xi0⁻¹ * incA D D.host.xi0 = 1 := by
    rw [← map_mul, inv_mul_cancel₀ GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero, map_one]
  have h1 : Mᵀ * reindex e e Gt * M.map (cA D) = reindex e e Gt := by
    have := congrArg (fun A => incA D D.host.xi0⁻¹ • A) hy
    simpa only [smul_smul, hx, one_smul] using this
  have h2 : (M.submatrix e e)ᵀ * Gt * (M.submatrix e e).map (cA D) = Gt := by
    have := congrArg (fun A => A.submatrix e e) h1
    rw [← submatrix_mul_equiv _ _ _ e _, ← submatrix_mul_equiv _ _ _ e _] at this
    simpa [reindex_apply, transpose_submatrix, submatrix_submatrix, ← Matrix.submatrix_map] using this
  have hT : Gtᵀ = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gram := by rw [← hGt]; exact Matrix.ext fun _ _ => rfl
  have h3 := congrArg transpose h2
  rw [transpose_mul, transpose_mul, transpose_transpose, ← Matrix.mul_assoc, hT] at h3
  rw [← hM, ← hu] at h3
  refine ⟨(⟨u, h3⟩ : HR (AF D.host.F) D.sp.cm.sig X.gram), ?_⟩
  apply Subtype.ext
  apply Units.ext
  show reindex e e u.1 = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat y
  rw [hu]
  ext a b
  simp

end GlobalTheory.SquareAgree
