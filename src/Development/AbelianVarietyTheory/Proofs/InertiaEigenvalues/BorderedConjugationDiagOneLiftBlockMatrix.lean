module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FullToGlIsSelfAdjoint
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.Step.ActEmbLift

theorem embHom_mul_full_mul (k : Type) [CommRing k] (r : ℕ) (g h : Matrix (Fin r) (Fin r) k) (Z : Gl r k) :
    embHom r k g * full Z * embHom r k h = full (g * Z.1 * h, g *ᵥ Z.2.1, Z.2.2.1 ᵥ* h, Z.2.2.2) := by
  simp only [embHom, MonoidHom.coe_mk, OneHom.coe_mk, full, Matrix.reindex_apply]
  rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  congr 2
  · simp
  · ext i j; simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  · ext i j; simp [Matrix.mul_apply, Matrix.vecMul, dotProduct]
  · ext i j; simp [Matrix.mul_apply]

theorem embHom_mulVec_eL (k : Type) [CommRing k] (r : ℕ) (g : Matrix (Fin r) (Fin r) k) :
    embHom r k g *ᵥ eL r k = eL r k := by
  ext i
  simp only [embHom, MonoidHom.coe_mk, OneHom.coe_mk, eL, Matrix.reindex_apply]
  rw [Matrix.mulVec_single_one]
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [Matrix.transpose_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_last]
  · simp [Matrix.transpose_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_last, finSumFinEquiv_symm_apply_castSucc]

theorem eL_vecMul_embHom (k : Type) [CommRing k] (r : ℕ) (g : Matrix (Fin r) (Fin r) k) :
    eL r k ᵥ* embHom r k g = eL r k := by
  ext i
  simp only [embHom, MonoidHom.coe_mk, OneHom.coe_mk, eL, Matrix.reindex_apply]
  rw [Matrix.single_one_vecMul]
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [Matrix.submatrix_apply, finSumFinEquiv_symm_last]
  · simp [Matrix.submatrix_apply, finSumFinEquiv_symm_last, finSumFinEquiv_symm_apply_castSucc]

theorem act_emb_lift (k : Type) [CommRing k] (r : ℕ) (g : GL (Fin r) k) (Z : Gl r k) (μ l : k) :
    act (GlobalTheory.JR.Step.emb r k g) (GlobalTheory.JR.Step.lift Z μ l) = GlobalTheory.JR.Step.lift (act g Z) μ l := by
  have hinv : ((emb r k g)⁻¹ : GL (Fin (r + 1)) k) = emb r k g⁻¹ := (map_inv _ _).symm
  simp only [act, lift, hinv, emb, Units.coe_map, MonoidHom.coe_coe]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ rfl))
  · exact embHom_mul_full_mul k r _ _ Z
  · simp only [Matrix.mulVec_smul, embHom_mulVec_eL]
  · exact eL_vecMul_embHom k r _

end GlobalTheory.JR.Step.ActEmbLift
