module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FullToGlIsSelfAdjoint
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BorderedInvariantsAndHankelDetMapRingHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisBorderedMatrixNormalFormInvariantsStatement
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.Step.MatchNotIm

section Alg
variable {r : ℕ} {k : Type} [CommRing k]

theorem full_act (g : GL (Fin r) k) (Y : Gl r k) :
    full (act g Y) = embHom r k (g : Matrix (Fin r) (Fin r) k) * full Y *
      embHom r k ((g⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) := by
  simp only [full, act, embHom, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.reindex_apply,
    Matrix.submatrix_mul_equiv]
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  congr 1
  congr 1
  all_goals (ext i j; simp [Matrix.mul_apply, Matrix.mulVec, Matrix.vecMul, dotProduct])

theorem last_eq : (Fin.last r) = finSumFinEquiv (Sum.inr (0 : Fin 1)) := by
  ext; simp

theorem embHom_last_row (g : Matrix (Fin r) (Fin r) k) (j : Fin (r + 1)) :
    embHom r k g (Fin.last r) j = if j = Fin.last r then 1 else 0 := by
  rw [last_eq]
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  rcases j with j | j
  · simp [embHom, Matrix.reindex_apply, Fin.ext_iff, (Fin.is_lt _).ne]
  · rw [Subsingleton.elim j 0]; simp [embHom, Matrix.reindex_apply]

theorem embHom_last_col (g : Matrix (Fin r) (Fin r) k) (i : Fin (r + 1)) :
    embHom r k g i (Fin.last r) = if i = Fin.last r then 1 else 0 := by
  rw [last_eq]
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  rcases i with i | i
  · simp [embHom, Matrix.reindex_apply, Fin.ext_iff, (Fin.is_lt _).ne]
  · rw [Subsingleton.elim i 0]; simp [embHom, Matrix.reindex_apply]

theorem conj_last (g g' : Matrix (Fin r) (Fin r) k) (N : Matrix (Fin (r + 1)) (Fin (r + 1)) k) :
    (embHom r k g * N * embHom r k g') (Fin.last r) (Fin.last r) = N (Fin.last r) (Fin.last r) := by
  simp [Matrix.mul_apply, embHom_last_row, embHom_last_col]

theorem eL_dot (N : Matrix (Fin (r + 1)) (Fin (r + 1)) k) :
    eL r k ⬝ᵥ (N *ᵥ eL r k) = N (Fin.last r) (Fin.last r) := by
  simp [eL, Matrix.mulVec, dotProduct, Pi.single_apply]

theorem full_glMap {k' : Type} [CommRing k'] (φ : k →+* k') (Y : Gl r k) :
    full (glMap φ Y) = (full Y).map φ := by
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  rcases i with i | i <;> rcases j with j | j <;> simp [full, glMap, Matrix.reindex_apply]

end Alg

end GlobalTheory.JR.Step.MatchNotIm

namespace GlobalTheory.JR.Step.MatchNotIm

theorem conj_pow {n : Type} [Fintype n] [DecidableEq n] {k : Type} [CommRing k] (P Q N : Matrix n n k)
    (hPQ : P * Q = 1) (hQP : Q * P = 1) (i : ℕ) : (P * N * Q) ^ i = P * N ^ i * Q := by
  induction i with
  | zero => simp [hPQ]
  | succ i ih =>
    rw [pow_succ, ih, pow_succ]
    calc P * N ^ i * Q * (P * N * Q) = P * N ^ i * (Q * P) * N * Q := by simp only [Matrix.mul_assoc]
      _ = P * (N ^ i * N) * Q := by rw [hQP, Matrix.mul_one, Matrix.mul_assoc P]

theorem hasInv_liftH : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (r : ℕ) (Z : Gl r F) (X : Hn r F E) (μ l : F) (ν : E),
    ν * star ν = algebraMap F E μ → μ ≠ 0 → Delta (inv (GlobalTheory.JR.Step.lift Z μ l)) ≠ 0 → Delta (inv Z) ≠ 0 →
    HasInv X (inv Z) → HasInv (GlobalTheory.JR.Step.liftH X ν l) (inv (GlobalTheory.JR.Step.lift Z μ l)) := by
  intro F E _ _ _ _ _ r Z X μ l ν hν _ _ hΔ hX
  have hΔ' : Delta (inv (glMap (algebraMap F E) Z)) ≠ 0 := by
    rw [InvMap.inv_glMap, InvMap.Delta_map]
    exact (map_ne_zero (algebraMap F E)).2 hΔ
  have hX' : inv X.toGl = inv (glMap (algebraMap F E) Z) := by
    rw [InvMap.inv_glMap]; exact hX
  obtain ⟨g, ⟨hg, -⟩, -⟩ := (GlobalTheory.T.jacquetRallis_borderedMatrix_normalForm_invariants E r).2.2.2.2 _ _ hΔ' hX'
  have hfull : full X.toGl = embHom r E (g : Matrix (Fin r) (Fin r) E) * (full Z).map (algebraMap F E) *
      embHom r E ((g⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) := by
    rw [← hg, full_act, full_glMap]
  have hPQ : embHom r E (g : Matrix (Fin r) (Fin r) E) * embHom r E ((g⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E)
      = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have hQP : embHom r E ((g⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) * embHom r E (g : Matrix (Fin r) (Fin r) E)
      = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have hs : star (ν • eL r E) = star ν • eL r E := by
    funext j
    simp only [Pi.star_apply, Pi.smul_apply, eL, Pi.single_apply, smul_eq_mul, star_mul']
    split_ifs <;> simp [mul_comm]
  replace hfull : full ((X.1.1, X.2.1, star X.2.1, algebraMap F E X.2.2) : Gl r E) =
      embHom r E (g : Matrix (Fin r) (Fin r) E) * (full Z).map (algebraMap F E) *
      embHom r E ((g⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) := hfull
  unfold HasInv
  refine Prod.ext ?_ (Prod.ext ?_ rfl)
  · funext i
    simp only [GlobalTheory.JR.inv, Inv.map, Hn.toGl, liftH, lift]
    rw [hfull]
    rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hQP, Matrix.one_mul, Matrix.charpoly_map, Polynomial.coeff_map]
  · funext i
    simp only [GlobalTheory.JR.inv, Inv.map, Hn.toGl, liftH, lift, mom]
    rw [hs, hfull, conj_pow _ _ _ hPQ hQP, Matrix.mulVec_smul, Matrix.mulVec_smul, dotProduct_smul,
      smul_dotProduct, dotProduct_smul, eL_dot, eL_dot, conj_last]
    have hp : ((full Z).map (algebraMap F E)) ^ (i : ℕ) = ((full Z) ^ (i : ℕ)).map (algebraMap F E) := by
      have := map_pow (algebraMap F E).mapMatrix (full Z) (i : ℕ)
      simpa only [RingHom.mapMatrix_apply] using this.symm
    rw [hp, Matrix.map_apply, smul_eq_mul, smul_eq_mul, smul_eq_mul, map_mul, ← hν]
    ring

end GlobalTheory.JR.Step.MatchNotIm
