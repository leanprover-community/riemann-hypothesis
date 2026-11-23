module

public import Formalism.ConjugateSelfDual.Statement
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TripleAtt
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm

@[expose] public section

open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.PurityInvariants

theorem isRoot_of_eigen {R K : Type} [CommRing R] [Field K] (f : R →+* K) (ι : K →+* ℂ) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) (c : K) (x : Fin n → K) (hx : x ≠ 0)
    (h : (M.map f).mulVec x = c • x) : (M.charpoly.map (ι.comp f)).IsRoot (ι c) := by
  classical
  have hdet : (Matrix.scalar (Fin n) c - M.map f).det = 0 := by
    rw [← Matrix.exists_mulVec_eq_zero_iff]
    refine ⟨x, hx, ?_⟩
    rw [Matrix.sub_mulVec, h]
    ext j
    simp [Matrix.scalar_apply]
  have hroot : ((M.map f).charpoly).eval c = 0 := by
    rw [Matrix.eval_charpoly]
    exact hdet
  unfold Polynomial.IsRoot
  rw [← Polynomial.map_map, ← Matrix.charpoly_map, Polynomial.eval_map, Polynomial.eval₂_hom,
    hroot, map_zero]

theorem eigen_of_dual {R K : Type} [CommRing R] [Field K] (f : R →+* K) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) (hM : IsUnit M.det) (c : R) (x : Fin n → K)
    (h : ((c • M⁻¹.transpose).map f).mulVec x = x) : (M.transpose.map f).mulVec x = f c • x := by
  have key : M.transpose * (c • M⁻¹.transpose) = c • (1 : Matrix (Fin n) (Fin n) R) := by
    rw [Matrix.mul_smul, ← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ hM, Matrix.transpose_one]
  calc (M.transpose.map f).mulVec x
      = (M.transpose.map f).mulVec (((c • M⁻¹.transpose).map f).mulVec x) := by rw [h]
    _ = ((M.transpose * (c • M⁻¹.transpose)).map f).mulVec x := by
        rw [Matrix.mulVec_mulVec, Matrix.map_mul]
    _ = f c • x := by
        rw [key]
        ext j
        simp [Matrix.mulVec, dotProduct, Matrix.one_apply, apply_ite f, ite_mul, Finset.sum_ite_eq]

theorem one_lt_norm {E : Type} [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)) :
    (1 : ℝ) < ((normV v : ℕ) : ℝ) := by
  have h1 : normV v = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rfl
  have hne1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact v.isPrime.ne_top
  have hne0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  have : 1 < normV v := by omega
  exact_mod_cast this

end GlobalTheory.PurityInvariants
