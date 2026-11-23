module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagRelativeTangentTopChernRenameBlockPerm
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.TypeStar
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

namespace GlobalTheory.GoodMetric.FibreAntisymm
open GlobalTheory.GoodMetric

theorem rename_chernRoots (ι : Type) [Fintype ι] (m : ι → ℕ) (w : ∀ τ, Equiv.Perm (Fin (m τ)))
    (R : MvPolynomial (ι × ℕ) ℝ) :
    rename (fun x : Root m => (⟨x.1, w x.1 x.2⟩ : Root m)) (chernRoots m R) = chernRoots m R := by
  have h : (rename (fun x : Root m => (⟨x.1, w x.1 x.2⟩ : Root m))).comp (chernRoots m) = chernRoots m := by
    apply MvPolynomial.algHom_ext
    intro x
    simp only [AlgHom.comp_apply, chernRoots, aeval_X, rename_rename]
    have e : ((fun x : Root m => (⟨x.1, w x.1 x.2⟩ : Root m)) ∘ Sigma.mk x.1) = Sigma.mk x.1 ∘ (w x.1) := by
      funext i; rfl
    rw [e, ← rename_rename, rename_esymm]
  exact AlgHom.congr_fun h R

theorem antisymm_chernRoots_mul (ι : Type) [Fintype ι] (m : ι → ℕ) (R : MvPolynomial (ι × ℕ) ℝ)
    (Q : MvPolynomial (Root m) ℝ) : antisymm (chernRoots m R * Q) = chernRoots m R * antisymm Q := by
  unfold antisymm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [map_mul, rename_chernRoots, mul_smul_comm]

theorem prod_Ioi_rev {R : Type*} [CommRing R] {N : ℕ} (v : Fin N → R) :
    (∏ i : Fin N, ∏ j ∈ Finset.Ioi i, (v (Fin.rev i) - v (Fin.rev j))) = ∏ i : Fin N, ∏ j ∈ Finset.Ioi i, (v j - v i) := by
  have h : ∀ f : Fin N → Fin N → R, (∏ i : Fin N, ∏ j ∈ Finset.Ioi i, f i j) =
      ∏ i : Fin N, ∏ j : Fin N, if i < j then f i j else 1 := by
    intro f
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Finset.prod_filter]
    congr 1
    ext j; simp
  rw [h, h, ← Fintype.prod_prod_type' (f := fun i j => if i < j then v (Fin.rev i) - v (Fin.rev j) else 1),
    ← Fintype.prod_prod_type' (f := fun i j => if i < j then v j - v i else 1)]
  refine Fintype.prod_equiv ((Equiv.prodComm _ _).trans (Fin.revPerm.prodCongr Fin.revPerm)) _ _ fun p => ?_
  simp [Fin.rev_lt_rev]

theorem sum_sign_prod_neg_pow {R : Type*} [CommRing R] {N : ℕ} (v : Fin N → R) :
    (∑ σ : Equiv.Perm (Fin N), (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : R) * ∏ i : Fin N, (-v (σ i)) ^ (N - 1 - (i : ℕ))) =
      ∏ j : Fin N, ∏ i ∈ Finset.Iio j, (v j - v i) := by
  let M : Matrix (Fin N) (Fin N) R := Matrix.of fun j i => (-v j) ^ (N - 1 - (i : ℕ))
  have h1 : M.det = ∑ σ : Equiv.Perm (Fin N), (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : R) * ∏ i : Fin N, (-v (σ i)) ^ (N - 1 - (i : ℕ)) := by
    rw [Matrix.det_apply']
    rfl
  have h2 : M.submatrix Fin.revPerm Fin.revPerm = Matrix.vandermonde (fun j => -v (Fin.rev j)) := by
    ext j i
    simp only [M, Matrix.submatrix_apply, Matrix.of_apply, Matrix.vandermonde_apply, Fin.revPerm_apply, Fin.val_rev]
    congr 1
    omega
  rw [← h1, ← Matrix.det_submatrix_equiv_self Fin.revPerm, h2, Matrix.det_vandermonde,
    GlobalTheory.GoodMetric.RootDiscrPerm.prod_Iio_eq_det, Matrix.det_vandermonde, ← prod_Ioi_rev]
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
  simp only [Fin.rev_rev]
  ring

theorem antisymm_fibrePoint (ι : Type) [Fintype ι] (m : ι → ℕ) : antisymm (fibrePoint m) = rootDiscr m := by
  have hw : ∀ w : ∀ τ, Equiv.Perm (Fin (m τ)),
      ((∏ τ, Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) • rename (fun x : Root m => (⟨x.1, w x.1 x.2⟩ : Root m)) (fibrePoint m) =
        ∏ τ, ((((Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) : MvPolynomial (Root m) ℝ) *
          ∏ i : Fin (m τ), (-(X (⟨τ, w τ i⟩ : Root m) : MvPolynomial (Root m) ℝ)) ^ (m τ - 1 - (i : ℕ))) := by
    intro w
    unfold fibrePoint
    rw [map_prod, Fintype.prod_sigma, zsmul_eq_mul, Units.coe_prod, Int.cast_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    simp [map_pow, map_neg, rename_X]
  unfold antisymm
  rw [Finset.sum_congr rfl fun w _ => hw w]
  rw [← Fintype.prod_sum (fun τ (σ : Equiv.Perm (Fin (m τ))) => ((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : MvPolynomial (Root m) ℝ) *
          ∏ i : Fin (m τ), (-(X (⟨τ, σ i⟩ : Root m) : MvPolynomial (Root m) ℝ)) ^ (m τ - 1 - (i : ℕ))))]
  unfold rootDiscr
  refine Finset.prod_congr rfl fun τ _ => ?_
  exact sum_sign_prod_neg_pow (fun i : Fin (m τ) => (X (⟨τ, i⟩ : Root m) : MvPolynomial (Root m) ℝ))

end GlobalTheory.GoodMetric.FibreAntisymm

namespace GlobalTheory.GoodMetric

theorem antisymm_chernRoots_mul_fibrePoint : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (R : MvPolynomial (ι × ℕ) ℝ),
    GlobalTheory.GoodMetric.antisymm (GlobalTheory.GoodMetric.chernRoots m R * GlobalTheory.GoodMetric.fibrePoint m) =
      GlobalTheory.GoodMetric.chernRoots m R * GlobalTheory.GoodMetric.rootDiscr m := by
  intro ι _ m R
  rw [FibreAntisymm.antisymm_chernRoots_mul, FibreAntisymm.antisymm_fibrePoint]

end GlobalTheory.GoodMetric
