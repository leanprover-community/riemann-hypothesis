module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.TypeStar
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric

namespace GlobalTheory.GoodMetric.RootDiscrPerm

theorem prod_Iio_eq_det {R : Type*} [CommRing R] {N : ℕ} (v : Fin N → R) :
    (∏ j : Fin N, ∏ i ∈ Finset.Iio j, (v j - v i)) = (Matrix.vandermonde v).det := by
  rw [Matrix.det_vandermonde]
  exact Finset.prod_comm' (fun j i => by simp [and_comm])

theorem det_vandermonde_comp_perm {R : Type*} [CommRing R] {N : ℕ} (v : Fin N → R) (σ : Equiv.Perm (Fin N)) :
    (Matrix.vandermonde (fun i => v (σ i))).det = ((Equiv.Perm.sign σ : ℤˣ) : ℤ) * (Matrix.vandermonde v).det := by
  have h : Matrix.vandermonde (fun i => v (σ i)) = (Matrix.vandermonde v).submatrix σ id := by
    ext i k; simp [Matrix.vandermonde_apply]
  rw [h, Matrix.det_permute]

theorem rootDiscr_eq_prod_det (ι : Type) [Fintype ι] (m : ι → ℕ) :
    rootDiscr m = ∏ τ, (Matrix.vandermonde (fun i : Fin (m τ) => (X ⟨τ, i⟩ : MvPolynomial (Root m) ℝ))).det := by
  unfold rootDiscr
  exact Finset.prod_congr rfl fun τ _ => prod_Iio_eq_det _

end GlobalTheory.GoodMetric.RootDiscrPerm

open GlobalTheory.GoodMetric.RootDiscrPerm in
theorem GlobalTheory.GoodMetric.rename_sigmaCongrRight_rootDiscr : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (w : ∀ τ, Equiv.Perm (Fin (m τ))), rename (Equiv.sigmaCongrRight w) (rootDiscr m) = ((∏ τ, Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) • rootDiscr m := by
  intro ι _ m w
  rw [rootDiscr_eq_prod_det, map_prod]
  have h : ∀ τ, rename (Equiv.sigmaCongrRight w)
      (Matrix.vandermonde (fun i : Fin (m τ) => (X ⟨τ, i⟩ : MvPolynomial (Root m) ℝ))).det =
      ((Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) * (Matrix.vandermonde (fun i : Fin (m τ) => (X ⟨τ, i⟩ : MvPolynomial (Root m) ℝ))).det := by
    intro τ
    rw [AlgHom.map_det]
    have e : (rename (Equiv.sigmaCongrRight w) : MvPolynomial (Root m) ℝ →ₐ[ℝ] MvPolynomial (Root m) ℝ).mapMatrix
        (Matrix.vandermonde (fun i : Fin (m τ) => (X ⟨τ, i⟩ : MvPolynomial (Root m) ℝ))) =
        Matrix.vandermonde (fun i : Fin (m τ) => (X ⟨τ, w τ i⟩ : MvPolynomial (Root m) ℝ)) := by
      ext i k; simp [Matrix.vandermonde_apply]
    rw [e]
    exact det_vandermonde_comp_perm (fun i : Fin (m τ) => (X ⟨τ, i⟩ : MvPolynomial (Root m) ℝ)) (w τ)
  rw [Finset.prod_congr rfl fun τ _ => h τ, Finset.prod_mul_distrib, zsmul_eq_mul]
  push_cast
  rfl
