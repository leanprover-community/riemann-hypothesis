module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Hom
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
public import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.PeriodVol

def reImCoord (g : ℕ) : (Fin g → ℂ) ≃ₗ[ℝ] (Fin g ⊕ Fin g → ℝ) where
  toFun z := Sum.elim (fun i => (z i).re) (fun i => (z i).im)
  invFun p := fun i => ⟨p (Sum.inl i), p (Sum.inr i)⟩
  map_add' z w := by ext (i | i) <;> simp
  map_smul' c z := by ext (i | i) <;> simp
  left_inv z := rfl
  right_inv p := by ext (i | i) <;> rfl

theorem volume_fundamentalDomain_reImCoord (g : ℕ) :
    volume (ZSpan.fundamentalDomain (Module.Basis.ofEquivFun (reImCoord g))) = 1 := by
  have h : ZSpan.fundamentalDomain (Module.Basis.ofEquivFun (reImCoord g)) =
      Set.pi Set.univ fun _ : Fin g =>
        Complex.measurableEquivRealProd ⁻¹' (Set.Ico (0 : ℝ) 1 ×ˢ Set.Ico (0 : ℝ) 1) := by
    ext z
    simp [ZSpan.fundamentalDomain, forall_and]
    tauto
  rw [h, volume_pi_pi]
  refine Finset.prod_eq_one fun _ _ => ?_
  rw [Complex.volume_preserving_equiv_real_prod.measure_preimage
    (measurableSet_Ico.prod measurableSet_Ico).nullMeasurableSet]
  simp [Measure.volume_eq_prod]

def periodMap {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) :=
  ((reImCoord g).symm : (Fin g ⊕ Fin g → ℝ) →ₗ[ℝ] (Fin g → ℂ)) ∘ₗ
    Matrix.toLin' (Matrix.fromBlocks 1 (τ.map Complex.re) 0 (τ.map Complex.im)) ∘ₗ
      ((reImCoord g).symm.symm : (Fin g → ℂ) →ₗ[ℝ] (Fin g ⊕ Fin g → ℝ))

theorem det_periodMap {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) :
    LinearMap.det (periodMap τ) = (τ.map Complex.im).det := by
  rw [periodMap, LinearMap.det_conj, LinearMap.det_toLin', Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_one, _root_.one_mul]

theorem periodMap_apply {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (z : Fin g → ℂ) :
    periodMap τ z = (fun i => ((z i).re : ℂ)) + τ.mulVec (fun i => ((z i).im : ℂ)) := by
  ext i
  apply Complex.ext
  · change (Matrix.fromBlocks 1 (τ.map Complex.re) 0 (τ.map Complex.im)).mulVec
      (Sum.elim (fun j => (z j).re) (fun j => (z j).im)) (Sum.inl i) = _
    simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.one_apply]
  · change (Matrix.fromBlocks 1 (τ.map Complex.re) 0 (τ.map Complex.im)).mulVec
      (Sum.elim (fun j => (z j).re) (fun j => (z j).im)) (Sum.inr i) = _
    simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.one_apply]

end GlobalTheory.PeriodVol

namespace GlobalTheory

open PeriodVol

theorem volume_fundamentalDomain_periodLattice :
    ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (φ : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (τ : Matrix (Fin g) (Fin g) ℂ),
    (τ.map Complex.im).PosDef →
    (∀ z, φ z ∈ Λ ↔ ∃ m n : Fin g → ℤ, z = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))) →
    ∀ Fd : Set (Fin g → ℂ), IsAddFundamentalDomain Λ Fd volume →
    (volume Fd).toReal = ‖LinearMap.det (φ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))‖ ^ 2 * (τ.map Complex.im).det := by
  intro g Λ φ τ hτ hΛ Fd hFd
  have hpos := hτ.det_pos
  let S : (Fin g → ℂ) ≃ₗ[ℝ] (Fin g → ℂ) :=
    LinearMap.equivOfDetNeZero (periodMap τ) (by rw [det_periodMap]; exact hpos.ne')
  have hS : ∀ z, S z = periodMap τ z := fun z => rfl
  let T : (Fin g → ℂ) ≃ₗ[ℝ] (Fin g → ℂ) := S.trans (φ.restrictScalars ℝ)
  let b₀ := Module.Basis.ofEquivFun (reImCoord g)
  have hspan : Λ = Submodule.span ℤ (Set.range (b₀.map T)) := by
    ext w
    obtain ⟨z, rfl⟩ := T.surjective w
    rw [Module.Basis.mem_span_iff_repr_mem]
    change φ (S z) ∈ Λ ↔ _
    rw [hΛ]
    simp only [Module.Basis.map_repr, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, b₀,
      Module.Basis.ofEquivFun_repr_apply]
    constructor
    · rintro ⟨m, n, h⟩
      have : z = fun i => ⟨m i, n i⟩ := S.injective (by rw [h, hS, periodMap_apply]; simp)
      subst this
      rintro (i | i)
      · exact ⟨m i, rfl⟩
      · exact ⟨n i, rfl⟩
    · intro h
      choose k hk using h
      refine ⟨fun i => k (Sum.inl i), fun i => k (Sum.inr i), ?_⟩
      have h1 : ∀ i, (z i).re = k (Sum.inl i) := fun i => (hk (Sum.inl i)).symm
      have h2 : ∀ i, (z i).im = k (Sum.inr i) := fun i => (hk (Sum.inr i)).symm
      rw [hS, periodMap_apply]
      simp [h1, h2]
  subst hspan
  have hdet : b₀.det (b₀.map T) =
      ‖LinearMap.det (φ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))‖ ^ 2 * (τ.map Complex.im).det := by
    have hT : (T : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ)) =
        (φ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)).restrictScalars ℝ ∘ₗ periodMap τ := rfl
    have : ⇑(b₀.map T) = (T : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ)) ∘ b₀ := by
      ext1 i; simp
    rw [this, Module.Basis.det_comp, Module.Basis.det_self, _root_.mul_one, hT, LinearMap.det_comp,
      det_periodMap, LinearMap.det_restrictScalars, Algebra.norm_complex_apply,
      Complex.normSq_eq_norm_sq]
  have : VAddInvariantMeasure (Submodule.span ℤ (Set.range (b₀.map T))) (Fin g → ℂ) volume :=
    ⟨fun c s _ => measure_preimage_add volume (c : Fin g → ℂ) s⟩
  rw [hFd.measure_eq (ZSpan.isAddFundamentalDomain (b₀.map T) volume),
    ZSpan.measure_fundamentalDomain _ volume b₀, volume_fundamentalDomain_reImCoord, _root_.mul_one, hdet,
    ENNReal.toReal_ofReal (abs_nonneg _), abs_of_nonneg (by positivity)]

end GlobalTheory
