module

import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsBasisOfIsExtension
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsExtensionOfIsPushout
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Algebra.MvPolynomial.Funext
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
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Dual.Lemmas

@[expose] public section

noncomputable section

namespace GlobalTheory.FieldBaseChange

variable {K F : Type} [Field K] [Field F] [Algebra K F]

theorem exists_functional_det_map_ne_zero [Infinite K] {n : Type} [Fintype n] [DecidableEq n]
    (M : Matrix n n F) (hM : M.det ≠ 0) : ∃ ℓ : F →ₗ[K] K, (M.map ℓ).det ≠ 0 := by
  classical
  let e := Module.Basis.ofVectorSpace K F
  let φ : F →ₗ[K] MvPolynomial (Module.Basis.ofVectorSpaceIndex K F) K := e.constr K MvPolynomial.X
  by_contra h
  push Not at h
  have hP : (M.map φ).det = 0 := by
    refine MvPolynomial.funext fun c => ?_
    have hc : ∀ x, MvPolynomial.aeval c (φ x) = e.constr K c x := fun x =>
      LinearMap.congr_fun (e.ext (f₁ := (MvPolynomial.aeval c).toLinearMap ∘ₗ φ) (f₂ := e.constr K c)
        (fun i => by simp [φ])) x
    rw [map_zero, ← h (e.constr K c), RingHom.map_det]
    congr 1
    ext i j
    exact hc _
  have hc : ∀ x, MvPolynomial.aeval e (φ x) = x := fun x =>
    LinearMap.congr_fun (e.ext (f₁ := (MvPolynomial.aeval e).toLinearMap ∘ₗ φ) (f₂ := LinearMap.id)
      (fun i => by simp [φ])) x
  apply hM
  have := congrArg (MvPolynomial.aeval (R := K) e) hP
  rw [map_zero, AlgHom.map_det] at this
  rw [← this]
  congr 1
  ext i j
  exact (hc _).symm

variable {V W V' W' : Type} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  [AddCommGroup V'] [Module F V'] [AddCommGroup W'] [Module F W']

theorem IsExtension.exists_basis {a : V →ₛₗ[algebraMap K F] V'} (h : IsExtension a) {ι : Type}
    (v : Module.Basis ι K V) : ∃ v' : Module.Basis ι F V', ∀ i, v' i = a (v i) := by
  apply GlobalTheory.ConstFam.exists_basis_of_isExtension <;> assumption

theorem IsCoord.map_algebraMap_smul {a : V →ₛₗ[algebraMap K F] V'}
    (h : Submodule.span F (Set.range a) = ⊤) {ℓ : F →ₗ[K] K} {Λ : V' →+ V} (hΛ : IsCoord a ℓ Λ)
    (k : K) (x : V') : Λ (algebraMap K F k • x) = k • Λ x :=
  IsCoord.natural h hΛ hΛ (k • LinearMap.id) (algebraMap K F k • LinearMap.id)
    (fun v => by simp [map_smulₛₗ]) x

theorem exists_intertwining_bijective_of_extension (K F : Type) [Field K] [Field F] [Algebra K F]
    [Infinite K] (V W V' W' : Type) [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup V'] [Module F V'] [AddCommGroup W'] [Module F W'] [FiniteDimensional F V']
    (iV : V →ₛₗ[algebraMap K F] V') (iW : W →ₛₗ[algebraMap K F] W')
    (hV : IsExtension iV) (hW : IsExtension iW)
    (J : Type) (a : J → V →ₗ[K] V) (b : J → W →ₗ[K] W) (a' : J → V' →ₗ[F] V') (b' : J → W' →ₗ[F] W')
    (ha : ∀ i v, a' i (iV v) = iV (a i v)) (hb : ∀ i w, b' i (iW w) = iW (b i w))
    (E' : V' →ₗ[F] W') (hE' : Function.Bijective E') (hc : ∀ i v, E' (a' i v) = b' i (E' v)) :
    ∃ E : V →ₗ[K] W, Function.Bijective E ∧ ∀ i v, E (a i v) = b i (E v) := by
  classical
  let v := Module.Basis.ofVectorSpace K V
  let w₀ := Module.Basis.ofVectorSpace K W
  obtain ⟨v', hv'⟩ := hV.exists_basis v
  obtain ⟨w₀', -⟩ := hW.exists_basis w₀
  let e := LinearEquiv.ofBijective E' hE'
  let w := w₀.reindex (w₀'.indexEquiv (v'.map e))
  obtain ⟨w', hw'⟩ := hW.exists_basis w
  haveI := Module.Finite.finite_basis v'
  letI := Fintype.ofFinite (Module.Basis.ofVectorSpaceIndex K V)
  have hdet : (LinearMap.toMatrix v' w' E').det ≠ 0 := (LinearEquiv.isUnit_det e v' w').ne_zero
  obtain ⟨ℓ, hℓ⟩ := exists_functional_det_map_ne_zero (K := K) _ hdet
  obtain ⟨Λ, hΛ⟩ := hW.coord ℓ
  let E : V →ₗ[K] W :=
    { toFun := fun x => Λ (E' (iV x))
      map_add' := fun x y => by simp only [map_add (f := _)]
      map_smul' := fun k x => by
        rw [map_smulₛₗ, map_smul, hΛ.map_algebraMap_smul hW.span]; rfl }
  have hM : LinearMap.toMatrix v w E = (LinearMap.toMatrix v' w' E').map ℓ := by
    ext i j
    rw [LinearMap.toMatrix_apply, Matrix.map_apply, LinearMap.toMatrix_apply]
    have : E (v j) = ∑ k, ℓ (w'.repr (E' (v' j)) k) • w k := by
      show Λ (E' (iV (v j))) = _
      rw [← hv']

      conv_lhs => rw [← w'.sum_repr (E' (v' j)), map_sum]
      simp only [hw', hΛ _ _]
    rw [this, w.repr_sum_self]
  refine ⟨E, ?_, fun i x => ?_⟩
  · have hu : IsUnit (LinearMap.toMatrix v w E).det := by rw [hM]; exact hℓ.isUnit
    exact (LinearEquiv.ofIsUnitDet hu).bijective
  · show Λ (E' (iV (a i x))) = b i (Λ (E' (iV x)))
    rw [← ha, hc]
    exact IsCoord.natural hW.span hΛ hΛ (b i) (b' i) (hb i) _

end GlobalTheory.FieldBaseChange
