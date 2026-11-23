module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LineBasis
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
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
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PerCApply

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem exists_coords {K C V : Type} [Field K] [Ring C] [Algebra K C] [Algebra ℚ K] [Algebra ℚ C]
    [IsScalarTower ℚ K C] [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V] [FiniteDimensional ℚ K]
    [FiniteDimensional K C] (n : ℕ)
    (rep : C →ₐ[ℚ] Module.End ℚ V) (hinj : Function.Injective rep) (hC : Module.finrank K C = n ^ 2)
    (hdim : Module.finrank ℚ V = n * Module.finrank ℚ K) :
    ∃ (kp : V ≃+ (Fin n → K)) (σ : C ≃ₐ[K] Matrix (Fin n) (Fin n) K), ∀ c w, kp (rep c w) = σ c *ᵥ kp w := by
  let f : K →+* Module.End ℚ V := (rep : C →+* Module.End ℚ V).comp (algebraMap K C)
  letI : Module K V := Module.compHom V f
  have hsm : ∀ (x : K) (w : V), x • w = rep (algebraMap K C x) w := fun _ _ => rfl
  haveI : IsScalarTower ℚ K V := by
    refine ⟨fun q x w => ?_⟩
    rw [hsm, hsm, ← IsScalarTower.toAlgHom_apply ℚ K C, map_smul, map_smul]
    rfl
  haveI : Module.Finite K V := Module.Finite.of_restrictScalars_finite ℚ K V
  have hfin : Module.finrank K V = n := by
    have h := Module.finrank_mul_finrank ℚ K V
    have hpos : 0 < Module.finrank ℚ K := Module.finrank_pos
    rw [hdim, mul_comm n] at h
    exact Nat.eq_of_mul_eq_mul_left hpos h
  let b : Module.Basis (Fin n) K V := Module.finBasisOfFinrankEq K V hfin
  let r : C →ₐ[K] Module.End K V := AlgHom.ofLinearMap
    { toFun := fun c =>
        { toFun := rep c
          map_add' := map_add _
          map_smul' := fun x w => by
            simp only [RingHom.id_apply, hsm]
            rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, Algebra.commutes] }
      map_add' := fun c c' => by ext w; simp
      map_smul' := fun x c => by
        ext w
        simp [hsm, Algebra.smul_def, Module.End.mul_apply] }
    (by ext w; simp) (fun c c' => by ext w; simp [Module.End.mul_apply])
  have hr : ∀ c w, r c w = rep c w := fun _ _ => rfl
  let s : C →ₐ[K] Matrix (Fin n) (Fin n) K := (LinearMap.toMatrixAlgEquiv b).toAlgHom.comp r
  have hsinj : Function.Injective s := by
    intro c c' h
    have h' : r c = r c' := (LinearMap.toMatrixAlgEquiv b).injective h
    apply hinj
    ext w
    exact congrArg (fun g => g w) h'
  have hrk : Module.finrank K C = Module.finrank K (Matrix (Fin n) (Fin n) K) := by
    rw [hC, Module.finrank_matrix, Module.finrank_self, Fintype.card_fin]
    ring
  have hsurj : Function.Surjective s :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := s.toLinearMap) hrk).1 hsinj
  refine ⟨b.equivFun.toAddEquiv, AlgEquiv.ofBijective s ⟨hsinj, hsurj⟩, fun c w => ?_⟩
  have h := LinearMap.toMatrix_mulVec_repr b b (r c) w
  exact h.symm

theorem UpperTheory.Gal.W2.fMat_of :
    UpperTheory.Gal.W2.FMat := by
  intro p _ D G L hm
  haveI := D.freeLa
  haveI := D.finLa
  have hK : Module.finrank ℚ G.F = Module.finrank ℚ D.F :=
    ((AlgEquiv.ofRingEquiv (f := L.e) (fun q => map_ratCast L.e q)).toLinearEquiv.finrank_eq).symm
  have hdim : Module.finrank ℚ (VQ D) = G.n * Module.finrank ℚ G.F := by
    rw [Module.finrank_baseChange, D.rankLa, hm, Nat.one_mul, L.n_eq, hK]
  exact exists_coords G.n L.rep L.rep_inj G.rankC hdim
