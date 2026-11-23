module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsStmt
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.ContDiff.Bounds
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open UpperTheory.V.Lit.Geo.Cs

theorem UpperTheory.V.Lit.Geo.Cs.altEv :
    AltEv := by
  classical
  intro V F _ _ _ _ _ _ q k
  let bs := Module.finBasis ℝ V
  let L : (V [⋀^Fin q]→L[ℝ] F) →ₗ[ℝ] ((Fin q → Fin (Module.finrank ℝ V)) → F) :=
    { toFun := fun g σ => g (fun i => bs (σ i))
      map_add' := fun g h => by ext σ; simp
      map_smul' := fun c g => by ext σ; simp }
  have hker : LinearMap.ker L = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro g hg
    have e : g.toAlternatingMap = (0 : V [⋀^Fin q]→L[ℝ] F).toAlternatingMap :=
      Module.Basis.ext_alternating bs (fun v _ => by simpa [L] using congrFun hg v)
    ext m
    simpa using DFunLike.congr_fun e m
  obtain ⟨M, hM⟩ := L.exists_leftInverse_of_injective hker
  let A : (Fin q → Fin (Module.finrank ℝ V)) → F →L[ℝ] (V [⋀^Fin q]→L[ℝ] F) := fun σ =>
    LinearMap.toContinuousLinearMap (M.comp (LinearMap.single ℝ (fun _ => F) σ))
  refine ⟨Finset.univ.image (fun σ : Fin q → Fin (Module.finrank ℝ V) => fun i => bs (σ i)),
    ∑ σ, ‖A σ‖, Finset.sum_nonneg (fun _ _ => norm_nonneg _), ?_⟩
  intro f x b hb hcd hsz
  have mem : ∀ σ : Fin q → Fin (Module.finrank ℝ V),
      (fun i => bs (σ i)) ∈ Finset.univ.image (fun σ : Fin q → Fin (Module.finrank ℝ V) =>
        fun i => bs (σ i)) :=
    fun σ => Finset.mem_image_of_mem _ (Finset.mem_univ σ)
  have hrep : f = fun y => ∑ σ, A σ (f y (fun i => bs (σ i))) := by
    funext y
    calc f y = M (L (f y)) := (LinearMap.congr_fun hM (f y)).symm
      _ = M (∑ σ, Pi.single σ (L (f y) σ)) := by rw [Finset.univ_sum_single]
      _ = ∑ σ, A σ (f y (fun i => bs (σ i))) := by

        rw [map_sum]
        rfl
  intro i hi
  have hcdi : ∀ σ : Fin q → Fin (Module.finrank ℝ V),
      ContDiffAt ℝ i (fun y => f y (fun i => bs (σ i))) x :=
    fun σ => (hcd _ (mem σ)).of_le (by exact_mod_cast le_top)
  have hsum := iteratedFDeriv_fun_sum_apply (𝕜 := ℝ) (n := i) (x := x) (u := Finset.univ)
    (f := fun σ y => A σ (f y (fun i => bs (σ i))))
    (fun σ _ => (A σ).contDiff.contDiffAt.comp x (hcdi σ))
  rw [hrep, hsum, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun σ _ => ?_)
  refine ((A σ).norm_iteratedFDeriv_comp_left (hcdi σ) le_rfl).trans ?_
  exact mul_le_mul_of_nonneg_left (hsz _ (mem σ) i hi) (norm_nonneg _)
