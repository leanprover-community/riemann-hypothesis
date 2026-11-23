module

public import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.IsSimpleFam
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker

noncomputable section

namespace GlobalTheory.CompanionTheory.ZuckMatHom

theorem mAct_coord {ι ι' V : Type} [Fintype ι] [AddCommGroup V] [Module ℂ V] (A : Matrix ι' ι ℂ)
    (x : ι → V) (c : ι') : mAct A x c = ∑ d, A c d • x d := by
  simp [mAct, LinearMap.sum_apply]

theorem mAct_mAct {ι ι' ι'' V : Type} [Fintype ι] [Fintype ι'] [AddCommGroup V] [Module ℂ V]
    (A : Matrix ι'' ι' ℂ) (B : Matrix ι' ι ℂ) (x : ι → V) :
    mAct A (mAct B x) = mAct (A * B) x := by
  funext c
  simp only [mAct_coord, Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]
  exact Finset.sum_comm

theorem dOp_mAct {ι ι' V V' : Type} [Fintype ι] [AddCommGroup V] [Module ℂ V] [AddCommGroup V']
    [Module ℂ V'] (A : Matrix ι' ι ℂ) (T : V →ₗ[ℂ] V') (x : ι → V) :
    dOp ι' T (mAct A x) = mAct A (dOp ι T x) := by
  funext c
  have h : ∀ (κ : Type) (y : κ → V) (e : κ), dOp κ T y e = T (y e) := fun _ _ _ => rfl

  simp only [h, mAct_coord, map_sum, map_smul]

theorem dsigW_eq_prod {k r : ℕ} (U : URep k r) :
    ∀ (W : List (Formalism.FourierDecayAlt.ThreeDimData.Mx k r)), LieWd k r W → ∀ v : U.R.smSub,
      PI.UpqRep.dsigW (k := k) (r := r) U.R.σ W (v : U.R.H) = ((W.map U.dsig).prod v : U.R.H)
  | [], _, _ => rfl
  | X :: W, hW, v => by
    have ih := dsigW_eq_prod U W (fun Y hY => hW Y (List.mem_cons_of_mem _ hY)) v
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply,
      URep.dsig_coe U (hW X List.mem_cons_self), ← ih]
    rfl

theorem matHom : MatHom := by
  intro k r F F' U A hA
  refine ⟨fun W hW => ⟨∑ c : F'.ι, ∑ d : F.ι, ‖A c d‖, [W], ?_, fun x => ?_⟩, fun g hg => ?_⟩
  · intro W' hW'
    rw [List.mem_singleton.1 hW']
    exact hW
  · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    change ∑ c : F'.ι, ‖PI.UpqRep.dsigW (k := k) (r := r) U.R.σ W ((mAct A x c : U.R.smSub) : U.R.H)‖ ≤
      (∑ c : F'.ι, ∑ d : F.ι, ‖A c d‖) *
        ∑ e : F.ι, ‖PI.UpqRep.dsigW (k := k) (r := r) U.R.σ W ((x e : U.R.smSub) : U.R.H)‖
    simp only [dsigW_eq_prod U W hW]
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun c _ => ?_

    rw [mAct_coord, map_sum, Submodule.coe_sum, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun d _ => ?_)
    rw [map_smul, Submodule.coe_smul, norm_smul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    exact Finset.single_le_sum
      (f := fun e => ‖(((W.map U.dsig).prod (x e) : U.R.smSub) : U.R.H)‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ d)
  · refine LinearMap.ext fun x => ?_
    change mAct A (mAct (F.ρ g) (dOp F.ι (U.sig g) x)) = mAct (F'.ρ g) (dOp F'.ι (U.sig g) (mAct A x))
    rw [dOp_mAct, mAct_mAct, mAct_mAct, hA g hg]

end GlobalTheory.CompanionTheory.ZuckMatHom

end
