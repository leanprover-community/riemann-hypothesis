module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RapidVal
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealTranslationCuspFormMapsEqSmoothLinearMapStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ValMoveProof

theorem lev_of_mem {D : D7} (θ : InfFam D) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)
    (J : Set (GA D V)) (χ : GA D V → ℂ) (T : MMap M) (hT : T ∈ Mult θ M J χ) :
    ∀ v, ∀ k ∈ J, ∀ g, T v (g * k) = χ k * T v g := by
  induction hT using Submodule.span_induction with
  | mem x hx => exact hx.lev
  | zero => intros; simp
  | add x y _ _ hx hy =>
    intro v k hk g
    simp only [MultilinearMap.add_apply, Pi.add_apply, hx v k hk g, hy v k hk g, mul_add]
  | smul a x _ hx =>
    intro v k hk g
    simp only [MultilinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, hx v k hk g]
    ring

theorem valMove : ∀ D : D7, ValMove D := by
  intro D θ hθ V S M J χ
  refine ⟨?_, ?_⟩
  · intro G hG x k hk
    rw [mem_multT] at hG
    have h := lev_of_mem θ M J χ _ hG
    have e : ∀ f, G (PiTensorProduct.tprod ℂ f) = (PiTensorProduct.lift.symm G) f := fun f => by
      simp [PiTensorProduct.lift_symm]
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r f =>
      funext g
      simp only [rTrans, map_smul, Pi.smul_apply, smul_eq_mul, e, h f k hk g]
      ring
    | add x y hx hy =>
      funext g
      have hx' := congrFun hx g
      have hy' := congrFun hy g
      simp only [rTrans, map_add (f := _), Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hx' hy' ⊢
      rw [hx', hy', mul_add]
  · intro a ha v
    obtain ⟨σ, hσ⟩ := GlobalTheory.T.realTranslation_cuspFormMaps_eq_smooth_linear_map D θ V S M hθ a ha
    exact ⟨σ v, fun G hG => (hσ J χ G hG v).symm⟩

end GlobalTheory.ValMoveProof

end
