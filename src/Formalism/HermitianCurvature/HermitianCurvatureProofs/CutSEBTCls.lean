module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSE2
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HasFDerivAtFsvOther
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftMemMatrixAlgebra
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SumPairLevStarMul
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA

section BTClsPf

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem opClos_op (X : ActualOps k r z z' π π') (l : Fin r) (B : Submodule ℂ (RadSp k r z z' π π')) (j : Fin 6) :
    ∀ Φ ∈ OpClos X l B, X.op l j Φ ∈ OpClos X l B := by
  intro Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨js, Ψ, hΨ, rfl⟩ := hx
    exact Submodule.subset_span ⟨j :: js, Ψ, hΨ, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx

theorem act_mem_of_entSub {S : Type} [Fintype S] [DecidableEq S] (C : Submodule ℂ (RadSp k r z z' π π'))
    (M : SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π'))) (hM : M ∈ entSub (presAlg C)) (u : Ix S → RadSp k r z z' π π')
    (hu : ∀ b, u b ∈ C) (b : Ix S) : act M u b ∈ C := by
  exact Formalism.FourierDecayAlt.P5.HerA.act_mem_pres M (fun a c => hM a c) u hu b

end BTClsPf

theorem boundary_torus_closure : BTCls := by
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 D hD _ _ _ _ _ _ l _ u hu
  have hAL := hD.2.2.1
  have hop : ∀ (j : Fin 6) (Φ : (RadSp P.k P.r z z' π π')), Φ ∈ (ClsE S P z z' π π' X L st l0 D l) → X.op l j Φ ∈ (ClsE S P z z' π π' X L st l0 D l) :=
    fun j Φ hΦ => opClos_op X l _ j Φ hΦ
  have hmk : ∀ i j : Fin 6, mkP (X.op l i) (X.op l j) ∈ Formalism.FourierDecayAlt.P5.HerA.presAlg (ClsE S P z z' π π' X L st l0 D l) := fun i j =>
    (show (∀ Φ ∈ (ClsE S P z z' π π' X L st l0 D l), (mkP (X.op l i) (X.op l j)).1 Φ ∈ (ClsE S P z z' π π' X L st l0 D l)) ∧
        ∀ Φ ∈ (ClsE S P z z' π π' X L st l0 D l), (mkP (X.op l i) (X.op l j)).2.unop Φ ∈ (ClsE S P z z' π π' X L st l0 D l) from
      ⟨fun Φ hΦ => hop i Φ hΦ, fun Φ hΦ => hop j Φ hΦ⟩)
  have hmkneg : ∀ i j : Fin 6, mkP (X.op l i) (-X.op l j) ∈ Formalism.FourierDecayAlt.P5.HerA.presAlg (ClsE S P z z' π π' X L st l0 D l) := fun i j =>
    (show (∀ Φ ∈ (ClsE S P z z' π π' X L st l0 D l), (mkP (X.op l i) (-X.op l j)).1 Φ ∈ (ClsE S P z z' π π' X L st l0 D l)) ∧
        ∀ Φ ∈ (ClsE S P z z' π π' X L st l0 D l), (mkP (X.op l i) (-X.op l j)).2.unop Φ ∈ (ClsE S P z z' π π' X L st l0 D l) from
      ⟨fun Φ hΦ => hop i Φ hΦ, fun Φ hΦ => by
        show (-X.op l j) Φ ∈ (ClsE S P z z' π π' X L st l0 D l)
        rw [LinearMap.neg_apply]
        exact Submodule.neg_mem _ (hop j Φ hΦ)⟩)
  have hp : L.p l ∈ Formalism.FourierDecayAlt.P5.HerA.presAlg (ClsE S P z z' π π' X L st l0 D l) := by rw [hAL.1 l]; exact hmkneg 0 3
  have hc : L.c l ∈ Formalism.FourierDecayAlt.P5.HerA.presAlg (ClsE S P z z' π π' X L st l0 D l) := by rw [hAL.2.2.1 l]; exact hmk 1 4
  have hci : L.ci l ∈ Formalism.FourierDecayAlt.P5.HerA.presAlg (ClsE S P z z' π π' X L st l0 D l) := by rw [hAL.2.2.2.1 l]; exact hmk 2 5
  have hconv : ∀ M : SlopeTestRemainingChoices S (Pr (RadSp P.k P.r z z' π π')),
      M ∈ Formalism.FourierDecayAlt.P5.matSub (Formalism.FourierDecayAlt.P5.HerA.presAlg (ClsE S P z z' π π' X L st l0 D l)).toSubalgebra (Ix S) →
        M ∈ Formalism.FourierDecayAlt.P5.HerA.entSub (Formalism.FourierDecayAlt.P5.HerA.presAlg (ClsE S P z z' π π' X L st l0 D l)) := fun M h => h
  have hins : ∀ (a : S) (M : M2 (Pr (RadSp P.k P.r z z' π π'))), (∀ i j, M i j ∈ Formalism.FourierDecayAlt.P5.HerA.presAlg (ClsE S P z z' π π' X L st l0 D l)) →
      ins a (lift0 M : M2 (SlopeTestRemainingChoices S (Pr (RadSp P.k P.r z z' π π')))) ∈
        Formalism.FourierDecayAlt.P5.matSub (Formalism.FourierDecayAlt.P5.HerA.presAlg (ClsE S P z z' π π' X L st l0 D l)).toSubalgebra (Ix S) := by
    intro a M hM
    apply Formalism.FourierDecayAlt.P5.ins_mem
    have h : ∀ (i j : Fin 2) (p q : Ix S), ((lift0 M : M2 (SlopeTestRemainingChoices S (Pr (RadSp P.k P.r z z' π π')))) i j) p q ∈
        (Formalism.FourierDecayAlt.P5.HerA.presAlg (ClsE S P z z' π π' X L st l0 D l)).toSubalgebra := by
      intro i j p q
      simp only [lift0, Matrix.map_apply, io, Matrix.scalar_apply, Matrix.diagonal_apply]
      split_ifs
      · exact hM i j
      · exact Subalgebra.zero_mem _
    exact h
  refine ⟨fun le b => ?_, fun le b => ?_, fun a i j b => ?_⟩
  · refine act_mem_of_entSub _ _ (hconv _ (hins le.intersection_update_fsHerm_neg_one _ ?_)) u hu b
    intro i j
    split_ifs
    · exact Formalism.FourierDecayAlt.P5.Ts_mem (T := (Formalism.FourierDecayAlt.P5.HerA.presAlg (ClsE S P z z' π π' X L st l0 D l)).toSubalgebra) (site L l) le.pt
        hp hc hci i j
    · exact star_mem
        (Formalism.FourierDecayAlt.P5.Ts_mem (T := (Formalism.FourierDecayAlt.P5.HerA.presAlg (ClsE S P z z' π π' X L st l0 D l)).toSubalgebra) (site L l) le.pt
          hp hc hci i j)
  · refine act_mem_of_entSub _ _ (hconv _ (hins le.intersection_update_fsHerm_neg_one _ ?_)) u hu b
    intro i j
    split_ifs
    · exact Formalism.FourierDecayAlt.P5.HerA.matrix_two_entries_mem (zero_mem _) (neg_mem (star_mem hci)) (star_mem hc)
        (add_mem (algebraMap_mem _ _) (star_mem hp)) i j
    · exact Formalism.FourierDecayAlt.P5.HerA.matrix_two_entries_mem (zero_mem _) (neg_mem hci) hc
        (add_mem (algebraMap_mem _ _) hp) i j
  · exact act_mem_of_entSub _ _
      (hconv _ (Formalism.FourierDecayAlt.P5.eU_mem (C := (Formalism.FourierDecayAlt.P5.HerA.presAlg (ClsE S P z z' π π' X L st l0 D l)).toSubalgebra) a i j)) u hu b

end Formalism.FourierDecayAlt.P.CutSE
