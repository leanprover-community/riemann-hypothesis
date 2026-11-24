module

public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem phiC_zero_rule {D : D7} (T : CoreJ D) {j : ℕ} {σ : T.Q.c.F →+* ℂ} {W : HSp D} (hV : T.V j σ = W)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) : phiC T hV a (0 : T.R j) = 0 := by
  subst hV
  show T.phiJ j σ a 0 = 0
  unfold CoreJ.phiJ
  rw [map_zero, map_zero, smul_zero]


set_option linter.unusedVariables false in
theorem evaluates_of_unif : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T R κ v₀), R.LUnif → fw.Evaluates := by
  set_option synthInstance.maxHeartbeats 200000 in
    intro D G _ _ Pl0 T0 A T _ R F κ v₀ fw hU i σ hσ hV f
    by_cases hj : ∃ j' : (Fin (R.nW i) → D.what₂.LL) →ₛₗ[σ] (R.HW i σ).H,
        ∀ f : T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n,
          ((R.HW i σ).e (j' ((fw.e i f : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL))) (v₀ i σ) =
            hV ▸ T.phiJ ((i : ℕ) + 1) (σ.comp (algebraMap T.Q.c.F D.what₂.LL)) (wtA (κ i)) (f : T.R ((i : ℕ) + 1))
    · exact fw.ev i σ hσ hV hj f
    · exfalso
      have hz : (R.FW i).j σ = 0 := fw.ev0 i σ hσ hV hj

      have hx : ∀ x : Fin (R.nW i) → D.what₂.LL, x = 0 := by
        intro x
        by_contra hne
        have hli := (hU i σ).1 1 (fun _ => x) (linearIndependent_unique_iff.mpr hne)
        simp only [hz, LinearMap.zero_apply] at hli
        exact hli.ne_zero 0 rfl

      apply hj
      refine ⟨0, fun f' => ?_⟩
      have hf' : f' = 0 := by
        simpa using hx ((fw.e i f' : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL)
      subst hf'
      simp
      exact (phiC_zero_rule T hV (wtA (κ i))).symm

end GlobalTheory
