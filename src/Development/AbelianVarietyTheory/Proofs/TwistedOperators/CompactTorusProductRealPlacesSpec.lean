module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ApplyMulTorProd
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryRealPointsStructureRealPlaces
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdSpan.ConjHol

theorem torProd_spec : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (B : C.Bas), C.IsB B → ∀ (s : D.what₂.Tau → Fin T.rank → ℝ), GlobalTheory.AdSpan.ConjHol.torProd C.θ T B s ∈ GinfC T ∧ ∀ ρ, compAt C.θ ρ (Formalism.L2.Theta.mt T (GlobalTheory.AdSpan.ConjHol.torProd C.θ T B s)) = B ρ * diagonal (fun c => cexp ((s ρ c : ℂ) * I)) * (B ρ)⁻¹ := by
  intro D S T C B hB s
  have R : GlobalTheory.SmoothForms.RealPoints C.θ T := (GlobalTheory.SmoothForms.RealPts.realPoints D).2 C.θ C.inf T
  have hu : ∀ ρ, IsAtTau C.θ T ρ (B ρ * diagonal (fun c => cexp ((s ρ c : ℂ) * I)) * (B ρ)⁻¹) (torAt C.θ T B ρ (s ρ)) := by
    intro ρ
    have hS : (diagonal fun c => cexp ((s ρ c : ℂ) * I))ᴴ * sgnM C.X * (diagonal fun c => cexp ((s ρ c : ℂ) * I)) = sgnM C.X := by
      unfold sgnM
      exact GlobalTheory.HolRead.AdExt.diag_unitary _ _
    exact GlobalTheory.HolRead.AdExt.atTau_spec R ρ (GlobalTheory.HolRead.AdExt.conj_mem_unitary (isUnit_det_B C hB ρ) (hB ρ) hS)
  suffices H : ∀ l : List D.what₂.Tau, l.Nodup → (l.map fun ρ => torAt C.θ T B ρ (s ρ)).prod ∈ GinfC T ∧
      ∀ ρ, infMat D.sp.cm.sig T.gram (C.θ ρ) (l.map fun ρ => torAt C.θ T B ρ (s ρ)).prod =
        if ρ ∈ l then B ρ * diagonal (fun c => cexp ((s ρ c : ℂ) * I)) * (B ρ)⁻¹ else 1 by
    obtain ⟨h1, h2⟩ := H (Finset.univ : Finset D.what₂.Tau).toList (Finset.nodup_toList _)
    refine ⟨h1, fun ρ => ?_⟩
    have := h2 ρ
    rw [if_pos (Finset.mem_toList.2 (Finset.mem_univ _))] at this
    exact this
  intro l hl
  induction l with
  | nil =>
    refine ⟨one_mem _, fun ρ => ?_⟩
    simpa using R.2.2.2.2.1 1 (one_mem _) ρ
  | cons τ l ih =>
    rw [List.nodup_cons] at hl
    obtain ⟨i1, i2⟩ := ih hl.2
    rw [List.map_cons, List.prod_cons]
    refine ⟨mul_mem (hu τ).1 i1, fun ρ => ?_⟩
    rw [R.2.2.2.1, i2 ρ]
    by_cases c : ρ = τ
    · subst c
      rw [(hu ρ).2.1, if_neg hl.1, if_pos List.mem_cons_self, Matrix.mul_one]
    · rw [(hu τ).2.2 ρ c, Matrix.one_mul]
      simp only [List.mem_cons, c, false_or]

end GlobalTheory.AdSpan.ConjHol
