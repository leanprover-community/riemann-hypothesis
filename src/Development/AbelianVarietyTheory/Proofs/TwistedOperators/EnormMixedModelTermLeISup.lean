module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DerAlong
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MixedTerm

theorem enorm_term_le_iSup : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ (G : WO V W → ℂ) (y : Matrix (Fin W.rank) (Fin r) D.host.E), ‖term ψ V V' W C C' B μ 𝓨 G y‖ₑ ≤ ⨆ w, ‖G w‖ₑ := by
  intro D V V' W r C C' B ψ hψ μ 𝓨 hμ G y
  have hψ1 : ∀ x, ‖(ψ x : ℂ)‖ₑ = 1 := fun x => by
    rw [← ofReal_norm_eq_enorm, hψ.1.2.1 x, ENNReal.ofReal_one]
  calc ‖term ψ V V' W C C' B μ 𝓨 G y‖ₑ
      ≤ ∫⁻ z in 𝓨, ‖heisO ψ V W (isoPart V W C' (Matrix.map y (incA D))) G
          (isoPart V W C z + midPart V V' W B 0)‖ₑ ∂μ := enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ _ in 𝓨, (⨆ w, ‖G w‖ₑ) ∂μ := by
        refine lintegral_mono fun z => ?_
        simp only [heisO, enorm_mul, hψ1, one_mul]
        exact le_iSup (fun w => ‖G w‖ₑ) _
    _ = ⨆ w, ‖G w‖ₑ := by rw [setLIntegral_const, hμ.2.2, mul_one]

end GlobalTheory.MixedTerm
