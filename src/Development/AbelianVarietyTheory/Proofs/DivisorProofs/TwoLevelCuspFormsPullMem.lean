module

public import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.TwoLevelLogarithm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormPullbackIsBoundedSection
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MemCuspFormsOfMultipleRationalIsometryMove
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LactMemDomOfIsom
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIsometryOfSabMap

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn GlobalTheory.CuspEmb

namespace GlobalTheory.CuspEmb

theorem pull_mem_SS : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C]
    (M : TwoLevels E r U C) (la : Wt M.Ψ r) (F : C → Frame M.Ψ r → ℂ) (h : U), F ∈ M.SS la → M.pull h F ∈ M.SS la := by
  intro E _ _ _ r U C _ _ M la F h hF c
  have hm : GlobalTheory.LevelCusp.IsMatch (M.comp c).toData (M.comp (h • c)).toData (M.tr h c) :=
    { psi := (M.comp_Ψ c).trans (M.comp_Ψ (h • c)).symm
      p0 := (M.comp_basePoint c).trans (M.comp_basePoint (h • c)).symm
      xi := (M.comp_ξ0 c).trans (M.comp_ξ0 (h • c)).symm
      iso := fun u v => by
        show herm (M.comp (h • c)).Gm _ _ = herm (M.comp c).Gm u v
        rw [M.comp_Gm, M.comp_Gm]
        exact M.tr_herm h c u v
      lat := fun v => M.tr_Λ h c v }
  exact GlobalTheory.LevelCusp.mem_SS_of_isMatch E r _ _ (M.tr h c) hm (castWt (M.comp_Ψ c) la)
    (castWt (M.comp_Ψ (h • c)) la) (fun τ i => rfl) _ (fun y => F (h • c) (castFrame (M.comp_Ψ (h • c)) y)) 1
    (GlobalTheory.PullBdd.pull_isBddSec E r U C M la F hF h c).1 (hF (h • c)) (fun x _ => by rw [one_mul]; rfl)

end GlobalTheory.CuspEmb

end
