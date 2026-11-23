module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.BcStmt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published

theorem UpperTheory.V.Br.selfIso :
    UpperTheory.V.Br.SelfIso := by
  intro H F _ _ _ a ha π η h2 h
  have hd : ∀ z, TR.dchi η z = 0 := fun z => by
    have e := TR.dchi_mul η η z
    rw [← pow_two, h2, TR.dchi_one] at e
    linear_combination (-1 / 2 : ℂ) * e
  obtain ⟨S, hS⟩ : π.Iso (π.twist η) := H F a ha _ _ (by
    filter_upwards [h] with w ⟨hu, B, hB, hE⟩
    exact ⟨B, hB, hE ▸ hB.twist hu⟩)
  have key : ∀ o φ, (S.trans (π.toTwist η).symm) (π.op o φ) =
      ((TR.opMul η o : ℂˣ) : ℂ) • π.op o ((S.trans (π.toTwist η).symm) φ) +
        TR.opAdd η o • (S.trans (π.toTwist η).symm) φ := fun o φ => by
    apply (π.toTwist η).injective
    rw [← TR.CuspSub.op_toTwist]
    simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, hS]
  refine ⟨S.trans (π.toTwist η).symm, fun k φ => ?_, fun k φ => ?_, fun X φ => ?_⟩
  all_goals rw [key]; simp [TR.opMul, TR.opAdd, hd]
