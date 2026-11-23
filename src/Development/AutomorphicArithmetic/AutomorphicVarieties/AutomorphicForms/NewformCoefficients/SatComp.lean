module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.CuspCritAlt
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
import Mathlib.Tactic.NormNum.Prime
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall

@[expose] public section

open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.CuspRep in
theorem UpperTheory.V.Af.Nf.satComp :
    UpperTheory.V.Af.Nf.SatComp := by
  intro F _ _ _ φ π ψ W h0 hW hd hφ w B h
  have hle : ∀ g, W ≤ W.comap (locSm F w g) := fun g x hx => hW (.fin (locGL F 2 w g)) x hx
  have hi : Function.Injective (W.mkQ ∘ₗ π.V.subtype) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_comp, Submodule.ker_mkQ]
    exact Submodule.disjoint_iff_comap_eq_bot.1 hd
  have he : W.mkQ φ = (W.mkQ ∘ₗ π.V.subtype) ψ := (Submodule.Quotient.eq W).2 hφ
  have h1 := h.map (ρ' := (locSm F w).quotient W hle) W.mkQ (fun _ _ => rfl)
    (by rw [he]; exact fun e => h0 (hi (e.trans (map_zero _).symm)))
  rw [he] at h1
  exact GlobalTheory.LFun.IsSatVecGL.of_map _ (fun _ _ => rfl) hi h1
