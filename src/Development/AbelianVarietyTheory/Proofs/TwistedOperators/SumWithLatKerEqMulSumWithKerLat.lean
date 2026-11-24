module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsGlOfEquiv
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum

@[expose] public section

open MeasureTheory ValuativeRel Matrix IsLocalRing GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LatPair
open scoped Pointwise

namespace GlobalTheory.LatPair

theorem card_withLat_eq_card_withKer {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : Type} (L : Submodule (↥𝒪[k]) (n → k))
    [Submodule.IsFullLattice k L] : (withLat L).card = (withKer L).card := by
  classical
  obtain ⟨q⟩ : Nonempty (Unif k) := inferInstance
  have e : Red L ≃ₗ[𝓀[k]] Module.Dual 𝓀[k] (Red L) := (Module.Free.chooseBasis 𝓀[k] (Red L)).toDualEquiv
  have e' : {x : Red L // x ≠ 0} ≃ {f : Module.Dual 𝓀[k] (Red L) // f ≠ 0} :=
    e.toEquiv.subtypeEquiv (fun x => by simp)
  refine Finset.card_eq_of_equiv ?_
  exact (Equiv.subtypeEquivRight (fun P => mem_withLat)).trans
    ((latEquiv L).symm.trans (e'.symm.trans ((kerEquiv L q).trans
      (Equiv.subtypeEquivRight (fun P => mem_withKer.symm)))))

end GlobalTheory.LatPair
