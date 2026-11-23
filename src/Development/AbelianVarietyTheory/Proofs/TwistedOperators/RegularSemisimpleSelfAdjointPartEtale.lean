module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct

namespace GlobalTheory.RegSS

theorem plusEtale : PlusEtale := by
  intro F E _ _ _ _ n _ _ σ J γ hreg hA hbij
  have : Nontrivial E := quad_nontrivial hreg.quad
  have : Module.Finite F E := quad_finite hreg.quad
  obtain ⟨b⟩ := hA.2.2.1
  have : Module.Free E (genAlg (γ : Matrix n n E)) := Module.Free.of_basis b
  have : Module.Finite E (genAlg (γ : Matrix n n E)) := Module.Finite.of_basis b
  have : Module.Finite F (genAlg (γ : Matrix n n E)) := Module.Finite.trans E _
  have : Module.Finite F (plusAlg σ J (γ : Matrix n n E)) :=
    Module.Finite.of_injective (plusAlg σ J (γ : Matrix n n E)).val.toLinearMap
      Subtype.val_injective
  have : IsReduced (genAlg (γ : Matrix n n E)) := genAlg_isReduced hreg hA
  have : IsReduced (plusAlg σ J (γ : Matrix n n E)) :=
    isReduced_of_injective (plusAlg σ J (γ : Matrix n n E)).val Subtype.val_injective
  refine ⟨etale_of_isReduced _, ?_, hbij⟩
  have hdim := (AlgEquiv.ofBijective _ hbij).toLinearEquiv.finrank_eq
  rw [Module.finrank_tensorProduct, hreg.quad.finrank_eq,
    ← Module.finrank_mul_finrank F E (genAlg (γ : Matrix n n E)), hreg.quad.finrank_eq, Module.finrank_eq_card_basis b] at hdim
  have hr : Module.finrank F (plusAlg σ J (γ : Matrix n n E)) = Fintype.card n := by omega
  exact ⟨(Module.finBasisOfFinrankEq F _ hr).reindex (Fintype.equivFin n).symm⟩

end GlobalTheory.RegSS
