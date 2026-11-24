module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.StandardOrderExtendedBasisApplyLowBlock
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RootExchangeRowUnipotentLatticeFrameConjApply
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

theorem _root_.GlobalTheory.T.rootExchangeRowUnipotent_latticeFrame_conj_apply : ∀ (k : Type) [Field k] (κ t : Type) [Fintype κ] [DecidableEq κ] [Fintype t] [DecidableEq t] (ϖ : kˣ) (j c l : ℕ) (h : j + c = l) (p : ℕ) (hp : p < c) (u : XIx κ t j → k) (a b : Ix (κ ⊕ Fin l) t j), ((typeFrame ϖ (stdOrd κ t j c h)).conj.symm (rowE c (p + 1) u)).val a b = (1 : Matrix (Ix (κ ⊕ Fin l) t j) (Ix (κ ⊕ Fin l) t j) k) a b + if a = Sum.inl (Sum.inr ⟨p, by omega⟩) then Sum.elim (fun y => ((ϖ : k) ^ (p + 1))⁻¹ * u y) (fun _ => 0) (stdOrd κ t j c h b) else 0 := by
  first | exact @GlobalTheory.typeFrame_conj_symm_rowE_apply | exact GlobalTheory.typeFrame_conj_symm_rowE_apply | (intros; apply GlobalTheory.typeFrame_conj_symm_rowE_apply <;> assumption)
