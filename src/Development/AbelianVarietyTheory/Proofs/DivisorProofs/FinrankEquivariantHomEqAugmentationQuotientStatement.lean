module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QActMSubAlgebraMap
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankEquivariantHomEqAugmentationQuotient
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.InfUniv
import Development.AbelianVarietyTheory.Definitions.Divisors.KottwitzDimSignatureOneOne

@[expose] public section

open Module GlobalTheory.HTRho GlobalTheory.UPel.Sm GlobalTheory.UPel.Sm.Model

theorem _root_.GlobalTheory.T.finrank_equivariantHom_eq_augmentation_quotient : ∀ {k O C Idx H : Type*} [Field k] [AddCommGroup H] [Module k H] [Ring O] [CommRing C] [Algebra C O] (σ : O →+* Module.End k H) (G : Submodule k H) (hG : ∀ a, ∀ x ∈ G, σ a x ∈ G) (χ : Idx → C →+* k), (jSub σ χ ⊤ ≤ G → jSub (qAct σ G hG) χ ⊤ = ⊥) ∧ ∀ i, finrank k ((H ⧸ G) ⧸ mSub (qAct σ G hG) (χ i) ⊤) = finrank k (H ⧸ (G ⊔ mSub σ (χ i) ⊤)) := by
  first | exact @GlobalTheory.HTRho.quotFacts | exact GlobalTheory.HTRho.quotFacts | (intros; apply GlobalTheory.HTRho.quotFacts <;> assumption)
