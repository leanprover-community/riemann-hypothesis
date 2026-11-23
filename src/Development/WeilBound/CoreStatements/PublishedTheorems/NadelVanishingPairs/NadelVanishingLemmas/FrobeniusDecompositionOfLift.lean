module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLifted
public import Development.AbelianVarietyTheory.Definitions.Divisors.CechFam
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RoundedTwistLocalEquationChartStatement
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CartierOperatorLogSectionsStatement
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CechLogFormsFrobeniusLiftStatement
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.LogSectionsDifferentialClosedStatement
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
import Mathlib.Tactic.Basify
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

open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.Cartier

set_option autoImplicit false

namespace GlobalTheory.LogDR

theorem mem_inter_iff {X : Scheme.{0}} [IsIntegral X] {ι : Type} (U : ι → X.Opens) (s : Finset ι) (y : X) :
    y ∈ inter U s ↔ ∀ i ∈ s, y ∈ U i := by
  classical
  unfold inter
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.inf_insert]
    simp only [Finset.mem_insert, forall_eq_or_imp]
    rw [← ih]
    exact Iff.rfl

theorem decomp_of_isLifted (p : ℕ) [Fact p.Prime] {X : Scheme.{0}} [IsIntegral X] [CharP X.functionField p]
    {C : Type} [Fintype C] {E : C → CartierDiv X} {n : ℕ} {ι : Type} [LinearOrder ι] (𝒜 : SncAtlas E n ι)
    (hn : n < p) (hL : IsLifted p (suppAll E) 𝒜.U 𝒜.x) : Decomp p 𝒜 := by
  intro G r hr a b hH
  exact GlobalTheory.T.cech_log_forms_frobenius_lift p (suppAll E) 𝒜.U 𝒜.x (inter 𝒜.U) G (p • G + ∑ c, r c • E c) hn 𝒜.gen
    (fun i => ((𝒜.chart i).chart _ (𝒜.gen i)).coord)
    (fun s _ y => mem_inter_iff 𝒜.U s y) hL
    (GlobalTheory.T.roundedTwist_localEquation_chart p 𝒜 G r hr).1
    (fun q s η hη => GlobalTheory.T.log_sections_differential_closed p 𝒜 G r hr q (inter 𝒜.U s) η hη)
    (fun s j hj γ hγ => GlobalTheory.T.cartier_operator_log_sections p 𝒜 G r hr s j hj γ hγ)
    a b hH

end GlobalTheory.LogDR
