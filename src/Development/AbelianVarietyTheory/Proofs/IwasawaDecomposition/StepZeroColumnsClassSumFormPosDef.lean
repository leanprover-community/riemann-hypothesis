module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSStageUnconditional
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassSumPosHerm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InnerProductPositiveDefinite
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SameForm

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Df
attribute [local instance] GlobalTheory.Mem.Col2.starE

namespace GlobalTheory.Mem.Df



theorem cols_ipV_herm {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (u : B.Word) (c : ((I.cols l).mem u).C.cls 0)
    (f g : ((I.cols l).mem u).C.Y 0 → ℂ) :
    ((I.cols l).fm u).ipV 0 c f g = starRingEnd ℂ (((I.cols l).fm u).ipV 0 c g f) :=
  ClassSumPos.ipVal_herm _ _ _ f g

theorem cols_ipC_herm {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (u : B.Word)
    (φ ψ : ((I.cols l).mem u).C.cls 0 → ((I.cols l).mem u).C.Y 0 → ℂ) :
    starRingEnd ℂ (((I.cols l).fm u).ipC 0 ψ φ) = ((I.cols l).fm u).ipC 0 φ ψ := by
  unfold MemberForms.ipC

  rw [map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_mul, cols_ipV_herm I l u c (φ c) (ψ c)]
  congr 1
  simp [ColumnChain.wt]

theorem cols_pos : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (hX : B.fields.Ok),
    SpectralModel.ColsPos (I.cols l) := by
  intro B X I _ _ l _ u
  refine ⟨fun x _ y _ => cols_ipC_herm I l u x y, fun x hx h0 => ?_⟩
  exact ipC_zero_re_pos B (I.cols l) u (fun φ ψ => (cols_ipC_herm I l u ψ.1 φ.1).symm) ⟨x, hx⟩
    (fun h => h0 (congrArg Subtype.val h))

end GlobalTheory.Mem.Df
