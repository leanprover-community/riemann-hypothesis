module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StandardModuleProperties
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

theorem _root_.GlobalTheory.T.standard_module_properties : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k], GlobalTheory.Published.LanglandsMultisegments →
    ∀ (P : Segment k → Prop), (∀ 𝔫 : Multiset (Segment k), (∀ Δ ∈ 𝔫, P Δ) → ∃ y : IrrGL (k := k), IsL 𝔫 y.rep) →
    ∀ (h N : ℕ) (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N) (𝔪 : Fin h → Multiset (Segment k)),
      (∀ j, IsL (𝔪 j) (x j).rep) → (∀ j, ∀ Δ ∈ 𝔪 j, P Δ) →
      ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), π.IsIrreducible →
        Nonempty (π.Equiv (prodIrr x hd)) → IsL (∑ j, 𝔪 j) π := by
  first | exact @GlobalTheory.LocGL.IrrProdL.isL_sum_of_isIrreducible | exact GlobalTheory.LocGL.IrrProdL.isL_sum_of_isIrreducible | (intros; apply GlobalTheory.LocGL.IrrProdL.isL_sum_of_isIrreducible <;> assumption)
