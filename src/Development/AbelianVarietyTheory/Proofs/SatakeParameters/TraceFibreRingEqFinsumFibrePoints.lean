module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TcoMem
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CardAlgHomReducedTraceSum
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FibFiniteAndSep
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
import Mathlib.Tactic.Linter.HaveILetI
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

open GlobalTheory GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PD.FibTrace

theorem trace_quot_eq_finsum_fib : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → IsAlgClosed k → IsReduced ((rB k K x {0}) ⧸ (Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem k K x j⟩ : (rB k K x {0}))))) → ∀ h : (rB k K x {0}), Algebra.trace k ((rB k K x {0}) ⧸ (Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem k K x j⟩ : (rB k K x {0}))))) (Ideal.Quotient.mk _ h) = ∑ᶠ e : fib k K x, e.1 h := by
  intro k _ _ F K _ _ _ _ _ _ d x hc hk hred h
  set J : Ideal (rB k K x {0}) := Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem k K x j⟩ : (rB k K x {0}))) with hJ
  haveI : Module.Finite k (rB k K x {0} ⧸ J) := GlobalTheory.PD.FibFin.finite_quot k K x hc
  haveI : Module.Free k (rB k K x {0} ⧸ J) := Module.Free.of_divisionRing k _
  have hred' : IsReduced (k ⊗[k] (rB k K x {0} ⧸ J)) :=
    isReduced_of_injective (Algebra.TensorProduct.lid k (rB k K x {0} ⧸ J)).toRingHom
      (Algebra.TensorProduct.lid k (rB k K x {0} ⧸ J)).injective
  have key := (GlobalTheory.finite_card_trace_algHom_of_isReduced_baseChange (O := k) (H := rB k K x {0} ⧸ J) (K := k) hred').2.2
    (Ideal.Quotient.mk J h)
  rw [Algebra.algebraMap_self, RingHom.id_apply] at key
  rw [key]
  have hker : ∀ e : fib k K x, ∀ a ∈ J, e.1 a = 0 := fun e a ha => by
    have : J ≤ RingHom.ker e.1 := by
      rw [hJ, Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      exact e.2 j
    exact this ha
  let E : fib k K x ≃ (rB k K x {0} ⧸ J →ₐ[k] k) :=
    { toFun := fun e => Ideal.Quotient.liftₐ J e.1 (hker e)
      invFun := fun φ => ⟨φ.comp (Ideal.Quotient.mkₐ k J), fun j => by
        simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
        have hm : (⟨_, tco_mem k K x j⟩ : rB k K x {0}) ∈ J := by
          rw [hJ]; exact Ideal.subset_span ⟨j, rfl⟩
        rw [Ideal.Quotient.eq_zero_iff_mem.2 hm, map_zero]⟩
      left_inv := fun e => Subtype.ext (AlgHom.ext fun a => rfl)
      right_inv := fun φ => by
        apply Ideal.Quotient.algHom_ext
        rfl }
  rw [← finsum_comp_equiv E]
  rfl

end GlobalTheory.PD.FibTrace
