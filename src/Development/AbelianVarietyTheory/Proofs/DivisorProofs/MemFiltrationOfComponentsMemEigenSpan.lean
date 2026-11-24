module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuotientEigenDifference
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SingleMemOfMem
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
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
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.MultiplicationKernelIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemAddValuationIntegerRingNormalizedIff

@[expose] public section

open scoped NNReal
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HerbrandBridge

namespace GlobalTheory.Div.KerFil
open GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference

theorem mem_of_components : ∀ (C : Type) [Field C] (w : Valuation C ℝ≥0) (S : Type) [Fintype S]
    [DecidableEq S] (a : S → w.valuationSubring) (N : ℕ)
    (F : Submodule w.valuationSubring (S → Fin N → C)), Function.Injective a →
    GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.IsFiltration a F → ∀ x ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a N,
    (∀ s, x s ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace F s) → x ∈ F := by
  intro C _ w S _ _ a N F ha hF x hx hc
  have hle : ∀ s, filSpace F s ≤ clearDen F s := fun s => by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨diffGen a s, diffGen_ne_zero a ha s, single_mem_of_mem a F hF.stable s y hy⟩
  choose b hb hbx using fun s => hle s (hc s)
  have hB : (∏ s, b s) ≠ 0 := Finset.prod_ne_zero_iff.2 fun s _ => hb s
  refine hF.saturated x hx (∏ s, b s) hB ?_
  have key : (∏ s, b s) • x = ∑ s, (∏ t ∈ Finset.univ.erase s, b t) •
      (Pi.single s (b s • x s) : S → Fin N → C) := by
    funext s' i
    rw [Finset.sum_apply, Finset.sum_apply, Finset.sum_eq_single s']
    · simp only [smul_pi_apply, Pi.single_eq_same, smul_vec_apply]
      rw [← mul_assoc, ← Subring.coe_mul, Finset.prod_erase_mul _ _ (Finset.mem_univ s')]
    · intro s _ e
      simp [smul_pi_apply, Pi.single_apply, Ne.symm e]
    · simp
  rw [key]
  exact sum_mem fun s _ => F.smul_mem _ (hbx s)

end GlobalTheory.Div.KerFil
