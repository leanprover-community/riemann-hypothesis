module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.ContinuousTorusCharacter
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open IsLocalRing Matrix UpperTheory.V.Hi

theorem UpperTheory.V.Hi.propCp :
    ∀ (G : Type) [Group G] (I : Iwa G) (A M : Type) [CommRing A] [AddCommGroup M] [Module A M] (π : Representation A G M) (a : G), a ∈ I.P → ∀ v ∈ fixd π I.N, I.uOp π a v - ((I.Nconj a).relIndex I.N : A) • π a v ∈ I.jacKer π := by
  intro G _ I A M _ _ _ π a ha v _
  have hfin : ((I.Nconj a).subgroupOf I.N).FiniteIndex := ⟨I.fin_N a ha⟩
  haveI : Fintype (I.N ⧸ (I.Nconj a).subgroupOf I.N) := Fintype.ofFinite _
  have hc : (I.Nconj a).relIndex I.N = Fintype.card (I.N ⧸ (I.Nconj a).subgroupOf I.N) := by
    rw [← Nat.card_eq_fintype_card]; rfl
  have hs : (((I.Nconj a).relIndex I.N : ℕ) : A) • π a v
      = ∑ _q : I.N ⧸ (I.Nconj a).subgroupOf I.N, π a v := by
    rw [Finset.sum_const, Finset.card_univ, hc, Nat.cast_smul_eq_nsmul]
  rw [hs, Iwa.uOp, finsum_eq_sum_of_fintype, LinearMap.sum_apply, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun q _ => Submodule.subset_span ?_
  refine ⟨(q.out : I.N), I.N_le (q.out).2, π a v, ?_⟩
  rw [map_mul]; rfl
