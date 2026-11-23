module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SubOfNonNil
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2

namespace GlobalTheory.CompanionTheory.HeckeSub

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {ι : Type} [Fintype ι] [DecidableEq ι]

theorem finite_cosets {K : Subgroup (GL ι F)} {e : GL ι F → ℂ} (hE : IsHk K e) :
    {q : GL ι F ⧸ K | e q.out ≠ 0}.Finite := by
  have hc : IsCompact (tsupport e) := hE.2.2.1
  obtain ⟨t, ht⟩ := hc.elim_finite_subcover (fun g : GL ι F => (fun x => g⁻¹ * x) ⁻¹' (K : Set (GL ι F)))
    (fun g => hE.1.preimage (continuous_const.mul continuous_id))
    (fun g _ => Set.mem_iUnion.2 ⟨g, by simp [K.one_mem]⟩)
  refine (t.finite_toSet.image (fun g => (QuotientGroup.mk g : GL ι F ⧸ K))).subset fun q hq => ?_
  have hq' : q.out ∈ tsupport e := subset_tsupport _ hq
  obtain ⟨g, hg, hgq⟩ := Set.mem_iUnion₂.1 (ht hq')
  exact ⟨g, hg, (QuotientGroup.eq.2 hgq).trans (QuotientGroup.out_eq' q)⟩

theorem hk_map {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (GL ι F) V) (σ : Representation ℂ (GL ι F) W) (f : V →ₗ[ℂ] W)
    (hf : ∀ g v, f (ρ g v) = σ g (f v)) {K : Subgroup (GL ι F)} {e : GL ι F → ℂ} (hE : IsHk K e) (v : V) :
    f (hk ρ K e v) = hk σ K e (f v) := by
  unfold hk
  have hfin : (Function.support fun q : GL ι F ⧸ K => e q.out • ρ q.out v).Finite :=
    (finite_cosets hE).subset fun q hq h0 => hq (by simp [show e q.out = 0 from h0])
  rw [map_finsum f hfin]
  simp only [map_smul, hf]

end GlobalTheory.CompanionTheory.HeckeSub
