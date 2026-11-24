module

public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.RecTTransport
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LanglandsClassificationSupercuspidalSupportMulti
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ClBasic
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.Multi
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.HasSupportOfIsSubquotientProdIrr
import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.IrreducibleAdmissibleGL
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands

theorem UpperTheory.Zero.LLC.goodSeg :
    UpperTheory.Zero.LLC.GoodSeg := by
  intro k _ _ _ _ _
  have huniq : ∀ (x : IrrGL (k := k)) (s s' : Multiset (IrrGL (k := k))),
      HasSupport x.rep s → HasSupport x.rep s' → s = s' :=
    fun x s s' hs hs' =>
      GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_unique PositivityTheory.Exh.geometricLemmaGL UpperTheory.Zero.LLC.Pr.bz hs hs'
  have hgood : ∀ (x : IrrGL (k := k)) (s : Multiset (IrrGL (k := k))), HasSupport x.rep s →
      (UpperTheory.Zero.LLC.Good x ↔ ∀ y ∈ s, UpperTheory.Zero.LLC.GoodCusp y) := by
    intro x s hs
    unfold UpperTheory.Zero.LLC.Good
    constructor
    · rintro ⟨t, ht, hy⟩
      rw [huniq x s t hs ht]
      exact hy
    · intro hy
      exact ⟨s, hs, hy⟩
  have htw : ∀ (y : IrrGL (k := k)) (a : ℂ),
      UpperTheory.Zero.LLC.GoodCusp (y.nu a) ↔ UpperTheory.Zero.LLC.GoodCusp y := by
    intro y a
    unfold IrrGL.nu
    exact ((UpperTheory.Zero.LLC.clBasic k y).2.1 _ _).2.2.1
  refine ⟨?_, ?_, huniq⟩
  · intro l x hl
    rw [hgood x _ (hasSupport_msupp_of_isL UpperTheory.Zero.LLC.Pr.zel k _ x hl)]
    unfold msupp
    constructor
    · intro h Δ hΔ
      have hmem : Δ.first.nu ((0 : ℕ) : ℂ) ∈ Δ.ms :=
        Segment.mem_ms.mpr (Segment.mem_carrier.mpr ⟨0, Δ.len_pos, rfl⟩)
      have hc := h _ (Multiset.mem_bind.mpr ⟨Δ, Multiset.mem_coe.mpr hΔ, hmem⟩)
      exact (htw _ _).mp hc
    · intro h y hy
      obtain ⟨Δ, hΔ, hy⟩ := Multiset.mem_bind.mp hy
      obtain ⟨a, _, rfl⟩ := Segment.mem_carrier.mp (Segment.mem_ms.mp hy)
      exact (htw _ _).mpr (h Δ (Multiset.mem_coe.mp hΔ))
  · intro x hx
    rw [hgood x {x} (hasSupport_self hx)]
    simp
