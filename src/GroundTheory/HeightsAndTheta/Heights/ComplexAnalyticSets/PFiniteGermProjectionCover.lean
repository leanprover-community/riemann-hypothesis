module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFiniteGermProjectionCover
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StIrreducibleGermProjectionOpenNear
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StProperOpenProjectionCover
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

theorem FiniteGermProjectionCover.proof (hopen : IrreducibleGermProjectionOpenNear.Statement)
    (hcov : ProperOpenProjectionCover.Statement) : FiniteGermProjectionCover.Statement := by
  intro σ _ X w d A hX hirr hiso hinj
  obtain ⟨N₀, hN₀, hop⟩ := hopen σ X w d A hX hirr hiso hinj
  obtain ⟨N, k, f, hNo, hwN, hf, hXN⟩ := hX
  refine ⟨interior N₀ ∩ N, Filter.inter_mem (interior_mem_nhds.2 hN₀) (hNo.mem_nhds hwN), ?_⟩
  intro B D hBo hBN hwB hDo hDc hmaps hprop hisoB
  have hBN' : B ⊆ N := fun x hx => (hBN hx).2

  have hzero : X ∩ B = {z | z ∈ B ∧ ∀ i, f i z = 0} := by
    ext z
    constructor
    · rintro ⟨hzX, hzB⟩
      have h1 : z ∈ X ∩ N := ⟨hzX, hBN' hzB⟩
      rw [hXN] at h1
      exact ⟨hzB, h1.2⟩
    · rintro ⟨hzB, hz⟩
      have h2 : z ∈ {z | z ∈ N ∧ ∀ i, f i z = 0} := ⟨hBN' hzB, hz⟩
      rw [← hXN] at h2
      exact ⟨h2.1, hzB⟩

  have hopB : ∀ x ∈ X ∩ B, ∀ V ∈ 𝓝 x, A '' (X ∩ B ∩ V) ∈ 𝓝 (A x) := by
    intro x hx V hV
    have h1 := hop x ⟨hx.1, interior_subset (hBN hx.2).1⟩ (V ∩ B)
      (Filter.inter_mem hV (hBo.mem_nhds hx.2))
    have h2 : X ∩ (V ∩ B) = X ∩ B ∩ V := by
      ext z
      simp only [Set.mem_inter_iff]
      tauto
    rwa [h2] at h1
  obtain ⟨δ, M, hδ, hδne, hcount, hgraph, hdense⟩ :=
    hcov σ X B k f d A D hBo (fun i => (hf i).mono hBN') hzero hDo hDc ⟨A w, hmaps hwB⟩ hmaps hprop hopB
  exact ⟨δ, M, hBo, hwB, hDo, hDc, hmaps, hprop, hisoB, hδ, hδne, hcount, hgraph, hdense⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
