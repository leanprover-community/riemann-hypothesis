module

public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Separation.Connected
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open GlobalTheory.SplitWeil

theorem UpperTheory.ConvolutionTheory.Loc.sbInv :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G], ∀ φ ∈ SB G, ∀ K : Subgroup G, IsOpen (K : Set G) → IsCompact (K : Set G) → TotallyDisconnectedSpace G →
      ∃ U : Subgroup G, IsOpen (U : Set G) ∧ U ≤ K ∧ ∀ u ∈ U, ∀ g, φ (u * g) = φ g ∧ φ (g * u) = φ g := by
  intro G _ _ _ φ hφ K hKo hKc hG
  obtain ⟨hl, hc⟩ := hφ
  have key : ∀ ψ : G × G → G, Continuous ψ → (∀ g, ψ (1, g) = g) → ∀ᶠ u in nhds (1 : G), ∀ g ∈ tsupport φ, φ (ψ (u, g)) = φ g := by
    intro ψ hψ h1
    apply IsCompact.eventually_forall_of_forall_eventually hc
    intro g _
    have a := (hl.comp_continuous hψ).eventually_eq (1, g)
    have b := (hl.comp_continuous continuous_snd).eventually_eq ((1 : G), g)
    filter_upwards [a, b] with z ha hb
    simp only [Function.comp, h1] at ha hb
    rw [ha, hb]
  have a := key (fun p => p.1 * p.2) (by fun_prop) (by simp)
  have b := key (fun p => p.2 * p.1) (by fun_prop) (by simp)
  obtain ⟨W, hW, hWo, hW1⟩ := mem_nhds_iff.1 (a.and b)
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hKc
  obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one (G := K) (U := Subtype.val ⁻¹' W) (hWo.preimage continuous_subtype_val) hW1
  have hU : ∀ u ∈ N.toSubgroup.map K.subtype, u ∈ W := by
    rintro _ ⟨x, hx, rfl⟩
    exact hN hx
  refine ⟨N.toSubgroup.map K.subtype, ?_, Subgroup.map_subtype_le _, fun u hu g => ⟨?_, ?_⟩⟩
  · exact hKo.isOpenMap_subtype_val _ N.isOpen
  · by_cases h : g ∈ tsupport φ
    · exact (hW (hU u hu)).1 g h
    · by_cases h' : u * g ∈ tsupport φ
      · have := (hW (hU _ (inv_mem hu))).1 _ h'
        simpa using this.symm
      · rw [image_eq_zero_of_notMem_tsupport h, image_eq_zero_of_notMem_tsupport h']
  · by_cases h : g ∈ tsupport φ
    · exact (hW (hU u hu)).2 g h
    · by_cases h' : g * u ∈ tsupport φ
      · have := (hW (hU _ (inv_mem hu))).2 _ h'
        simpa using this.symm
      · rw [image_eq_zero_of_notMem_tsupport h, image_eq_zero_of_notMem_tsupport h']
