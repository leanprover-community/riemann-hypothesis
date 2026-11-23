module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.JordanExists
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.SplitAtOf
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsIsomLocFOfVdZero
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsSqAbsNormOfInert
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.IsHermSemilocalLocRing
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.IsUnimodularAtIffVd
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.VdEqZeroOfNotLe
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.ExistsNearOfSmul
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.JordanSpanHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.MemSpanSSelf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.RebasingHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.UniformizerValuationHolds
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G3

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA

theorem jordanIsom_of (hE : ExactVec) (hR : Rebase) (hL : LocSpan) (hU : UnifVal)
    (hJ : JordSpan) : Formalism.L2.SG.Pf.Cnt.JordanIsom := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hd L L' hLl hLl' 𝔭 h𝔭 b a b' a' hb hb' hv
  obtain ⟨P, hP, rfl⟩ := exists_maximal_over hK hF h𝔭
  obtain ⟨π, hπ, hval⟩ := hU K F hK hF P hP
  have hda := LocF.aniso_of_totPosDef hd
  obtain ⟨-, hbL, hbo, hbn, hba⟩ := hb
  obtain ⟨-, hbL', hbo', hbn', hba'⟩ := hb'
  have span_of_jordan (c : Fin (finrank K (⊤ : Submodule K V)) → V)
      (d : Fin (finrank K (⊤ : Submodule K V)) → 𝓞 F)
      (ho : ∀ i j, i ≠ j → h (c i) (c j) = 0)
      (hn : ∀ i, h (c i) (c i) = algebraMap F K ((d i : 𝓞 F) : F))
      (hd : ∀ i, d i ≠ 0) : Submodule.span K (Set.range c) = ⊤ := by
    have hi : LinearIndependent K c := LinearMap.linearIndependent_of_isOrthoᵢ ho (fun i => by
      rw [hn i]
      apply (map_ne_zero (algebraMap F K)).2
      intro hz
      apply hd i
      exact FaithfulSMul.algebraMap_injective (𝓞 F) F (by simpa using hz))
    apply hi.span_eq_top_of_card_eq_finrank'
    simp
  have hsp := span_of_jordan b a hbo hbn hba
  have hsp' := span_of_jordan b' a' hbo' hbn' hba'
  have hS := isHermSemilocal_locRing hK hP
  obtain ⟨g, hg, -, hgm⟩ := core_of_split hs hda
    (splitAt_of (hE K F V hK hF h hs hd P hP π hπ) (hR K V (locRing P) π h hS hπ hs hda))
    _ (Fin _) le_rfl b b' (fun i => vF _ (a i)) 1 hbo hbo'
    (fun i => by rw [hbn i]; exact hval _ (hba i))
    (fun i => by rw [hbn' i, hv i]; exact hval _ (hba' i)) (one_mem _)
    (fun v => by
      rw [hsp, hsp']
      exact ⟨fun _ => Submodule.mem_top, fun _ => Submodule.mem_top⟩)
  refine ⟨g, hg, gmap_eq_of_iff fun v => ?_⟩
  rw [← hbL, ← hbL', locF_eq_loc hK hF hP, locF_eq_loc hK hF hP, hL K F V hK hF P hP,
    hL K F V hK hF P hP]
  exact hgm v

end Formalism.L2.SG.Pf.G3

namespace Formalism.L2.SG.Pf.Cnt

theorem jordan_isometry_holds : JordanIsom :=
  Formalism.L2.SG.Pf.G3.jordanIsom_of Formalism.L2.SG.Pf.TemperedBoundGL3.exact_vector_holds Formalism.L2.SG.Pf.TemperedBoundGL3.rebasing_holds
    Formalism.L2.SG.Pf.G3.local_span_holds Formalism.L2.SG.Pf.TemperedBoundGL3.uniformizer_valuation_holds Formalism.L2.SG.Pf.G3.jordan_span_holds

end Formalism.L2.SG.Pf.Cnt
