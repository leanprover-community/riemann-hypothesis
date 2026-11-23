module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.AlgCechSt
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenSESStep
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenTwistGenerated
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

namespace GroundTheory.Heights₂.Heights.Kleiman

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

namespace KHCechDDeg

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, Fintype (ι k)]
  [∀ k, LinearOrder (ι k)]

theorem cellRes_mem_locPart {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M]
    [IsScalarTower S (MRingOver S ι) M] {𝓜 : (K → ℤ) → Submodule S M} {c : K → ℤ}
    {J I : ∀ k, Finset (ι k)} (h : KH.cellMon S J ≤ KH.cellMon S I) {x : LocalizedModule (KH.cellMon S J) M}
    (hx : x ∈ KH.locPart ι 𝓜 (KH.cellMon S J) c) :
    KH.cellRes S M J I x ∈ KH.locPart ι 𝓜 (KH.cellMon S I) c := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, t, a, ht, hm, rfl⟩ := hx
    rw [GroundTheory.Heights₂.Heights.HilbertSamuel.GenTwistGenerated.cellRes_mk h]
    exact GroundTheory.Heights₂.Heights.HilbertSamuel.GenSESStep.mk_mem_locPart m ⟨t.1, h t.2⟩ a ht hm
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul s x _ hx => rw [LinearMap.map_smul_of_tower]; exact Submodule.smul_mem _ s hx

theorem face_subset {K : Type} [DecidableEq K] {ι : K → Type} [∀ k, DecidableEq (ι k)]
    (I : ∀ k, Finset (ι k)) (k : K) (i : ι k) (l : K) :
    Function.update I k ((I k).erase i) l ⊆ I l := by
  by_cases hl : l = k
  · subst hl
    rw [Function.update_self]
    exact Finset.erase_subset _ _
  · rw [Function.update_of_ne hl]

end KHCechDDeg

theorem KHCechDDeg.full : KH.CechDDegStatement := by
  classical
  intro S _ K _ _ ι _ _ M _ _ _ _ 𝓜 c n φ hφ
  refine Submodule.mem_pi.mpr fun I _ => ?_
  simp only [KH.cechD, LinearMap.pi_apply, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun k _ => Submodule.sum_mem _ fun i _ => ?_
  split_ifs with hI
  · change KH.faceSign I.1 k i • KH.cellRes S M _ I.1 (φ ⟨_, hI⟩) ∈ _
    refine zsmul_mem (KHCechDDeg.cellRes_mem_locPart ?_ (Submodule.mem_pi.mp hφ _ (Set.mem_univ _))) _
    exact GroundTheory.Heights₂.Heights.HilbertSamuel.GenTwistGenerated.cellMon_mono
      (KHCechDDeg.face_subset I.1 k i)
  · rw [LinearMap.zero_apply]
    exact zero_mem _

end GroundTheory.Heights₂.Heights.Kleiman
