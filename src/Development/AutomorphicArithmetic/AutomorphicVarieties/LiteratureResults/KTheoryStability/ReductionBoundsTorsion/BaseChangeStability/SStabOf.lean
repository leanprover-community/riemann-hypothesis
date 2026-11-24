module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.SBridgeAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.BaseChangeStability.BaseChangeBijective
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open CategoryTheory UpperTheory.V.KL
open scoped TensorProduct

namespace PositivityTheory.KB

theorem sStab_of : SChain → SBridge → SStab := by
  intro hC hB R _ _ k n n' h hn
  obtain ⟨θ, hsurj, hker, hnat⟩ := hB k
  have := StabilizationIso.isIso_stab R (k + 1) n (by omega) n' h
  obtain ⟨hinj, hsur⟩ := StabilizationIso.baseChange_bijective (grpHMap (stab R n n' h) (k + 1))
  have hcyc : ∀ z : Chn (GL (Fin n) R) (k + 1), IsCyc z → IsCyc (cmap (stab R n n' h) (k + 1) z) :=
    fun z hz => by
      unfold IsCyc at hz ⊢
      rw [hC.2.1, hz, map_zero]
  refine ⟨fun z hz hb => ?_, fun z' hz' => ?_⟩
  · have e := hnat _ _ (stab R n n' h) ⟨z, LinearMap.mem_ker.2 hz⟩
      ⟨_, LinearMap.mem_ker.2 (hcyc z hz)⟩ rfl
    rw [(hker _ _).2 hb] at e
    refine (hker _ ⟨z, LinearMap.mem_ker.2 hz⟩).1 (hinj ?_)
    rw [← e, map_zero]
  · obtain ⟨y, hy⟩ := hsur (θ _ ⟨z', LinearMap.mem_ker.2 hz'⟩)
    obtain ⟨w, rfl⟩ := hsurj _ y
    refine ⟨w.1, LinearMap.mem_ker.1 w.2, ?_⟩
    have e := hnat _ _ (stab R n n' h) w ⟨_, LinearMap.mem_ker.2 (hcyc w.1 (LinearMap.mem_ker.1 w.2))⟩ rfl
    exact (hker _ (⟨_, LinearMap.mem_ker.2 (hcyc w.1 (LinearMap.mem_ker.1 w.2))⟩ -
      ⟨z', LinearMap.mem_ker.2 hz'⟩)).1 (by rw [map_sub, e, hy, sub_self])

end PositivityTheory.KB

end
