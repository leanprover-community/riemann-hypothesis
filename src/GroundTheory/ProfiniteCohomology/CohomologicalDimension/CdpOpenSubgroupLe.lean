module

public import GroundTheory.ProfiniteCohomology.CohomologicalDimension.PrimaryComponentCohomologyEqBotOfScdpLt
public import Mathlib.Topology.Algebra.OpenSubgroup
public import GroundTheory.ProfiniteCohomology.CohomologicalDimension.SubsingletonCohomologyOfPrimaryOfFinite
public import GroundTheory.ProfiniteCohomology.Shapiro
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
import Mathlib.Tactic.Linter.Style
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

namespace GroundTheory.ProfCoh

open CategoryTheory

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]

theorem isAddTorsion_coind (U : OpenSubgroup G) (B : Rep.{u} (ULift.{u} ℤ) (U : Subgroup G))
    [IsDiscreteRep B] (hB : IsAddTorsion B) :
    IsAddTorsion (Rep.coind (U : Subgroup G).subtype B) := by
  classical
  intro f
  have hfin : (Set.range (f.1 : G → B)).Finite := (isLocallyConstant_coind U B f).range_finite
  let N := ∏ v ∈ hfin.toFinset, addOrderOf v
  have hN : 0 < N := Finset.prod_pos fun v _ => (hB v).addOrderOf_pos
  refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨N, hN, Subtype.ext (funext fun x => ?_)⟩
  show N • f.1 x = 0
  have hv : f.1 x ∈ hfin.toFinset := by simp
  exact addOrderOf_dvd_iff_nsmul_eq_zero.1 (Finset.dvd_prod_of_mem _ hv)

theorem cdp_openSubgroup_le (p : ℕ) (U : OpenSubgroup G) : cdp p (U : Subgroup G) ≤ cdp p G := by
  rw [cdp_le_iff]
  intro B _ hB q hq
  have h0 := primaryComponent_cohomology_eq_bot_of_cdp_lt (Rep.coind (U : Subgroup G).subtype B)
    (isAddTorsion_coind U B hB) hq
  rw [primaryComponent_eq_bot_iff] at h0 ⊢
  rintro x ⟨k, hk⟩
  have hy : (shapiroIso U B q).inv.hom x = 0 := h0 _ ⟨k, by rw [← map_nsmul, hk, map_zero]⟩
  rw [← Iso.inv_hom_id_apply (shapiroIso U B q) x, hy, map_zero]

end GroundTheory.ProfCoh
