module

public import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsSemilocIntegral
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PCentreOverW
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
public import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

theorem SemilocIntegral.proof (h₁ : ValCentreZ.Statement) (h₂ : CentreOverW.Statement) :
    SemilocIntegral.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' n s α W hv hP' hP hs hsP hW
  have := hP'.2.1.1
  letI := (locToSemiloc hv P' W).toAlgebra
  let f : locRing (imageZ v P') W →+* FractionRing (MRing ι' ⧸ P') :=
    (semiLocRing P' (fibreOver v P' W)).subtype.comp (locToSemiloc hv P' W)
  refine ⟨fun b => ?_⟩
  refine RingHom.IsIntegralElem.of_map (g := (semiLocRing P' (fibreOver v P' W)).subtype)
    Subtype.val_injective ?_
  have hmem : (b : FractionRing (MRing ι' ⧸ P')) ∈ ⨅ V : {V : ValuationSubring
      (FractionRing (MRing ι' ⧸ P')) // Set.range f ⊆ V.toSubring}, V.1.toSubring := by
    rw [Subring.mem_iInf]
    rintro ⟨V, hV⟩
    obtain ⟨y, hy⟩ := h₁ K' ι' P' hP'.2.1 V
    have hcase := h₂ K ι K' ι' κ v P' n s α W hv hP' hP hs hsP hW V
      (fun a ha => hV ⟨⟨a, ha⟩, rfl⟩) y hy
    have hle : semiLocRing P' (fibreOver v P' W) ≤ V.toSubring := by
      rw [semiLocRing, Subring.closure_le]
      rintro _ ⟨u, w, a, hw, hwW, hu, hwa, rfl⟩
      have hwy : w ∉ y := by
        rcases hcase with rfl | hy'
        · exact fun h => nonZeroDivisors.ne_zero hw (Ideal.Quotient.eq_zero_iff_mem.mpr h)
        · exact hwW y hy'
      rw [SetLike.mem_coe, IsFractionRing.mk'_eq_div]
      exact (hy.2.2 a u w hu hwa hwy).1
    exact hle b.2
  rw [iInf_valuationSubring_superset, ← RingHom.coe_range, Subring.closure_eq] at hmem
  obtain ⟨p, hp, hpx⟩ := (hmem : IsIntegral f.range (b : FractionRing (MRing ι' ⧸ P')))
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    ((Polynomial.mem_lifts p).mpr
      (Polynomial.map_surjective f.rangeRestrict (fun ⟨_, a, ha⟩ => ⟨a, Subtype.ext ha⟩) p)) hp
  refine ⟨q, hqm, ?_⟩
  change Polynomial.eval₂ (f.range.subtype.comp f.rangeRestrict) (b : FractionRing _) q = 0
  rw [← Polynomial.eval₂_map, hq]
  exact hpx

end GroundTheory.Heights₂.Heights.Inter
