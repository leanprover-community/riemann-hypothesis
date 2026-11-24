module

public import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsSemilocFinite
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsSemilocIntegral
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsLocRingIntClosure
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsLocRingDimOne
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsSmoothHermFubiniStudyO1

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

theorem semiLocRing_le_empty {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (P : Ideal (MRing ι))
    (𝒲 : Set (Ideal (MRing ι))) : semiLocRing P 𝒲 ≤ semiLocRing P ∅ := by
  unfold semiLocRing
  refine Subring.closure_mono ?_
  rintro _ ⟨u, w, a, hw, -, hu, hwa, rfl⟩
  exact ⟨u, w, a, hw, fun _ h => h.elim, hu, hwa, rfl⟩

theorem SemilocFinite.proof (h₁ : SemilocIntegral.Statement) (h₂ : LocRingIntClosureFinite.Statement)
    (h₃ : LocRingDimOne.Statement) : SemilocFinite.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' n s α W hv hP' hQ hs hsQ hW
  have := hP'.2.1.1
  let _ := (locToSemiloc hv P' W).toAlgebra
  have hN : IsNoetherianRing (locRing (imageZ v P') W) := (h₃ K ι (imageZ v P') s α W hQ.2.1 hs hsQ hW).1
  have hint := h₁ K ι K' ι' κ v P' n s α W hv hP' hQ hs hsQ hW
  refine ⟨?_, ?_⟩
  · let _ := ((fracMapZ v P').comp (locRing (imageZ v P') W).subtype).toAlgebra
    let _ : Module (locRing (imageZ v P') W) (FractionRing (MRing ι' ⧸ P')) := Algebra.toModule
    obtain ⟨t, ht⟩ := h₂ K ι K' ι' κ v P' n s α W hv hP' hQ hs hsQ hW
    let g : semiLocRing P' (fibreOver v P' W) →ₗ[locRing (imageZ v P') W] FractionRing (MRing ι' ⧸ P') :=
      { toFun := Subtype.val, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    have hg : ∀ b, g b ∈ Submodule.span (locRing (imageZ v P') W) (t : Set (FractionRing (MRing ι' ⧸ P'))) :=
      fun b => ht _ (semiLocRing_le_empty P' _ b.2)
        ((hint.isIntegral b).map_of_comp_eq (RingHom.id (locRing (imageZ v P') W)) (semiLocRing P' (fibreOver v P' W)).subtype
          (RingHom.ext fun _ => rfl))
    have : IsNoetherian (locRing (imageZ v P') W)
        (Submodule.span (locRing (imageZ v P') W) (t : Set (FractionRing (MRing ι' ⧸ P')))) :=
      isNoetherian_span_of_finite _ t.finite_toSet
    exact Module.Finite.of_injective (g.codRestrict _ hg)
      fun b c hbc => by
        have h := congrArg Subtype.val hbc
        exact Subtype.ext h
  · have := imageZ_isPrime_of_prime v P'
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    intro a b hab
    exact Subtype.val_injective ((fracMapZ v P').injective (congrArg Subtype.val hab))

end GroundTheory.Heights₂.Heights.Inter
