module

public import GroundTheory.HeightsAndTheta.Heights.StrongApproximation.Statements
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.StrongApproximation.EichPreserves

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.StrongApprox

open Matrix NumberField IsDedekindDomain TensorProduct Topology ReciprocityTheory.ChartRestriction.G.SA

theorem sigA_inclA_apply {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (c : E ≃ₐ[F] E)
    (x : E) : sigA c (inclA F E x) = inclA F E (c x) := by
  simp [sigA, inclA, Algebra.TensorProduct.map_tmul]

theorem OrthProjection.proof (hT : AETopologicalRing.Statement) : OrthProjection.Statement := by
  refine ⟨?_, ?_⟩
  · intro R _ σ hσ N J hJ e f hee hff hef
    have hfe : hf σ J f e = 1 := by rw [← hf_symm hσ hJ, hef, map_one]
    have perp : ∀ u, hf σ J (perpProj σ J e f u) e = 0 ∧ hf σ J (perpProj σ J e f u) f = 0 := by
      intro u
      simp only [perpProj, hf_sub_left, hf_smul_left, hee, hff, hef, hfe]
      constructor <;> ring
    have fix : ∀ u, hf σ J u e = 0 → hf σ J u f = 0 → perpProj σ J e f u = u := by
      intro u h1 h2
      simp [perpProj, h1, h2]
    refine ⟨⟨fun u v => ?_, fun a u => ?_⟩, fun u => fix _ (perp u).1 (perp u).2, perp, fix⟩
    · simp only [perpProj, hf_add_left, add_smul]
      abel
    · simp only [perpProj, hf_smul_left, smul_sub, mul_smul]
  · intro F E _ _ _ _ _ c h2 hc N J e f _ _
    have := (hT F E c h2 hc).1
    refine ⟨?_, fun u => ?_⟩
    · unfold perpProj hf
      fun_prop
    · have hmap : ∀ x y : Fin N → E, inclA F E (hf c.toRingHom J x y) =
          hf (sigA c) (J.map (inclA F E)) (inclA F E ∘ x) (inclA F E ∘ y) := by
        intro x y

        simp [hf, map_sum, map_mul, sigA_inclA_apply]
      funext i
      simp only [perpProj, Function.comp_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub,
        map_mul, hmap]

end GroundTheory.Heights₂.Heights.StrongApprox
