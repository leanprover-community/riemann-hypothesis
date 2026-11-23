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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.StrongApproximation.DenseRangeFiniteAdele

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace StrongApprox

open NumberField IsDedekindDomain TensorProduct Topology ReciprocityTheory.ChartRestriction.G.SA

theorem EDenseInAE.proof (hT : AETopologicalRing.Statement) : EDenseInAE.Statement := by
  intro F E _ _ _ _ _ c h2 hc _ _
  obtain ⟨-, -, ⟨δ, -, hδ⟩, -⟩ := hT F E c h2 hc
  have : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (FiniteAdeleRing (𝓞 F) F) (AE F E)
  let φ : FiniteAdeleRing (𝓞 F) F × FiniteAdeleRing (𝓞 F) F → AE F E :=
    fun p => p.1 • (1 : AE F E) + p.2 • inclA F E δ
  have hφc : Continuous φ :=
    by unfold φ; fun_prop
  have hφs : Function.Surjective φ := fun a => by
    obtain ⟨p, hp, -⟩ := hδ a
    exact ⟨p, hp.symm⟩
  have hK : DenseRange (algebraMap F (FiniteAdeleRing (𝓞 F) F)) :=
    denseRange_finiteAdele (R := 𝓞 F) (K := F)
  have hD : DenseRange (φ ∘ Prod.map (algebraMap F (FiniteAdeleRing (𝓞 F) F))
      (algebraMap F (FiniteAdeleRing (𝓞 F) F))) :=
    hφs.denseRange.comp (hK.prodMap hK) hφc
  refine hD.mono ?_
  rintro _ ⟨⟨x, y⟩, rfl⟩
  refine ⟨algebraMap F E x + algebraMap F E y * δ, ?_⟩
  simp only [Function.comp_apply, Prod.map_apply, φ, algebraMap_smul, map_add (f := _), map_mul]
  have hinc : ∀ z : F, inclA F E (algebraMap F E z) = z • (1 : AE F E) := fun z => by
    rw [← Algebra.algebraMap_eq_smul_one]
    exact (Algebra.TensorProduct.includeRight : E →ₐ[F] AE F E).commutes z
  rw [hinc, hinc, smul_one_mul]

end StrongApprox

end GroundTheory.Heights₂.Heights
