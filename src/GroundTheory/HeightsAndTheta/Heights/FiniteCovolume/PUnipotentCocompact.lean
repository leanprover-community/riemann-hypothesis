module

public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StUnipotentHorizontal
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StUnipotentCentral
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PWittPartner
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem UnipotentCocompact.proof (h : HermitianForm F E W) (v : Basis ι E W)
    (hP : UnipotentCoordProper.Statement h v) (hH : UnipotentHorizontal.Statement h v)
    (hC : UnipotentCentral.Statement h v) : UnipotentCocompact.Statement h v := by
  intro D La x₀ hLa hx₀ hne hiso
  obtain ⟨w₀, h1, h2⟩ := WittPartner.proof h x₀ hne hiso
  have hp : IsHyperbolicPair h x₀ w₀ := ⟨hiso, h2, h1⟩
  obtain ⟨K₁, hK₁, hred⟩ := hH D La x₀ w₀ hLa hx₀ hp
  obtain ⟨K, hK, hcen⟩ := hC D La x₀ w₀ hLa hx₀ hp K₁ hK₁
  refine ⟨{n | unipCoord h v x₀ w₀ n ∈ K}, hP x₀ w₀ hp K hK, fun n => ?_⟩
  obtain ⟨δ₁, hδ₁, t, ht⟩ := hred n
  obtain ⟨δ₂, hδ₂, hK'⟩ := hcen (δ₁ * n) ⟨t, ht⟩
  refine ⟨δ₂ * δ₁, ?_, ?_⟩
  · exact Subgroup.mul_mem _ hδ₂ hδ₁
  · change unipCoord h v x₀ w₀ (δ₂ * δ₁ * n) ∈ K
    rwa [mul_assoc]

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
