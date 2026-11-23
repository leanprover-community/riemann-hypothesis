module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.DetOfCharpoly
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyPosDefHermFormNearZeroMatrixStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPeriodMapCompInjectiveRealLinearStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannRelationConverseConjAffineStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.PerCoordU GlobalTheory.PeriodCoord

namespace UpperTheory.Gal.W2

theorem perNear_of : PerNear := by
  intro O _ bar g ρ D P₀ M₀ hP hM d co hco
  obtain ⟨hHerm, hPos, hIm⟩ := hM
  have hdet : M₀.det ≠ 0 := det_ne_zero_of_pos hPos
  obtain ⟨t, ht, htO, ht0⟩ := eventually_nhds_iff.mp (T.eventually_posDef_hermForm_near_zero_matrix M₀ hPos)
  have hcont : Continuous co := LinearMap.continuous_of_finiteDimensional co
  refine ⟨co ⁻¹' t, htO.preimage hcont, by simpa using ht0, ?_, ?_⟩
  · intro b hb
    obtain ⟨h1, h2, h3⟩ := ht (co b) hb
    have hT : (co b)ᵀ * M₀ ∈ Tsp bar ρ := hco b
    obtain ⟨hH, hF⟩ := T.riemann_relation_converse_conjAffine M₀ (co b) hHerm hdet hT.1 h1
    have hcomm := comm_of_mem_Tsp hP hIm hdet hT
    refine T.isPeriodMap_comp_injective_realLinear D ρ P₀ (realMap 1 (co b)) (M₀ * (1 - (co b).map star * co b)⁻¹) hP
      (realMap_one_injective h2) ?_ hH h3 ?_
    · intro a x
      simp only [realMap_apply, Matrix.one_mulVec, Matrix.mulVec_add, star_mulVec_map,
        Matrix.mulVec_mulVec, hcomm a]
      rw [Matrix.one_mul]
    · intro x y
      simp only [realMap_apply, Matrix.one_mulVec]
      rw [hF, hIm]
  · intro x
    set v := star (P₀ x)
    let f : (Fin d → ℂ) →ₗ[ℂ] (Fin g → ℂ) :=
      { toFun := fun b => co b *ᵥ v
        map_add' := by intro a b; simp [Matrix.add_mulVec]
        map_smul' := by intro c b; simp [Matrix.smul_mulVec] }
    have hf : Differentiable ℂ (fun b => co b *ᵥ v) :=
      (LinearMap.toContinuousLinearMap f).differentiable
    have : (fun b => (perC P₀ (co b)) x) = fun b => P₀ x + co b *ᵥ v := by
      funext b; simp [perC_apply, v]
    rw [this]
    exact ((differentiable_const _).add hf).differentiableOn

end UpperTheory.Gal.W2
