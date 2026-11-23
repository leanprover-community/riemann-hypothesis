module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FiniteResidueFieldPadicInt
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
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EsymmInvMulEsymmCard

@[expose] public section

open GlobalTheory.LatHecke GlobalTheory.SatakeInv

noncomputable section
namespace GlobalTheory.LatHecke

def coordIncl (O K : Type) [CommRing O] [Field K] [Algebra O K] (r : ℕ) :
    (Fin r → O) →ₗ[O] (Fin r → K) :=
  LinearMap.pi fun i => (Algebra.linearMap O K).comp (LinearMap.proj i)

theorem coordIncl_apply {O K : Type} [CommRing O] [Field K] [Algebra O K] {r : ℕ} (x : Fin r → O) :
    coordIncl O K r x = fun i => algebraMap O K (x i) := rfl

theorem coordIncl_injective {O K : Type} [CommRing O] [IsDomain O] [Field K] [Algebra O K]
    [IsFractionRing O K] {r : ℕ} : Function.Injective (coordIncl O K r) := by
  intro x y h
  funext i
  exact IsFractionRing.injective O K (congrFun h i)

theorem std_eq_map_top (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
    [Algebra O K] [IsFractionRing O K] (r : ℕ) :
    (std O K r).1 = (⊤ : Submodule O (Fin r → O)).map (coordIncl O K r) := by
  rw [← (Pi.basisFun O (Fin r)).span_eq, Submodule.map_span, ← Set.range_comp]
  show Submodule.span O (Set.range (Pi.basisFun K (Fin r))) = _
  congr 2
  funext i
  funext j
  simp [coordIncl_apply, Pi.single_apply]

theorem glMap_std_eq {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
    [Algebra O K] [IsFractionRing O K] {r : ℕ} (A : Matrix (Fin r) (Fin r) O) (g : GL (Fin r) K)
    (hg : (g : Matrix (Fin r) (Fin r) K) = A.map (algebraMap O K)) :
    glMap g (std O K r).1 = (LinearMap.range A.mulVecLin).map (coordIncl O K r) := by
  rw [glMap, std_eq_map_top, ← Submodule.map_comp, LinearMap.range_eq_map,
    ← Submodule.map_comp]
  congr 1
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, Matrix.toLin'_apply,
      Matrix.mulVecLin_apply, coordIncl_apply, hg]
  funext i
  exact (RingHom.map_mulVec (algebraMap O K) A x i).symm

end GlobalTheory.LatHecke


open GlobalTheory.LatHecke in
theorem GlobalTheory.LatHecke.relIndex_glMap_std_of_integral : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] (r : ℕ) (A : Matrix (Fin r) (Fin r) O) (g : GL (Fin r) K), (g : Matrix (Fin r) (Fin r) K) = A.map (algebraMap O K) → (glMap g (std O K r).1).toAddSubgroup.relIndex (std O K r).1.toAddSubgroup = Nat.card ((Fin r → O) ⧸ LinearMap.range A.mulVecLin) ∧ (IsLocalRing.maximalIdeal O • (std O K r).1 ≤ glMap g (std O K r).1 → IsLocalRing.maximalIdeal O • (⊤ : Submodule O (Fin r → O)) ≤ LinearMap.range A.mulVecLin) := by
  intro O K _ _ _ _ _ _ r A g hg
  rw [glMap_std_eq A g hg, std_eq_map_top]
  refine ⟨?_, ?_⟩
  · have h := AddSubgroup.relIndex_map_map_of_injective (f := (coordIncl O K r).toAddMonoidHom)
      (LinearMap.range A.mulVecLin).toAddSubgroup (⊤ : Submodule O (Fin r → O)).toAddSubgroup
      coordIncl_injective
    refine h.trans ?_
    rw [Submodule.top_toAddSubgroup, AddSubgroup.relIndex_top_right]
    rfl
  · intro h
    rw [← Submodule.map_smul''] at h
    exact (Submodule.map_le_map_iff_of_injective coordIncl_injective _ _).1 h
