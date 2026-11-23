module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSegreFlagCutProjection
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

section Objects

variable {K : Type*} {ι : K → Type} {Ω : Type*} [Field Ω] {N M M' : ℕ} {E : Type*} [AddCommGroup E]
  [Module Ω E] {Φ : Type*} [Field Φ] [Algebra Ω Φ]

def flagProjPt {K' : Type*} (j : K' ↪ Option (Option K)) (y : (Σ k, ι k) → Ω) (w e : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) (φ' : Fin M' → Module.Dual Ω E) (t : Fin N → Φ) (k : ℕ) :
    (Σ o, bundleIdx (bundleIdx ι M) M' (j o)) → Φ :=
  fun p => flagClosurePt y w e φ φ' t k (FieldNumbers.blockIncl j (bundleIdx (bundleIdx ι M) M') p)

end Objects

theorem comap_pointIdeal_blockIncl {R : Type*} [CommRing R] {Φ : Type*} [Field Φ] [Algebra R Φ] {K K' : Type*}
    (j : K ↪ K') {ι' : K' → Type*} (pt : (Σ k', ι' k') → Φ) :
    (pointIdeal R pt).comap (rename (FieldNumbers.blockIncl j ι')) =
      pointIdeal R (fun p => pt (FieldNumbers.blockIncl j ι' p)) := by
  have key : ((pointConeMap R pt).comp (rename (FieldNumbers.blockIncl j ι'))) =
      ((rename j).restrictScalars R).comp (pointConeMap R (fun p => pt (FieldNumbers.blockIncl j ι' p))) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [pointConeMap, FieldNumbers.blockIncl]
  ext f
  simp only [pointIdeal, Ideal.mem_comap, RingHom.mem_ker]
  have hf := congrArg (fun φ => φ f) key
  simp only [AlgHom.comp_apply] at hf
  rw [hf, AlgHom.restrictScalars_apply]
  exact map_eq_zero_iff _ (rename_injective _ j.injective)

def SegreFlagCutLiesOver.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (Ω : Type) [Field Ω] [Algebra O Ω]
      (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (y : (Σ k, ι k) → Ω) (d : ℕ), IsModelOver (pointIdeal O y) d →
    ∀ (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E]
      (B B' : ChartBundle O (segreVec y) N E), SameGenericFibre ϖ B B' →
    ∀ (w w' : Module.Basis (Fin N) Ω E) (x x' : Fin N → K → ℤ) (f g : Fin N → MRing ι O),
      IsFlagPair ϖ y B B' w w' x x' f g →
    ∀ (M M' : ℕ) (a₀ a₀' : K → ℤ) (φ : Fin M → Module.Dual Ω E) (φ' : Fin M' → Module.Dual Ω E),
      IsTwistedDualGens y B a₀ φ → IsTwistedDualGens y B' a₀' φ' →
    ∀ (Φ : Type) [Field Φ] [Algebra Ω Φ] [Algebra O Φ] [IsScalarTower O Ω Φ]
      (e : Module.Basis (Fin N) Ω E) (t : Fin N → Φ), AlgebraicIndependent Ω t →
    ∀ (k : ℕ) (hk : k < N),
      (∀ (cs ch : Option (Option K) → ℕ) (s h : MRing (bundleIdx (bundleIdx ι M) M') O),
        IsMultiHomog s cs → IsMultiHomog h ch →
        (fun o => (cs o : ℤ) - ch o) = zetaFirst a₀ + liftPairDeg (x ⟨k, hk⟩) →
        s ∉ pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) → h ∉ pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) →
        aeval (flagClosurePt y w e φ φ' t (k + 1)) s = flagLineCoord w w e t (k + 1) ⟨k, hk⟩ * aeval (flagClosurePt y w e φ φ' t (k + 1)) h →
        ∀ W, (C ϖ : MRing (bundleIdx (bundleIdx ι M) M') O) ∈ W → ratDiv (pointIdeal O (flagClosurePt y w e φ φ' t (k + 1))) s h W ≠ 0 →
        pointIdeal O (flagProjPt Function.Embedding.some y w e φ φ' t k) ≤
          W.comap (rename (FieldNumbers.blockIncl Function.Embedding.some (bundleIdx (bundleIdx ι M) M')))) ∧
      (∀ (cs ch : Option (Option K) → ℕ) (s h : MRing (bundleIdx (bundleIdx ι M) M') O),
        IsMultiHomog s cs → IsMultiHomog h ch →
        (fun o => (cs o : ℤ) - ch o) = zetaSecond a₀' + liftPairDeg (x' ⟨k, hk⟩) →
        s ∉ pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) → h ∉ pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) →
        aeval (flagClosurePt y w e φ φ' t (k + 1)) s = flagLineCoord w' w e t (k + 1) ⟨k, hk⟩ * aeval (flagClosurePt y w e φ φ' t (k + 1)) h →
        ∀ W, (C ϖ : MRing (bundleIdx (bundleIdx ι M) M') O) ∈ W → ratDiv (pointIdeal O (flagClosurePt y w e φ φ' t (k + 1))) s h W ≠ 0 →
        pointIdeal O (flagProjPt secondFactorBlocks y w e φ φ' t k) ≤
          W.comap (rename (FieldNumbers.blockIncl secondFactorBlocks (bundleIdx (bundleIdx ι M) M'))))

def SegreFlagProjSpecialDim.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (Ω : Type) [Field Ω] [Algebra O Ω]
      (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (y : (Σ k, ι k) → Ω) (d : ℕ), IsModelOver (pointIdeal O y) d →
    ∀ (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E]
      (B B' : ChartBundle O (segreVec y) N E), SameGenericFibre ϖ B B' →
    ∀ (w w' : Module.Basis (Fin N) Ω E) (x x' : Fin N → K → ℤ) (f g : Fin N → MRing ι O),
      IsFlagPair ϖ y B B' w w' x x' f g →
    ∀ (M M' : ℕ) (a₀ a₀' : K → ℤ) (φ : Fin M → Module.Dual Ω E) (φ' : Fin M' → Module.Dual Ω E),
      IsTwistedDualGens y B a₀ φ → IsTwistedDualGens y B' a₀' φ' →
    ∀ (Φ : Type) [Field Φ] [Algebra Ω Φ] [Algebra O Φ] [IsScalarTower O Ω Φ]
      (e : Module.Basis (Fin N) Ω E) (t : Fin N → Φ), AlgebraicIndependent Ω t →
    ∀ k : ℕ, k < N →
      FieldNumbers.relDim (specialIdeal (pointIdeal O (flagProjPt Function.Embedding.some y w e φ φ' t k))) <
          ((d + k : ℕ) : WithBot (WithTop ℤ)) ∧
        FieldNumbers.relDim (specialIdeal (pointIdeal O (flagProjPt secondFactorBlocks y w e φ φ' t k))) <
          ((d + k : ℕ) : WithBot (WithTop ℤ))

end

end GroundTheory.Heights₂.Heights.NumbersDVR
