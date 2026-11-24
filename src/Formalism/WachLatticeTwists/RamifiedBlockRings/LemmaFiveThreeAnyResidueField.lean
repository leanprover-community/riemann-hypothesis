module

public import Formalism.WachLatticeTwists.RamifiedBlockRings.ChainFromPrimitiveData
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Formalism.WachLatticeTwists.CoprimeLiftBounds.Statement

@[expose] public section

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.ringDataObjects

open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities Formalism.RepresentationBoundsCohomology.BR

def StatKerBc : Prop :=
  ∀ (O O' : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O'] (e : ℕ),
    (∀ y : O, IsDiscreteValuationRing.addVal O' (algebraMap O O' y) =
      e * IsDiscreteValuationRing.addVal O y) →
    ∀ (m n : Type) [Fintype m] [Fintype n] [DecidableEq n] (A : Matrix m n O),
      Module.length O' (LinearMap.ker (relMap O' (KO O') (A.map (algebraMap O O')))) =
        e * Module.length O (LinearMap.ker (relMap O (KO O) A))

def StatModuleBc : Prop :=
  ∀ (O O' : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O'] [Module.Free O O']
    [Module.Finite O O'] (e : ℕ),
    (∀ y : O, IsDiscreteValuationRing.addVal O' (algebraMap O O' y) =
      e * IsDiscreteValuationRing.addVal O y) →
    ∀ (X : Type) [Fintype X] (d G : Type) [Fintype d] [DecidableEq d] [Group G] (t : ℕ)
      (bl : d → Fin (t + 1)) (T : Subalgebra O (X → O)) (r : G →* (X → Matrix d d O)) (π : X)
      (χ₁ ε : G →* Oˣ) (g₀ : G) (eB e₁ s : X → Matrix d d O),
    DistinctEigenvalueCornerPerturbation O T r π t g₀ eB s →
    ∀ (D : RingData O X d G t bl) (D' : RingData O' X d G t bl),
      RingDef O T r π χ₁ ε g₀ eB e₁ s D →
      RingDef O' (bcT O' T) (bcR O' r) π (bcChar O' χ₁) (bcChar O' ε) g₀ (bcM O' eB) (bcM O' e₁)
        (bcM O' s) D' →
    ∀ [IsNoetherian D.R' D.R'] [∀ k, SMulCommClass D.R' O (blockRestrictedRepresentationType bl D.ρk k)]
      [∀ k, SMulCommClass D'.R' O' (blockRestrictedRepresentationType bl D'.ρk k)]
      (NN : Type) [AddCommGroup NN] [Module D.R' NN] (g : ℕ) (n : Fin g → NN),
      Submodule.span D.R' (Set.range n) = ⊤ →
      ∃ (NN' : Type) (_ : AddCommGroup NN') (_ : Module D'.R' NN') (n' : Fin g → NN'),
        Submodule.span D'.R' (Set.range n') = ⊤ ∧
        (∀ Z : Set X, (∀ x', D.p x' ∉ Z → ∃ φ : NN →ₗ[D.R'] EvalSp O d D.R' x', φ ≠ 0) →
          ∀ y', D'.p y' ∉ Z → ∃ φ : NN' →ₗ[D'.R'] EvalSp O' d D'.R' y', φ ≠ 0) ∧
        ∀ k, Module.length O' (NN' →ₗ[D'.R'] blockRestrictedRepresentationType bl D'.ρk k) =
          e * Module.length O (NN →ₗ[D.R'] blockRestrictedRepresentationType bl D.ρk k)

def StatBigResidueExt : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (N : ℕ),
    ∃ (O' : Type) (_ : CommRing O') (_ : IsDomain O') (_ : IsDiscreteValuationRing O')
      (_ : Algebra O O') (_ : Module.Free O O') (_ : Module.Finite O O'),
      (∀ y : O, IsDiscreteValuationRing.addVal O' (algebraMap O O' y) =
        IsDiscreteValuationRing.addVal O y) ∧
      (N : Cardinal) < Cardinal.mk (IsLocalRing.ResidueField O')

def LemmaFiveThreeOverExtension : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (X : Type) [Fintype X]
    (d G : Type) [Fintype d] [DecidableEq d] [Group G] (t : ℕ) (_ : 1 ≤ t) (bl : d → Fin (t + 1))
    (T : Subalgebra O (X → O)) (r : G →* (X → Matrix d d O)) (π : X) (χ₁ ε : G →* Oˣ) (g₀ : G)
    (eB e₁ s : X → Matrix d d O),
    PrimHyp O T r π bl χ₁ ε →
    AbsIrr (fun g => ((r g π).toSquareBlock bl 0).map (IsLocalRing.residue O)) →
    IdemHyp O T r π bl eB e₁ → DistinctEigenvalueCornerPerturbation O T r π t g₀ eB s →
    ∀ (D : RingData O X d G t bl), RingDef O T r π χ₁ ε g₀ eB e₁ s D →
    ∀ [IsNoetherian D.R' D.R'] [∀ k, SMulCommClass D.R' O (blockRestrictedRepresentationType bl D.ρk k)]
      (Z : Set X) (NN : Type) [AddCommGroup NN] [Module D.R' NN] (g : ℕ) (n : Fin g → NN),
      Submodule.span D.R' (Set.range n) = ⊤ →
      (∀ x', D.p x' ∉ Z → ∃ φ : NN →ₗ[D.R'] EvalSp O d D.R' x', φ ≠ 0) →
    ∀ (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O']
      [Module.Free O O'] [Module.Finite O O'] (e : ℕ),
      (∀ y : O, IsDiscreteValuationRing.addVal O' (algebraMap O O' y) =
        e * IsDiscreteValuationRing.addVal O y) →
      ((g * Fintype.card d : ℕ) : Cardinal) < Cardinal.mk (IsLocalRing.ResidueField O') →
      vcc T Z π ≤ ∑ k : Fin (t + 1), Module.length O (NN →ₗ[D.R'] blockRestrictedRepresentationType bl D.ρk k)

def LemmaFiveThreeAnyResidueField : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (X : Type) [Fintype X]
    (d G : Type) [Fintype d] [DecidableEq d] [Group G] (t : ℕ) (_ : 1 ≤ t) (bl : d → Fin (t + 1))
    (T : Subalgebra O (X → O)) (r : G →* (X → Matrix d d O)) (π : X) (χ₁ ε : G →* Oˣ) (g₀ : G)
    (eB e₁ s : X → Matrix d d O),
    PrimHyp O T r π bl χ₁ ε →
    AbsIrr (fun g => ((r g π).toSquareBlock bl 0).map (IsLocalRing.residue O)) →
    IdemHyp O T r π bl eB e₁ → DistinctEigenvalueCornerPerturbation O T r π t g₀ eB s →
    ∀ (D : RingData O X d G t bl), RingDef O T r π χ₁ ε g₀ eB e₁ s D →
    ∀ [IsNoetherian D.R' D.R'] [∀ k, SMulCommClass D.R' O (blockRestrictedRepresentationType bl D.ρk k)]
      (Z : Set X) (NN : Type) [AddCommGroup NN] [Module D.R' NN] (g : ℕ) (n : Fin g → NN),
      Submodule.span D.R' (Set.range n) = ⊤ →
      (∀ x', D.p x' ∉ Z → ∃ φ : NN →ₗ[D.R'] EvalSp O d D.R' x', φ ≠ 0) →
      vcc T Z π ≤ ∑ k : Fin (t + 1), Module.length O (NN →ₗ[D.R'] blockRestrictedRepresentationType bl D.ρk k)

end Formalism.RepresentationBoundsCohomology.ringDataObjects
