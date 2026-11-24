module

public import Formalism.WachLatticeTwists.RamifiedBlockRings.DistinctEigenvalueCornerPerturbation
public import Mathlib.FieldTheory.Separable
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

def bcT {O : Type} (O' : Type) [CommRing O] [CommRing O'] [Algebra O O'] {X : Type}
    (T : Subalgebra O (X → O)) : Subalgebra O' (X → O') :=
  Algebra.adjoin O' ((fun f : X → O => algebraMap O O' ∘ f) '' (T : Set (X → O)))

def bcM {O : Type} (O' : Type) [CommRing O] [CommRing O'] [Algebra O O'] {X d : Type}
    (a : X → Matrix d d O) : X → Matrix d d O' := fun x => (a x).map (algebraMap O O')

def bcR {O : Type} (O' : Type) [CommRing O] [CommRing O'] [Algebra O O'] {X d G : Type} [Fintype d]
    [DecidableEq d] [Group G] (r : G →* (X → Matrix d d O)) : G →* (X → Matrix d d O') where
  toFun g := bcM O' (r g)
  map_one' := by
    funext x
    simp [bcM]
  map_mul' g h := by
    funext x
    simp [bcM, Matrix.map_mul]

def bcChar {O : Type} (O' : Type) [CommRing O] [CommRing O'] [Algebra O O'] {G : Type} [Group G]
    (χ : G →* Oˣ) : G →* O'ˣ := (Units.map (algebraMap O O').toMonoidHom).comp χ

def StatBcSpan : Prop :=
  ∀ (O O' : Type) [CommRing O] [CommRing O'] [Algebra O O'] (X : Type) (T : Subalgebra O (X → O)),
    (bcT O' T : Set (X → O')) =
      Submodule.span O' ((fun f : X → O => algebraMap O O' ∘ f) '' (T : Set (X → O)))

def StatBcLocal : Prop :=
  ∀ (O O' : Type) [CommRing O] [IsLocalRing O] [CommRing O'] [IsLocalRing O'] [Algebra O O']
    [IsLocalHom (algebraMap O O')] (X : Type) [Finite X] [Nonempty X] (T : Subalgebra O (X → O)),
    IsLocalRing T → IsLocalRing (bcT O' T)

def StatAbsIrrExt : Prop :=
  ∀ (k k' : Type) [Field k] [Field k'] (f : k →+* k') (n : Type) [Fintype n] [DecidableEq n] (G : Type)
    [Monoid G] (ρ : G →* Matrix n n k), AbsIrr ρ → AbsIrr (fun g => (ρ g).map f)

def StatBcRank : Prop :=
  ∀ (O : Type) [CommRing O] [IsLocalRing O] (F F' : Type) [Field F] [Field F'] (f : O →+* F)
    (f' : O →+* F') (d : Type) [Fintype d] [DecidableEq d] (e : Matrix d d O), e * e = e →
    (e.map f').rank = (e.map f).rank

def StatBcSplit : Prop :=
  ∀ (K : Type) [Field K] (d : Type) [Fintype d] [DecidableEq d] (e a : Matrix d d K) (t : ℕ),
    e * e = e → e * a = a → a * e = a → e.rank = t →
    (blockPoly e a).Monic ∧ (blockPoly e a).natDegree = t ∧
    ((blockPoly e a).Separable → (blockPoly e a).Splits →
      ∃ α : Fin t → K, Function.Injective α ∧
        blockPoly e a = ∏ i, (Polynomial.X - Polynomial.C (α i)))

def StatStageC : Prop :=
  ∀ (O O' : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O'] [Module.Free O O']
    [Module.Finite O O'] (e : ℕ),
    (∀ y : O, IsDiscreteValuationRing.addVal O' (algebraMap O O' y) =
      e * IsDiscreteValuationRing.addVal O y) →
    ∀ (X : Type) [Fintype X] (T : Subalgebra O (X → O)) (d : Type) [Fintype d] [DecidableEq d]
      (G : Type) [Group G] (r : G →* (X → Matrix d d O)) (π : X) (t : ℕ) (bl : d → Fin (t + 1))
      (χ₁ ε : G →* Oˣ),
    PrimHyp O T r π bl χ₁ ε →
    AbsIrr (fun g => ((r g π).toSquareBlock bl 0).map (IsLocalRing.residue O)) →
    ∀ eB e₁ : X → Matrix d d O, IdemHyp O T r π bl eB e₁ →
    ∀ (g₀ : G) (s : X → Matrix d d O), s ∈ tSpan T r → eB * s = s → s * eB = s → s π = 0 →
    (∀ x, (blockPoly ((eB x).map (algebraMap O (FractionRing O)))
      ((eB x * r g₀ x * eB x + s x).map (algebraMap O (FractionRing O)))).Separable) →
    (∀ x, ((blockPoly (eB x) (eB x * r g₀ x * eB x + s x)).map
      ((algebraMap O' (FractionRing O')).comp (algebraMap O O'))).Splits) →
    PrimHyp O' (bcT O' T) (bcR O' r) π bl (bcChar O' χ₁) (bcChar O' ε) ∧
    AbsIrr (fun g => ((bcR O' r g π).toSquareBlock bl 0).map (IsLocalRing.residue O')) ∧
    IdemHyp O' (bcT O' T) (bcR O' r) π bl (bcM O' eB) (bcM O' e₁) ∧
    DistinctEigenvalueCornerPerturbation O' (bcT O' T) (bcR O' r) π t g₀ (bcM O' eB) (bcM O' s) ∧
    ∀ Z : Set X, vcc (bcT O' T) Z π = e * vcc T Z π

def ChainHyp (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {X : Type}
    (T : Subalgebra O (X → O)) {d : Type} [Fintype d] [DecidableEq d] {G : Type} [Group G]
    (r : G →* (X → Matrix d d O)) (π : X) {t : ℕ} (bl : d → Fin (t + 1)) (χ₁ ε : G →* Oˣ) (g₀ : G) :
    Prop :=
  PrimHyp O T r π bl χ₁ ε ∧
  AbsIrr (fun g => ((r g π).toSquareBlock bl 0).map (IsLocalRing.residue O)) ∧
  2 ≤ Fintype.card {a // bl a = 0} ∧
  (∀ x, ∃ (m : ℕ) (c : d → Fin m) (P : Matrix d d (FractionRing O)),
    BlockDiagonalIrreducibleAt (fun g => (r g x).map (algebraMap O (FractionRing O))) m c P) ∧
  (∀ i j : ℕ, i < t → j < t → (ε g₀) ^ i = (ε g₀) ^ j → i = j)

def ChainAB (O : Type) [CommRing O] [IsDomain O] {X : Type} (T : Subalgebra O (X → O)) {d : Type}
    [Fintype d] [DecidableEq d] {G : Type} [Group G] (r : G →* (X → Matrix d d O)) (π : X) {t : ℕ}
    (bl : d → Fin (t + 1)) (g₀ : G) (c : O) (eB e₁ s : X → Matrix d d O) : Prop :=
  IdemHyp O T r π bl eB e₁ ∧
  (∃ (m : ℕ) (jj : Fin m → X → O) (a : Fin m → X → Matrix d d O),
    (∀ i, jj i ∈ T ∧ jj i π = 0 ∧ a i ∈ tSpan T r) ∧
    s = fun x => c • ∑ i, jj i x • (eB x * a i x * eB x)) ∧
  (∀ x, (blockPoly ((eB x).map (algebraMap O (FractionRing O)))
    ((eB x * r g₀ x * eB x + s x).map (algebraMap O (FractionRing O)))).Separable)

end Formalism.RepresentationBoundsCohomology.ringDataObjects
