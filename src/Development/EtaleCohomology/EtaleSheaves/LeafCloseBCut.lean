module

public import Development.EtaleCohomology.EtaleSheaves.LeafSpreadVCut
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

@[expose] public section

noncomputable section
open CategoryTheory AlgebraicGeometry LateralTheory.E.E4

namespace LateralTheory.E.LeafCloseBCut

def LeafProjModel : Prop := ∀ (k : Type) [Field k] (A : Type) [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A], ∃ (B : Scheme.{0}) (b : B ⟶ Sp k) (ι : Sp A ⟶ B), IsIntegral B ∧ IsProper b ∧
    IsOpenImmersion ι ∧ ι ≫ b = Spec.map (CommRingCat.ofHom (algebraMap k A))

def LeafDimOpen : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} (b : X ⟶ Sp k) [LocallyOfFiniteType b],
    IsIntegral X → ∀ U : Set X, IsOpen U → U.Nonempty → topologicalKrullDim X ≤ topologicalKrullDim U

theorem goal_of (h1 : LeafProjModel) (h2 : LeafDimOpen) : LateralTheory.E.LeafSpreadVCut.LeafCloseB := by
  intro k _ A _ _ _ _
  obtain ⟨B, b, ι, hB, hb, hι, hc⟩ := h1 k A
  refine ⟨B, b, ι, hB, hb, hι, hc, ?_⟩
  obtain ⟨x⟩ : Nonempty (PrimeSpectrum A) := inferInstance
  have hemb := ι.isOpenEmbedding
  calc topologicalKrullDim B ≤ topologicalKrullDim (Set.range ι) :=
        h2 k b hB _ hemb.isOpen_range ⟨ι x, x, rfl⟩
    _ = topologicalKrullDim (Sp A) :=
        (IsHomeomorph.topologicalKrullDim_eq _ (hemb.isEmbedding.toHomeomorph).isHomeomorph).symm
    _ = ringKrullDim A := PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim A

end LateralTheory.E.LeafCloseBCut

end
