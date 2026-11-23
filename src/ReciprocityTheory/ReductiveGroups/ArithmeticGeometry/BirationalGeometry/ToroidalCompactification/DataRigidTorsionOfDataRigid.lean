module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegUnif
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

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj

def LatFinOrdSt : Prop :=
  ∀ (Y : Type) [AddCommGroup Y] [Module.Free ℤ Y] [Module.Finite ℤ Y] (b : LinearMap.BilinForm ℤ Y),
    (∀ y z, b y z = b z y) → (∀ y, y ≠ 0 → 0 < b y y) →
    ∀ σ : Y ≃ₗ[ℤ] Y, (∀ y z, b (σ y) (σ z) = b y z) → ∃ n : ℕ, 0 < n ∧ σ ^ n = 1

def LatMinkowskiSt : Prop :=
  ∀ (Y : Type) [AddCommGroup Y] [Module.Free ℤ Y] [Module.Finite ℤ Y] (σ : Y ≃ₗ[ℤ] Y) (n M : ℕ), 0 < n →
    σ ^ n = 1 → 3 ≤ M → (∀ y, ∃ z, σ y = y + M • z) → σ = 1

section Gt

open ReciprocityTheory.ChartRestriction.G.Out

def GtCoordToGtSt : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (e : ℕ) (G : Over (Spec (CommRingCat.of R)))
    [GrpObj G] [IsCommMonObj G], Nonempty (GtCoord I D e G) →
    ∃ (E : SplitExt (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
      (β : E.B ≅ thickObj R I e D.P.A) (xe : D.X ≃+ E.X), IsMonHom β.hom ∧
      (∀ χ : D.X, ∃ w : LB.Iso (E.O (xe χ)).L (LB.LinComb D.P.L
          (fun k => ((Over.map (thick R I e)).map β.hom ≫ D.prBe I e).left ≫
            D.Oφ (𝟙 _) χ k) Oε), w.IsGen) ∧
      E.IsGt (thickObj R I e G)

end Gt

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
