module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
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

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section
namespace GlobalTheory.ZJ
variable {S : Scheme.{0}} {H : Over S} [GrpObj H]

def Charts.InK (C : Charts H.left) (a : {i // C.wt i = C.c₀}) {Y : Over S} (k : Y ⟶ H) : Prop :=
  ∃ (h : ⊤ ≤ k.left ⁻¹ᵁ C.W a) (h₁ : ⊤ ≤ (1 : Y ⟶ H).left ⁻¹ᵁ C.W a), ∀ j, C.wt j = C.c₀ →
    (k.left.appLE _ ⊤ h).hom (C.r a j) = ((1 : Y ⟶ H).left.appLE _ ⊤ h₁).hom (C.r a j)

def Charts.Based (C : Charts H.left) {d : ℕ} (c : Fin d → C.Cl) (a : {i // C.wt i = C.c₀}) (j : Fin d → C.I) : Prop :=
  ⊤ ≤ eSec H ⁻¹ᵁ C.W a ∧ ∀ n, C.wt (j n) = c n ∧ ⊤ ≤ eSec H ⁻¹ᵁ H.left.basicOpen (C.r a (j n))

def Charts.KerIs (C : Charts H.left) {d : ℕ} (a : {i // C.wt i = C.c₀}) (j : Fin d → C.I)
    (i : splitTorus S (Fin d → ℤ) ⟶ H) : Prop :=
  Mono i ∧ (∀ (Y : Over S) (k : Y ⟶ H), C.InK a k ↔ ∃ t, k = t ≫ i) ∧
    ∀ (Y : Over S) (t : Y ⟶ splitTorus S (Fin d → ℤ)) (n : Fin d) (h : ⊤ ≤ (t ≫ i).left ⁻¹ᵁ C.W a)
      (h₁ : ⊤ ≤ (1 : Y ⟶ H).left ⁻¹ᵁ C.W a), ((t ≫ i).left.appLE _ ⊤ h).hom (C.r a (j n)) =
        t.left.appTop.hom (charUnit S (Fin d → ℤ) (Pi.single n 1)).val * ((1 : Y ⟶ H).left.appLE _ ⊤ h₁).hom (C.r a (j n))

end GlobalTheory.ZJ
end
