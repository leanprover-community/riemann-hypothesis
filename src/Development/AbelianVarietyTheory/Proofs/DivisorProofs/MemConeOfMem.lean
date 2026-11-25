module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAlgAtlasAtlasOf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernLeviEqConstant

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.Mean4O
open scoped NNReal

namespace GlobalTheory.VertForm

section Algebra

universe u

variable {E : Type u} [AddCommGroup E] [Module ℝ E] {D : ℕ}


variable (E D) in
abbrev Form : Type u := (Π _ : Fin (D + 1), E) →ₘₗ[ℝ] ℝ

variable {num : Form E D} {G : Set E}

end Algebra

section Bundles

variable {k : Type} [CommRing k] {X X' : Scheme.{0}} {p : X ⟶ Sp k} {q : X' ⟶ Sp k}



def NefOver (L : HermLB p) (l : ℕ) : Prop :=
  ∀ (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z] (κ : Type)
    [Field κ] [Finite κ] [CharP κ l] [Algebra κ Γ(Z, ⊤)], topologicalKrullDim Z = 1 → 0 ≤ topSelfIntersection κ (L.B.pull i) 1

theorem nefFib_iff (L : HermLB p) : NefFib L ↔ ∀ l : ℕ, l.Prime → NefOver L l :=
  ⟨fun h _ _ Z i _ _ κ _ _ _ _ hZ => h Z i κ hZ, fun h Z i _ _ κ _ _ _ hZ =>
    h (ringChar κ) (CharP.char_is_prime κ _) Z i κ hZ⟩

end Bundles

section Covers

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

end Covers

end GlobalTheory.VertForm

end
