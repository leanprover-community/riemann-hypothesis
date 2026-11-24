module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw

namespace GlobalTheory.FormalAlg

structure Charts {R : Type} [CommRing R] (I : Ideal R)
    (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
    (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (n : ℕ) where

  D : ∀ e, Fin (n + 1) → (Y e).left.Opens

  aff : ∀ e i, IsAffineOpen (D e i)

  cover : ∀ e, ⨆ i, D e i = ⊤

  pre : ∀ e i, β e ⁻¹ᵁ D (e + 1) i = D e i

  ρ : ∀ e i, Fin (n + 1) → Γ((Y e).left, D e i)

  ρ_pull : ∀ e i j, ((β e).appLE (D (e + 1) i) (D e i) (pre e i).ge).hom (ρ (e + 1) i j) = ρ e i j

  ρ_self : ∀ i, ρ 0 i i = 1

  basic : ∀ i j, (Y 0).left.basicOpen (ρ 0 i j) = D 0 i ⊓ D 0 j

  cocycle : ∀ i j l, rs (Y 0).left (inf_le_left : D 0 i ⊓ D 0 j ≤ D 0 i) (ρ 0 i l) =
    rs (Y 0).left (inf_le_left : D 0 i ⊓ D 0 j ≤ D 0 i) (ρ 0 i j) *
      rs (Y 0).left (inf_le_right : D 0 i ⊓ D 0 j ≤ D 0 j) (ρ 0 j l)

  surj : ∀ i, Function.Surjective (MvPolynomial.eval₂Hom (cst (Y 0).hom (D 0 i)) (ρ 0 i))

variable {R : Type} [CommRing R] {I : Ideal R}
  {Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))}
  {β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left} {n : ℕ}

def towerIdeal (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (e : ℕ) (J : Ideal R)
    (V : (Y e).left.Opens) : Ideal Γ((Y e).left, V) :=
  J.map (cst ((Y e).hom ≫ thick R I e) V)

def Charts.ev (C : Charts I Y β n) (e : ℕ) (i : Fin (n + 1)) :
    MvPolynomial (Fin (n + 1)) R →+* Γ((Y e).left, C.D e i) :=
  MvPolynomial.eval₂Hom (cst ((Y e).hom ≫ thick R I e) (C.D e i)) (C.ρ e i)

section Projective

open GlobalTheory.ProjSpace
open ReciprocityTheory.ChartRestriction.G.Semi (LB)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (PSpace)


end Projective

end GlobalTheory.FormalAlg
