module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.AffGlue

structure Data (T : Scheme.{0}) where

  M : ∀ V : T.Opens, IsAffineOpen V → Type

  grp : ∀ V hV, AddCommGroup (M V hV)

  mod : ∀ V hV, Module Γ(T, V) (M V hV)

  ρ : ∀ {V V' : T.Opens} (hV : IsAffineOpen V) (hV' : IsAffineOpen V'), V' ≤ V → M V hV →+ M V' hV'
  ρ_smul : ∀ {V V' : T.Opens} (hV : IsAffineOpen V) (hV' : IsAffineOpen V') (h : V' ≤ V)
    (a : Γ(T, V)) (m : M V hV), ρ hV hV' h (a • m) = resG T h a • ρ hV hV' h m
  ρ_self : ∀ {V : T.Opens} (hV : IsAffineOpen V) (h : V ≤ V) (m : M V hV), ρ hV hV h m = m
  ρ_ρ : ∀ {V V' V'' : T.Opens} (hV : IsAffineOpen V) (hV' : IsAffineOpen V')
    (hV'' : IsAffineOpen V'') (h : V' ≤ V) (h' : V'' ≤ V') (m : M V hV),
    ρ hV' hV'' h' (ρ hV hV' h m) = ρ hV hV'' (h'.trans h) m

  loc_surj : ∀ {V : T.Opens} (hV : IsAffineOpen V) (f : Γ(T, V)) (hD : IsAffineOpen (T.basicOpen f))
    (m : M (T.basicOpen f) hD), ∃ (n : ℕ) (x : M V hV),
      resG T (T.basicOpen_le f) f ^ n • m = ρ hV hD (T.basicOpen_le f) x

  loc_inj : ∀ {V : T.Opens} (hV : IsAffineOpen V) (f : Γ(T, V)) (hD : IsAffineOpen (T.basicOpen f))
    (x : M V hV), ρ hV hD (T.basicOpen_le f) x = 0 → ∃ n : ℕ, f ^ n • x = 0

attribute [instance] Data.grp Data.mod

variable {T : Scheme.{0}} (D : Data T)

variable {D}

end GlobalTheory.AffGlue
