module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.IsCoordA
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical

namespace UpperTheory.Gal.W2

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G)

abbrev Loc (G : HTGroup p) : Type := (w : Fin G.m) → Fin G.n → G.Fw w

def IntL (z : Loc G) : Prop := ∀ w i, ‖(z w i : PadicAlgCl p)‖ ≤ 1

def pairL (a b : Loc G) : ℚ_[p] := ∑ w, Algebra.trace ℚ_[p] (G.Fw w) (a w ⬝ᵥ b w)

structure PFrame (β : G.Cˣ) where
  T : VQ D →+ Loc G
  T' : VQ D →+ Loc G
  act : ∀ (c : G.C) x w, T (L.rep c x) w = G.rho w c *ᵥ T x w
  act' : ∀ (c : G.C) x w, T' (L.rep c x) w = (G.rho w ((β : G.C) * sh G c * ((β⁻¹ : G.Cˣ) : G.C)))ᵀ *ᵥ T' x w
  form : ∀ u x, ((formB L β u x : ℚ) : ℚ_[p]) = pairL (T' x) (T u) - pairL (T' u) (T x)
  dense : ∀ (a b : Loc G) (k : ℕ), ∃ x a' b', IntL a' ∧ IntL b' ∧ T x = a + p ^ k • a' ∧ T' x = b + p ^ k • b'
  bound : ∃ (s : Finset (VQ D)) (k : ℕ), Submodule.span ℚ (s : Set (VQ D)) = ⊤ ∧
    ∀ x, IntL (T x) → IntL (T' x) → ∃ m : ℕ, m.Coprime p ∧ (m * p ^ k) • x ∈ AddSubgroup.closure (s : Set (VQ D))

variable {L}

def PFrame.Mem {β : G.Cˣ} (A : PFrame L β) (g : Gp G) (x : VQ D) : Prop :=
  IntL (fun w => (((g.2 w)⁻¹ : GL (Fin G.n) (G.Fw w)) : Matrix (Fin G.n) (Fin G.n) (G.Fw w)) *ᵥ A.T x w) ∧
    ∀ z : Loc G, IntL z → ‖((g.1⁻¹ : ℚ_[p]ˣ) : ℚ_[p]) * pairL (A.T' x) (fun w => (g.2 w : Matrix (Fin G.n) (Fin G.n) (G.Fw w)) *ᵥ z w)‖ ≤ 1

def IntPt (g : Gp G) : Prop :=
  ‖(g.1 : ℚ_[p])‖ = 1 ∧ ∀ w i j, ‖((g.2 w : Matrix (Fin G.n) (Fin G.n) (G.Fw w)) i j : PadicAlgCl p)‖ ≤ 1 ∧
    ‖((((g.2 w)⁻¹ : GL (Fin G.n) (G.Fw w)) : Matrix (Fin G.n) (Fin G.n) (G.Fw w)) i j : PadicAlgCl p)‖ ≤ 1

end UpperTheory.Gal.W2
