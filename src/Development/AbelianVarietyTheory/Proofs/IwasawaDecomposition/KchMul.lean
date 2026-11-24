module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.LamT

namespace GlobalTheory.KeyFourth

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

def Tied {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (s : LB.Sec (PPx x)) (u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left))
    (Φ : FibKey Xo S x) : Prop :=
  SecTie Φ.m Φ.th s ∧ ∃ hg : Φ.T.g = g, ∀ i : Fin Φ.T.g,
    (Φ.v i).left ≫ Φ.m.φ = u (e (i.cast hg)).1 (e (i.cast hg)).2

def kch {S : Type} [CommRing S] (t : Ix Dw → Sˣ) : Sˣ := ∏ i, t i ^ keyEx Dw i

theorem kch_mul {S : Type} [CommRing S] (t t' : Ix Dw → Sˣ) : kch (t * t') = kch t * kch t' := by
  simp only [kch, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]

theorem kch_inv {S : Type} [CommRing S] (t : Ix Dw → Sˣ) : kch t⁻¹ = (kch t)⁻¹ := by
  simp only [kch, Pi.inv_apply, inv_zpow, Finset.prod_inv_distrib]

theorem kch_eq {S : Type} [CommRing S] (t : Ix Dw → Sˣ) :
    kch t = (∏ x : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), t (some x)) * (t none ^ 2)⁻¹ := by
  rw [kch, Fintype.prod_option, mul_comm]
  simp only [keyEx, zpow_one, zpow_neg]
  rfl

def RootVal {σ : c.F →+* ℂ} {r : ℕ} (U : Formalism.L2.PjFree.Unf Xo c σ r) (y : FrPt Xo c (CAt σ)) (v : ℂ) : Prop :=
  ∃ (k : U.Comp) (x : (U.X k).dom) (t : Ix Dw → (CAt σ)ˣ), FrBor t (U.un k x) y ∧
    v = Formalism.L2.PjFree.toC ((kch t : (CAt σ)ˣ) : CAt σ)

end GlobalTheory.KeyFourth
