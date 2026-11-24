module

public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ProjSpace

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.EtProj

variable {R : Type} [CommRing R] {X : Scheme.{0}} {N : ℕ} (ι : X ⟶ PSpace R N)

def fOpen (g : MvPolynomial (Fin (N + 1)) R) : X.Opens := ι ⁻¹ᵁ Proj.basicOpen (grading R N) g

def fRatio {n : ℕ} (f g : MvPolynomial (Fin (N + 1)) R) (hf : f ∈ grading R N n) (hg : g ∈ grading R N n) :
    Γ(X, fOpen ι g) :=
  (ι.app (Proj.basicOpen (grading R N) g)).hom (GlobalTheory.ProjFrac.frac (grading R N) _ f g hf hg le_rfl)

theorem fRatio_self {n : ℕ} (g : MvPolynomial (Fin (N + 1)) R) (hg : g ∈ grading R N n) :
    fRatio ι g g hg hg = 1 := by
  unfold fRatio
  rw [GlobalTheory.ProjFrac.frac_self]
  exact map_one _

theorem mem_fOpen (g : MvPolynomial (Fin (N + 1)) R) (z : X) :
    z ∈ fOpen ι g ↔ g ∉ (ι.base z).asHomogeneousIdeal := Iff.rfl

end GlobalTheory.EtProj
