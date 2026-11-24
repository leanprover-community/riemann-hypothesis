module

public import Development.EtaleCohomology.EtaleTrace.LadicH0LocallyConstant
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

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LateralTheory.EtaleTrace.LPdCut

def Dp (k : Type) [Field k] (N : ℕ) (i : Fin (N + 1)) : (PN k N).Opens :=
  Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i)

def LChart : Prop := ∀ (k : Type) [Field k] (N : ℕ) (i : Fin (N + 1)),
  ∃ j : Spec (CommRingCat.of (MvPolynomial (Fin N) k)) ⟶ PN k N, IsOpenImmersion j ∧
    j ≫ PNto k N = Spec.map (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial (Fin N) k)) ∧
    Set.range j = (Dp k N i : Set (PN k N))

def LProper : Prop := ∀ (k : Type) [Field k] (N : ℕ), IsProper (PNto k N)

def LSmooth : Prop := ∀ (k : Type) [Field k] (N : ℕ), SmoothOfRelativeDimension N (PNto k N)

def LEmpty : Prop := A5 → A9 → ∀ (R : Type) [CommRing R] (X : Scheme.{0}), IsEmpty X → ∀ (F : Shv R) (n : ℤ),
  Subsingleton (H R (sch.obj X) F n)

theorem unit_of {k : Type} [Field k] {X : Scheme.{0}} (p : X ⟶ S k) {q : ℕ} (h : IsUnit (q : k)) : IsUnit (q : Γ(X, ⊤)) := by
  simpa using (h.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom).map p.appTop.hom

end LateralTheory.EtaleTrace.LPdCut

end
