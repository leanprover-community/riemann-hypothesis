module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianPartBaseChange
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.abelian_part_base_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (L L' : Type) [Field L] [Field L'] (z : Sp L ⟶ S) (P : AbPart t z) (e : L →+* L'), ∃ (P' : AbPart t (spMap e ≫ z)) (mK : SABMap P'.tK P.tK (spMap e)) (mB : SABMap P'.tB P.tB (spMap e)), mK.φ ≫ P.m.φ = P'.m.φ ∧ mK.φ ≫ (P.τ.q ≫ P.e.hom).left = (P'.τ.q ≫ P'.e.hom).left ≫ mB.φ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.AbPartFieldChange.exists_baseChange | exact GlobalTheory.CompanionTheory.Ar.AbPartFieldChange.exists_baseChange | (intros; apply GlobalTheory.CompanionTheory.Ar.AbPartFieldChange.exists_baseChange <;> assumption)
