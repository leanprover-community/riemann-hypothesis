module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsFramedPointOfLieEigenbasis
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT


theorem _root_.GlobalTheory.T.exists_framedPoint_of_lie_eigenbasis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (x : Sp K ⟶ Xo.X) (Φ : FibKey Xo K x) (e : (Σ b : E →+* ℂ, Fin (Dw.mult b)) ≃ Fin Φ.T.g) (U : Matrix (Fin Φ.T.g) (Fin Φ.T.g) K) (w : Fin Φ.T.g → (epsR K ⟶ Φ.T.t.G)), x ≫ Xo.s = sOf c K → U.det ≠ 0 → (∀ k, IsLieComb (U k) Φ.v (w k)) → (∀ τ i, IsEigAt c τ ((w (e ⟨τ, i⟩)).left ≫ Φ.m.φ)) → ∃ y : FrPt Xo c K, y.x = x ∧ SecTie Φ.m Φ.th y.s ∧ ∀ τ i, y.u τ i = (w (e ⟨τ, i⟩)).left ≫ Φ.m.φ := by
  first | exact @GlobalTheory.LamT.exists_frPt_of_eigenbasis | exact GlobalTheory.LamT.exists_frPt_of_eigenbasis | (intros; apply GlobalTheory.LamT.exists_frPt_of_eigenbasis <;> assumption)
