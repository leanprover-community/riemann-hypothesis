module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.VectorsAtComplexPoint
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

theorem _root_.GlobalTheory.T.vectors_at_complex_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (τ : E →+* ℂ) (σ : c.F →+* ℂ) (y : Sp ℂ ⟶ Xo.XF c) (v : Vecs y D.p) (w : Vecs y D.q) (v₀ : Fin D.p → (epsAt (y ≫ Y.j) ⟶ Y.t.G)) (w₀ : Fin D.q → (epsAt (y ≫ Y.j) ⟶ Y.t.G)), y ≫ pullback.snd _ _ = spMap σ → (∀ i, SameVec Y y (v i) (v₀ i)) → (∀ j, SameVec Y y (w j) (w₀ j)) → IsEigFrame Y.t.act (y ≫ Y.j) (σ.comp (tauIn c τ)) v₀ → IsEigFrame Y.t.act (y ≫ Y.j) (σ.comp (tauIn c (ComplexEmbedding.conjugate τ))) w₀ → IsFramed Set.univ τ σ y v w := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.isFramed_of_model | exact GlobalTheory.CompanionTheory.Ar.Flat.isFramed_of_model | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.isFramed_of_model <;> assumption)
