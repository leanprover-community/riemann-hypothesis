module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsConstMul
public import Formalism.LocalToGlobal.ProjectiveLattices.IsCombAt
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FramePointVectors
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
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsLineGenOn

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

theorem _root_.GlobalTheory.T.frame_point_vectors : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (τ : E →+* ℂ) (S : Type) [CommRing S] [Algebra c.F S] (z : Formalism.L2.Pj.FrPt Xo c S) (F : Type) [Field F] (ψ : S →+* F) (y : Sp F ⟶ Xo.XF c) (hp : D.mult τ = D.p) (hq : D.mult (ComplexEmbedding.conjugate τ) = D.q), under y = spMap ψ ≫ z.x → y ≫ pullback.snd _ _ = spMap (ψ.comp (algebraMap c.F S)) → ∃ (v : Vecs y D.p) (w : Vecs y D.q), (∀ i, (v i).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u τ (i.cast hp.symm)) ∧ (∀ j, (w j).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u (ComplexEmbedding.conjugate τ) (j.cast hq.symm)) ∧ ∀ U : Set (Xo.XF c), Set.range y ⊆ U → IsFramed U τ (ψ.comp (algebraMap c.F S)) y v w := by
  exact @GlobalTheory.CompanionTheory.Ar.FrameEig.isFramed_frPt
