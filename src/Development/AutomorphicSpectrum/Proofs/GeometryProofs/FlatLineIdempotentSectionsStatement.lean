module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import Formalism.LocalToGlobal.ProjectiveLattices.IsCombAt
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatLineIdempotentSections
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

theorem _root_.GlobalTheory.T.flat_line_idempotent_sections : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (Z : CptOver Y U) (φ : FrameFn Xo c), τ (H.rt : E) = H.rt0 → IsClopen U → IsLineFn U τ φ → FlatOnModel Z τ φ → ∃ s s' e : Formalism.L2.Pj.Rul Xo c, e ∈ Formalism.L2.Pj.sec Xo c 0 0 ∧ s * s' = e ∧ s * e = s ∧ s' * e = s' ∧ (∀ (a a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Formalism.L2.Pj.Rul Xo c), (∀ x : (E →+* ℂ) × ℕ, x.2 < D.mult x.1 → (a' x : ℤ) = a x + Set.indicator {x : (E →+* ℂ) × ℕ | x.1 = ComplexEmbedding.conjugate τ} 1 x - Set.indicator {x : (E →+* ℂ) × ℕ | x.1 = τ} 1 x) → (f ∈ Formalism.L2.Pj.sec Xo c a n → f * s ∈ Formalism.L2.Pj.sec Xo c a' n) ∧ (f ∈ Formalism.L2.Pj.sec Xo c a' n → f * s' ∈ Formalism.L2.Pj.sec Xo c a n)) ∧ ∀ (p : Formalism.L2.Pj.TRing c.F) (z : Formalism.L2.Pj.FrPt Xo c p.R) (F : Type) [Field F] (ψ : p.R →+* F) (y : Sp F ⟶ Xo.XF c), under y = spMap ψ ≫ z.x → y ≫ pullback.snd _ _ = spMap (ψ.comp (algebraMap c.F p.R)) → (¬ Set.range y ⊆ U → ψ (e p z) = 0) ∧ (Set.range y ⊆ U → ψ (e p z) = 1 ∧ ∀ (v : Vecs y D.p) (w : Vecs y D.q) (hp : D.mult τ = D.p) (hq : D.mult (ComplexEmbedding.conjugate τ) = D.q), (∀ i, (v i).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u τ (i.cast hp.symm)) → (∀ j, (w j).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u (ComplexEmbedding.conjugate τ) (j.cast hq.symm)) → ψ (s p z) = φ F y v w) := by
  exact @GlobalTheory.CompanionTheory.Ar.Flat.exists_flat_rule
