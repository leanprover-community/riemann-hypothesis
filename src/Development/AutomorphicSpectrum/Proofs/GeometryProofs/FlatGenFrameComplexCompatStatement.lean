module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsConstMul
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatGenFrameComplexCompat
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

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

theorem _root_.GlobalTheory.T.flat_gen_frame_complex_compat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ φ₀ : FrameFn Xo c) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n), IsTypeFn H D.p D.q ty → IsFlatGen U τ φ FU i → IsFlatGen U τ φ₀ FU i → (∀ y : Sp ℂ ⟶ Xo.XF c, y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) → Set.range y ⊆ U → ∃ P, IsPeriod (FU.Di i) ty P ∧ under y = FU.u i P) → ∃ a : c.F, a ≠ 0 ∧ ∀ (F : Type) [Field F] (β : c.F →+* F) y v w, IsFramed U τ β y v w → φ F y v w = β a * φ₀ F y v w := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.flatGen_unique | exact GlobalTheory.CompanionTheory.Ar.Flat.flatGen_unique | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.flatGen_unique <;> assumption)
