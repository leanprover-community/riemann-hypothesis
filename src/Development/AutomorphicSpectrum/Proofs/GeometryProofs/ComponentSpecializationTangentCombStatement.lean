module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsValFam
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentSpecializationTangentComb
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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat
open GlobalTheory.CompanionTheory.Ar.Flat.Rep

theorem _root_.GlobalTheory.T.component_specialization_tangent_comb : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (F : Type) [Field F] (y : Sp F ⟶ Xo.XF c) (n : ℕ) (b : Fin n → Z.V) (v : Vecs y n) (s : Fin n → Z.Ω) (r : Fin n → F) (w : epsAt (under y) ⟶ Xo.univ.t.G), genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j) → IsValFam Z y b v → (∀ j, ValAt (Z.ξ₀ ≫ Y.j) (y ≫ Y.j) (s j) (r j)) → IsComb r v w → ∃ w', Z.M.ValAt (y ≫ Y.j) (∑ j, s j • b j) w' ∧ SameVec Y y w w' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.Rep.valFam_sum_comb | exact GlobalTheory.CompanionTheory.Ar.Flat.Rep.valFam_sum_comb | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.Rep.valFam_sum_comb <;> assumption)
