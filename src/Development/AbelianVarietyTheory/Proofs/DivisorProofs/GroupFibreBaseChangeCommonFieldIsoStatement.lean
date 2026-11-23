module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupFibreBaseChangeCommonFieldIso
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.groupFibre_baseChange_common_field_iso : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (W' : Type) [CommRing W'] [IsLocalRing W'] (G' : Over (Sp W')) [GrpObj G'] (ξ' : Sp W' ⟶ S) (β : G'.left ⟶ G.left), IsGrpPullback G' G ξ' β → ∀ (k : Type) [Field k] (Y : Over (Sp k)) [GrpObj Y] (κ' : k →+* ResidueField W') (e' : (Over.pullback (spMap (residue W'))).obj G' ≅ (Over.pullback (spMap κ')).obj Y), IsMonHom e'.hom → ∀ (Ω : Type) [Field Ω] (x : Sp Ω ⟶ S) (κ : k →+* Ω) (Ω' : Type) [Field Ω'] (io : Ω →+* Ω') (i₂ : ResidueField W' →+* Ω'), spMap io ≫ x = spMap i₂ ≫ spMap (residue W') ≫ ξ' → io.comp κ = i₂.comp κ' → ∃ (e : (Over.pullback (spMap io ≫ x)).obj G ≅ (Over.pullback (spMap (io.comp κ))).obj Y) (τ : ((Over.pullback (spMap io ≫ x)).obj G).left ⟶ ((Over.pullback (spMap (residue W'))).obj G').left), IsMonHom e.hom ∧ τ ≫ pullback.fst G'.hom (spMap (residue W')) ≫ β = pullback.fst G.hom (spMap io ≫ x) ∧ e.hom.left ≫ pullback.fst Y.hom (spMap (io.comp κ)) = τ ≫ e'.hom.left ≫ pullback.fst Y.hom (spMap κ') := by
  first | exact @GlobalTheory.Mum.FibBC.fibre_baseChange | exact GlobalTheory.Mum.FibBC.fibre_baseChange | (intros; apply GlobalTheory.Mum.FibBC.fibre_baseChange <;> assumption)
