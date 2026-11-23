module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtAbelianVarietyHomDescent
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

theorem _root_.GlobalTheory.T.exists_finiteExt_abelianVarietyHom_descent : ∀ (K Ω : Type) [Field K] [CharZero K] [Field Ω] (ga : K →+* Ω) (A A' : Over (Sp K)) [GrpObj A] [GrpObj A'], IsAbelianScheme A → IsAbelianScheme A' → ∀ f : (Over.pullback (spMap ga)).obj A ⟶ (Over.pullback (spMap ga)).obj A', IsMonHom f → ∃ (K' : Type) (_ : Field K') (io : K →+* K') (Ω' : Type) (_ : Field Ω') (j : Ω →+* Ω') (l : K' →+* Ω') (f' : (Over.pullback (spMap io)).obj A ⟶ (Over.pullback (spMap io)).obj A'), io.Finite ∧ l.comp io = j.comp ga ∧ IsMonHom f' ∧ ∀ (Z : Scheme.{0}) (p : Z ⟶ pullback A.hom (spMap ga)) (p' : Z ⟶ pullback A.hom (spMap io)) (t : Z ⟶ Sp Ω'), p ≫ pullback.fst _ _ = p' ≫ pullback.fst _ _ → p ≫ pullback.snd _ _ = t ≫ spMap j → p' ≫ pullback.snd _ _ = t ≫ spMap l → p ≫ f.left ≫ pullback.fst _ _ = p' ≫ f'.left ≫ pullback.fst _ _ := by
  first | exact @GlobalTheory.HomFinExt.exists_finite_hom | exact GlobalTheory.HomFinExt.exists_finite_hom | (intros; apply GlobalTheory.HomFinExt.exists_finite_hom <;> assumption)
