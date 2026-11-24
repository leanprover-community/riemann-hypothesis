module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Formalism.LocalToGlobal.CMDeterminantIdeals.DetIdeal

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.CM

theorem hasType_of_iso : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (G G' : Over (Sp R)) [GrpObj G] [GrpObj G'] (a : OAct (𝓞 E) G) (a' : OAct (𝓞 E) G') (e : G ≅ G') (ρ : R) (p q : ℕ), Serre.IsLinearHom a a' e.hom → HasType H a' ρ p q → HasType H a ρ p q := by
  intro E _ _ _ H R _ G G' _ _ a a' e ρ p q he h k _ _ β hβ τ
  have := he.isMonHom
  have key : ∀ n, LieMult a (spMap β) τ n ↔ LieMult a' (spMap β) τ n := fun n => by
    have := LiePull.lieMult_pull _ _ _ G' G (𝟙 _) e.hom.left a' a (isGrpPullback_of_iso e)
      (fun c => congrArg (fun z => z.left) (he.comm c)) k (spMap β) τ n
    rwa [Category.comp_id] at this
  rw [key, key]
  exact h k β hβ τ

end GlobalTheory.CM
