module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel
public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ExistsObjMapOfPIsogenyPullback
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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

theorem _root_.GlobalTheory.T.exists_objMap_of_p_isogeny_pullback : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (c : ℕ) (T Y : Scheme.{0}) (s₁ : T ⟶ Sp R) (s : Y ⟶ Sp R) (t : T ⟶ Y) (o₁ o₁' : Obj b N s₁) (o o' : Obj b N s) (m : ObjMap o₁ o t) (ψ₁ : o₁.A ⟶ o₁'.A) (ψ : o.A ⟶ o'.A) (θ : o₁'.A.left ⟶ o'.A.left), IsUnit ((p : ℕ) : R) → IsPIsog c o₁ o₁' ψ₁ → IsPIsog c o o' ψ → IsGrpPullback o₁'.A o'.A t θ → m.φ ≫ ψ.left = ψ₁.left ≫ θ → ∃ m' : ObjMap o₁' o' t, m'.φ = θ := by
  first | exact @UpperTheory.Cb.exists_objMap_of_p_isogeny_pullback | exact UpperTheory.Cb.exists_objMap_of_p_isogeny_pullback
