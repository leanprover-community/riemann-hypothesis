module

public import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyDieudonneIntegralityFactorisation
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

open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.AV GlobalTheory.AV.AbVar
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.abelianVariety_dieudonne_integrality_factorisation : ∀ (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k] [CharP k p] [PerfectRing k p] (A B : AbVar k) (G H : PDivGroup p k) (t : G.TorsionTower A.X) (t' : H.TorsionTower B.X) (f : A ⟶ B), (∀ n : ℕ, (∀ m, ∃ m', T.map (t.map t' f.hom) m = p ^ n • m') → ∃ f' : A ⟶ B, f = p ^ n • f') ∧ (IsIsogeny f → IsIsog (t.map t' f.hom) ∧ Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map (t.map t' f.hom))) = padicValNat p (deg f)) ∧ ∀ (C : AbVar k) (K : PDivGroup p k) (t'' : K.TorsionTower C.X) (g : A ⟶ C) (e : ℕ), IsIsogeny f → deg f = p ^ e → LinearMap.range (T.map (t.map t'' g.hom)) ≤ LinearMap.range (T.map (t.map t' f.hom)) → ∃ u : B ⟶ C, f ≫ u = g := by
  first | (exact @GlobalTheory.Dieu.AbVarDieu.abVar_dieudonne_integral_length_factor) | (exact GlobalTheory.Dieu.AbVarDieu.abVar_dieudonne_integral_length_factor) | (intros; apply GlobalTheory.Dieu.AbVarDieu.abVar_dieudonne_integral_length_factor  <;> assumption)
