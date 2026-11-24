module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfTransl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBirigidifiedBundleOfDescent
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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

theorem _root_.GlobalTheory.T.exists_birigidified_bundle_of_descent : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (M : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b M s) (A' : Over S) [GrpObj A'] [IsCommMonObj A'] (ψ : o.A ⟶ A'), IsMonHom ψ → ∀ (m : ℕ) (P₀ : LB (G2 A').left), P₀.IsLB → LBIso (GlobalTheory.UPel.HT.Hecke.lbPow o.P m) (P₀.pull (GlobalTheory.UPel.HT.Hecke.sq2 ψ)) → ∃ P' : LB (G2 A').left, P'.IsLB ∧ (∃ t : (P'.pull (lift (1 : A' ⟶ A') (𝟙 A')).left).Gen, t.IsGen) ∧ (∃ t : (P'.pull (lift (𝟙 A') (1 : A' ⟶ A')).left).Gen, t.IsGen) ∧ LBIso (GlobalTheory.UPel.HT.Hecke.lbPow o.P m) (P'.pull (GlobalTheory.UPel.HT.Hecke.sq2 ψ)) := by
  first | (exact @GlobalTheory.UPel.HT.Hecke.exists_birigidified_of_descent) | (exact GlobalTheory.UPel.HT.Hecke.exists_birigidified_of_descent) | (intros; apply GlobalTheory.UPel.HT.Hecke.exists_birigidified_of_descent  <;> assumption)
