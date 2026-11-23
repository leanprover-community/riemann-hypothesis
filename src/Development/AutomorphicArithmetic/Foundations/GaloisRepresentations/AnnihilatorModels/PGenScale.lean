module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.GenericScale
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LiftMap
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp TensorProduct Module
open UpperTheory.Gal.crystallineComparison

private theorem prod_map_scale (z : ℂ) (s : Multiset ℂˣ) :
    (s.map fun b : ℂˣ => z * (b : ℂ)).prod = z ^ s.card * ((s.prod : ℂˣ) : ℂ) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, ih, Units.val_mul, pow_succ]
    ring

private theorem lift_map {α β : Type} (f : α → β) (B : Multiset α) (t : Multiset β)
    (h : ∀ x ∈ t, x ∈ B.map f) : ∃ t' : Multiset α, t'.map f = t ∧ ∀ x ∈ t', x ∈ B :=
  _root_.UpperTheory.Reformulated.B.Qk56.lift_map f B t h

private theorem generic_scale_units (B : Multiset ℂˣ) (z : ℂ) (hz : z ≠ 0) (hB : GenericMul B) :
    GenericMul (B.map fun b : ℂˣ => z * (b : ℂ)) := by
  intro t hc hm hp
  obtain ⟨t', rfl, h2⟩ := lift_map (fun b : ℂˣ => z * (b : ℂ)) B t hm
  have hcard : t'.card = B.card := by simpa using hc
  rw [prod_map_scale, prod_map_scale, hcard] at hp
  have hprod : t'.prod = B.prod :=
    Units.ext (mul_left_cancel₀ (pow_ne_zero _ hz) hp)
  rw [hB t' hcard h2 hprod]

theorem UpperTheory.Gal.crystallineComparison.genScale_of :
    GenericScale := by
  intro B z hz hB
  have h := generic_scale_units B z hz hB
  have e : (do let a ← B; pure (a : ℂ) : Multiset ℂ) = B.map fun b : ℂˣ => (b : ℂ) := by
    simp only [Multiset.bind_def, Multiset.pure_def, Multiset.bind_singleton]
  rw [e, Multiset.map_map]
  exact h
