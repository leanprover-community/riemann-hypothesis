module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.OrdReadOf
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
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.resClosed_of :
    ResClosed := by
  intro V _ _ _ _
  refine IsAlgClosed.of_exists_root _ ?_
  intro p hm hirr
  have hsurj : Function.Surjective (IsLocalRing.residue V) := IsLocalRing.residue_surjective
  have hl : p ∈ Polynomial.lifts (IsLocalRing.residue V) :=
    Polynomial.mem_lifts _ |>.2 (Polynomial.map_surjective _ hsurj p)
  obtain ⟨P, hP, hdeg, hPm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl hm
  have hinj : Function.Injective (algebraMap V (FractionRing V)) :=
    IsFractionRing.injective V (FractionRing V)
  have hpos : 0 < P.natDegree := hdeg ▸ hirr.natDegree_pos
  have hd : (P.map (algebraMap V (FractionRing V))).degree ≠ 0 := by
    rw [Polynomial.degree_map_eq_of_injective hinj]
    exact (Polynomial.natDegree_pos_iff_degree_pos.1 hpos).ne'
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root _ hd
  have hint : IsIntegral V x := by
    refine ⟨P, hPm, ?_⟩
    simpa [Polynomial.IsRoot.def, Polynomial.eval_map] using hx
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  have hy : P.eval y = 0 := by
    apply hinj
    rw [map_zero, ← Polynomial.eval₂_at_apply, ← Polynomial.eval_map]
    exact hx
  refine ⟨IsLocalRing.residue V y, ?_⟩
  rw [← hP, Polynomial.eval_map, Polynomial.eval₂_at_apply, hy, map_zero]
