module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdeleAwayFromPEqZeroOfDivisibleCoprimeStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.LKGeo.ModZero

theorem repr_isIntAf {p : ℕ} [Fact p.Prime] (D : Datum p) {κ : Type} (b : Module.Basis κ ℤ D.La)
    (u : AfP p ⊗[ℚ] VQ D) (hu : u ∈ LaHat D) (i : κ) :
    IsIntAf ((Algebra.TensorProduct.basis (AfP p) (Algebra.TensorProduct.basis ℚ b)).repr u i) := by
  induction hu using AddSubgroup.closure_induction with
  | mem u hu =>
    obtain ⟨a, x, ha, rfl⟩ := hu
    intro v
    rw [Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply,
      Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul, one_smul,
      eq_intCast (algebraMap ℤ ℚ), map_intCast, map_mul, map_intCast]
    exact mul_mem (ha v) (intCast_mem _ _)
  | zero => intro v; rw [map_zero, Finsupp.zero_apply, map_zero]; exact zero_mem _
  | add u u' _ _ hu hu' => intro v; rw [map_add (f := _), Finsupp.add_apply, map_add (f := _)]; exact add_mem (hu v) (hu' v)
  | neg u _ hu => intro v; rw [map_neg, Finsupp.neg_apply, map_neg]; exact neg_mem (hu v)

end GlobalTheory.LKGeo.ModZero


open GlobalTheory.LKGeo.ModZero in
theorem GlobalTheory.LKGeo.eq_zero_of_forall_nsmul_laHat : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (z : AfP p ⊗[ℚ] VQ D),
    (∀ n : ℕ, 0 < n → n.Coprime p → ∃ w ∈ LaHat D, z = n • w) → z = 0 := by
  intro p _ D z hz
  have := D.freeLa
  have := D.finLa
  let b := Module.Free.chooseBasis ℤ D.La
  let bA := Algebra.TensorProduct.basis (AfP p) (Algebra.TensorProduct.basis ℚ b)
  refine bA.ext_elem fun i => ?_
  rw [map_zero, Finsupp.zero_apply]
  refine GlobalTheory.T.finiteAdeleAwayFromP_eq_zero_of_divisible_coprime p (bA.repr z i) fun n hn hc => ?_
  obtain ⟨w, hw, rfl⟩ := hz n hn hc
  exact ⟨bA.repr w i, repr_isIntAf D b w hw i, by rw [map_nsmul, Finsupp.smul_apply]⟩
