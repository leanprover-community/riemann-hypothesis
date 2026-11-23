module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCompletionEqLatticeVectorAddNsmul
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct

namespace GlobalTheory.LKGeo.LiftSys

theorem exists_lift_sys : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (h₀ : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D)), (∀ v ∈ LaHat D, h₀ v ∈ LaHat D) → ∃ h : ℕ → D.La →+ D.La, ∀ n : ℕ, 0 < n → n.Coprime p → ∀ x, ∃ w ∈ LaHat D, h₀ (inAf D x) = inAf D (h n x) + n • w := by
  intro p _ D h₀ hh
  classical
  haveI := D.freeLa
  haveI := D.finLa
  let Ix := Module.Free.ChooseBasisIndex ℤ D.La
  let b : Module.Basis Ix ℤ D.La := Module.Free.chooseBasis ℤ D.La
  let iA : D.La →+ AfP p ⊗[ℚ] VQ D :=
    AddMonoidHom.mk' (inAf D) (fun x y => by simp only [inAf, TensorProduct.tmul_add])
  have hiA : ∀ x, iA x = inAf D x := fun _ => rfl
  have key : ∀ n : ℕ, 0 < n → n.Coprime p → ∀ i : Ix, ∃ (x : D.La) (w : AfP p ⊗[ℚ] VQ D),
      w ∈ LaHat D ∧ h₀ (inAf D (b i)) = inAf D x + n • w := fun n hn hnp i =>
    exists_inAf_add_nsmul_of_mem_laHat p D n hn hnp _ (hh _ (AddSubgroup.subset_closure ⟨1, b i, fun v => by rw [map_one]; exact one_mem _, rfl⟩))
  let h : ℕ → D.La →+ D.La := fun n =>
    if hn : 0 < n ∧ n.Coprime p then
      (b.constr ℤ (fun i => (key n hn.1 hn.2 i).choose)).toAddMonoidHom
    else 0
  refine ⟨h, fun n hn hnp x => ?_⟩
  have hx : x ∈ Submodule.span ℤ (Set.range b) := by rw [b.span_eq]; trivial
  have hh' : h n = (b.constr ℤ (fun i => (key n hn hnp i).choose)).toAddMonoidHom := by
    simp only [h, dif_pos (And.intro hn hnp)]
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    obtain ⟨hw, e⟩ := (key n hn hnp i).choose_spec.choose_spec
    have hbi : h n (b i) = (key n hn hnp i).choose := by
      rw [hh']; simp [Module.Basis.constr_basis]
    refine ⟨_, hw, e.trans ?_⟩
    rw [hbi]
  | zero =>
    refine ⟨0, zero_mem _, ?_⟩
    rw [← hiA, ← hiA, map_zero, map_zero, map_zero, map_zero, smul_zero, add_zero]
  | add y z _ _ hy hz =>
    obtain ⟨w₁, hw₁, e₁⟩ := hy
    obtain ⟨w₂, hw₂, e₂⟩ := hz
    refine ⟨w₁ + w₂, add_mem hw₁ hw₂, ?_⟩
    rw [← hiA, ← hiA, map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), hiA, hiA, hiA, hiA, e₁, e₂, smul_add]
    abel
  | smul c y _ hy =>
    obtain ⟨w, hw, e⟩ := hy
    refine ⟨c • w, zsmul_mem hw c, ?_⟩
    rw [← hiA, ← hiA, map_zsmul, map_zsmul, map_zsmul, hiA, hiA, e, smul_add, smul_comm c (n : ℕ) w]
    rw [← hiA (c • _), map_zsmul, hiA]

end GlobalTheory.LKGeo.LiftSys
