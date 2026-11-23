module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.StLocB
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

private noncomputable def densPhi {n : ℕ} (t : ℂ) (z : Fin n → ℂˣ) (p : Fin n × Fin n) : ℂ :=
  (1 - (z p.1 : ℂ) / (z p.2 : ℂ)) / (1 - t * ((z p.1 : ℂ) / (z p.2 : ℂ)))

private lemma half_inv_eq {n : ℕ} (t : ℂ) (z : Fin n → ℂˣ) :
    half t z⁻¹ = ∏ p ∈ (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.2 < p.1), densPhi t z p := by
  unfold half
  refine Finset.prod_nbij' Prod.swap Prod.swap ?_ ?_ ?_ ?_ ?_
  · intro p hp
    simpa using hp
  · intro p hp
    simpa using hp
  · intro p _
    simp
  · intro p _
    simp
  · intro p _
    have h : (((z⁻¹) p.1 : ℂˣ) : ℂ) / (((z⁻¹) p.2 : ℂˣ) : ℂ) = (z p.2 : ℂ) / (z p.1 : ℂ) := by
      simp only [Pi.inv_apply, Units.val_inv_eq_inv_val]
      rw [inv_div_inv]
    simp only [densPhi, Prod.fst_swap, Prod.snd_swap, h]

private lemma dens_eq {n : ℕ} (t : ℂ) (z : Fin n → ℂˣ) :
    dens t z = ∏ p ∈ (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 ≠ p.2), densPhi t z p := by
  have h3 : (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 ≠ p.2) =
      prs n ∪ (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.2 < p.1) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, prs]
    exact ⟨fun h => lt_or_gt_of_ne h, fun h => h.elim (fun h => h.ne) (fun h => h.ne')⟩
  have hd : Disjoint (prs n) ((Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.2 < p.1)) := by
    rw [Finset.disjoint_left]
    intro p hp hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, prs] at hp hq
    exact lt_asymm hp hq
  rw [h3, Finset.prod_union hd, ← half_inv_eq]
  rfl

theorem UpperTheory.Gal.Gen.densSymm :
    UpperTheory.Gal.Gen.DensSymm := by
  intro n t z σ
  rw [dens_eq, dens_eq]
  refine Finset.prod_nbij' (Prod.map σ σ) (Prod.map σ.symm σ.symm) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    simpa using hp
  · intro p hp
    simpa using hp
  · rintro ⟨a, b⟩ _
    simp
  · rintro ⟨a, b⟩ _
    simp
  · intro p _
    rfl
