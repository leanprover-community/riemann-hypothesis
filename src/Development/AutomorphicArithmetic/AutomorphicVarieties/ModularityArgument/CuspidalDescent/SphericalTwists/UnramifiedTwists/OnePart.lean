module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.SphericalTwists.RowProps
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CuspRep UpperTheory.V.Af UpperTheory.V.Af.Gu

theorem UpperTheory.V.Z.Desc.W.onePart :
    UpperTheory.V.Z.Desc.W.OnePart := by
  intro hJS hTw E _ _ _ n c hn a d P π had hw
  obtain ⟨s, -⟩ := hJS E (Σ i : Fin c, Fin (d i)) Unit (fun x => a x.1) (fun _ => n)
    (fun x => CG.mk ((P x.1).twist
      (GlobalTheory.HeckeGal.Model.absPow E (-(((x.2 : ℕ) : ℝ) - ((d x.1 : ℝ) - 1) / 2)))))
    (fun _ => CG.mk π) (fun x => (had x.1).1) (fun _ => hn)
    (hw.mono fun w ⟨S, h1, h2⟩ => ⟨_, fun _ => satTot w d S, fun x => hTw E _ _ _ w _ (h1 x.1), fun _ => h2, by
      simp only [neg_neg, Finset.univ_unique, Finset.sum_singleton, satTot]
      exact Fintype.sum_sigma _⟩)
  have hc : ∑ i, d i = 1 := by simpa using Fintype.card_congr s
  have hle : c ≤ ∑ i, d i := by
    simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ => (had i).2)
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hc
  refine ⟨by omega, fun i => le_antisymm ?_ (had i).2⟩
  rw [← hc]
  exact Finset.single_le_sum (f := d) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
