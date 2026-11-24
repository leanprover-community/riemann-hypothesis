module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

namespace GlobalTheory.CompanionTheory.StdCompat

theorem sum_castLE_eq_sum_filter {s : ℕ} (f : Fin s → ℕ) (c : Fin s) :
    ∑ b : Fin (c : ℕ), f (Fin.castLE c.2.le b) = ∑ j ∈ Finset.univ.filter (· < c), f j := by
  refine Finset.sum_bij (fun b _ => Fin.castLE c.2.le b) ?_ ?_ ?_ ?_
  · intro b _
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, b.2⟩
  · intro x _ y _ h
    exact Fin.castLE_injective _ h
  · intro j hj
    have hj' : (j : ℕ) < c := (Finset.mem_filter.1 hj).2
    exact ⟨⟨j, hj'⟩, Finset.mem_univ _, Fin.ext rfl⟩
  · intro _ _
    rfl

theorem partial_sum_drop_empty {r r' : ℕ} (d : Fin r → ℕ) (o : Fin r' → Fin r)
    (ho : StrictMono o) (hr : ∀ j, d j ≠ 0 → j ∈ Set.range o) (a : Fin r') :
    ∑ b ∈ Finset.univ.filter (· < a), d (o b) = ∑ j ∈ Finset.univ.filter (· < o a), d j := by
  rw [← Finset.sum_image (s := Finset.univ.filter (· < a)) (g := o) (f := d)
    (fun x _ y _ h => ho.injective h)]
  refine Finset.sum_subset ?_ ?_
  · intro j hj
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hj
    have hb' : b < a := (Finset.mem_filter.1 hb).2
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, ho hb'⟩
  · intro j hj hj'
    by_contra hne
    obtain ⟨b, rfl⟩ := hr j hne
    have hlt : o b < o a := (Finset.mem_filter.1 hj).2
    exact hj' (Finset.mem_image.2
      ⟨b, Finset.mem_filter.2 ⟨Finset.mem_univ _, ho.lt_iff_lt.1 hlt⟩, rfl⟩)

theorem stdBlocks_drop_empty : ∀ {r r' N : ℕ} (d : Fin r → ℕ) (hd : ∑ a, d a = N)
    (o : Fin r' → Fin r), StrictMono o → (∀ j, d j ≠ 0 → j ∈ Set.range o) →
    ∀ (hd' : ∑ a, d (o a) = N) (a : Fin r') (t : Fin (d (o a))),
      stdBlocks (fun a => d (o a)) hd' ⟨a, t⟩ = stdBlocks d hd ⟨o a, t⟩ := by
  intro r r' N d hd o ho hr hd' a t
  apply Fin.ext
  have h1 := stdBlocks_val (fun a => d (o a)) hd' a t
  have h2 := stdBlocks_val d hd (o a) t
  have h3 := sum_castLE_eq_sum_filter (fun a => d (o a)) a
  have h4 := sum_castLE_eq_sum_filter d (o a)
  have h5 := partial_sum_drop_empty d o ho hr a
  rw [h1, h2]
  rw [h3, h4, h5]

end GlobalTheory.CompanionTheory.StdCompat
