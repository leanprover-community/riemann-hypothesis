module

public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DominantIwahoriCosetRepsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeOperatorCosetSumStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

namespace GlobalTheory.CompanionTheory.Lbc

theorem hecke_dominant_mul : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], PositivityTheory.Lbc.C1 k := by
  intro k _ _ _ _ N h d hd J hJo hJc hIw hpos V _ _ π hπ t t' ht ht' T T' hT hT' v l hl
  obtain ⟨r, hr, x, hxN, hx⟩ := GlobalTheory.T.dominant_iwahori_coset_reps k N h d hd J hJo hJc hIw hpos t' ht'
  have hxJ : ∀ i, x i ∈ J := fun i => (hxN i).1
  have hform := GlobalTheory.T.hecke_operator_coset_sum k N J hJc V π hπ _ T' hT' r x hr hxJ hx v
  have hr0 : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hr.ne'
  set g := leviEmb k (stdBlocks d hd) t with hg
  set g' := leviEmb k (stdBlocks d hd) t' with hg'
  have hmul : leviEmb k (stdBlocks d hd) (t * t') = g * g' := map_mul _ _ _
  have hterm : ∀ i, l (π g (π (x i * g') (v : V))) = l (π (g * g') (v : V)) := by
    intro i
    have hc : g * x i * g⁻¹ ∈ J := (ht.1 _ (hxN i)).1
    have hfac : g * (x i * g') = (g * x i * g⁻¹) * (g * g') := by group
    have h1 : l (π (g * x i * g⁻¹) (π (g * g') (v : V))) = l (π (g * g') (v : V)) :=
      LinearMap.congr_fun (hl _ hc) _
    rw [← Module.End.mul_apply, ← map_mul, hfac, map_mul, Module.End.mul_apply, h1]
  have hTT : l (((T * T') v : fixed π J) : V) = l (π g ((T' v : fixed π J) : V)) :=
    (hT (T' v) l hl).symm

  rw [hTT, hform, hmul, map_smul, map_sum, map_smul, map_sum]
  simp only [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [smul_eq_mul]
  field_simp

end GlobalTheory.CompanionTheory.Lbc
