module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsBisSide
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bdy
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.IsMultZero
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.IsCoreMod
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLoc
import Formalism.RealPlaceAnalysis.StatementA

@[expose] public section

noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.PairMult.Asm

open Formalism.REAL (GlRel qdet)
open GlobalTheory.CompanionTheory.PairMult
open GlobalTheory.CompanionTheory.RgCOBlock (sz shift fb)
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD

variable {n : ℕ}

theorem mem_down {S : Finset (Fin n)} (hS : ∀ a b, b ≤ a → a ∈ S → b ∈ S) (a : Fin n) :
    a ∈ S ↔ (a : ℕ) < S.card :=
  _root_.UpperTheory.Reformulated.B.DYlb8.main hS a

theorem twice_sum_Ico (m d : ℕ) :
    2 * ∑ k ∈ Finset.Ico m (m + d), (k : ℝ) = 2 * (d : ℝ) * m + d * ((d : ℝ) - 1) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [← add_assoc, Finset.sum_Ico_succ_top (by omega), mul_add, ih]
    push_cast
    ring

theorem level_sum (lev : Fin n → ℕ) (hm : Monotone lev) (c : ℕ) :
    2 * ∑ a ∈ univ.filter (fun a => lev a = c), ((a : ℕ) : ℝ) =
      2 * ((univ.filter fun a => lev a = c).card : ℝ) * ((univ.filter fun a => lev a < c).card : ℝ) +
        ((univ.filter fun a => lev a = c).card : ℝ) * (((univ.filter fun a => lev a = c).card : ℝ) - 1) := by
  set d := (univ.filter fun a => lev a = c).card with hd
  set m := (univ.filter fun a => lev a < c).card with hmm
  have hlow : ∀ a, lev a < c ↔ (a : ℕ) < m := fun a => by
    have := mem_down (S := univ.filter fun a => lev a < c) (fun x y hyx hx => by
      rw [mem_filter] at hx ⊢
      exact ⟨mem_univ _, lt_of_le_of_lt (hm hyx) hx.2⟩) a
    simpa using this
  have hcard : (univ.filter fun a => lev a < c + 1).card = m + d := by
    rw [hmm, hd, ← Finset.card_union_of_disjoint]
    · congr 1
      ext a
      simp only [mem_filter, mem_univ, true_and, mem_union]
      omega
    · rw [Finset.disjoint_left]
      intro a h1 h2
      have := (mem_filter.1 h1).2
      have := (mem_filter.1 h2).2
      omega
  have hup : ∀ a, lev a < c + 1 ↔ (a : ℕ) < m + d := fun a => by
    have := mem_down (S := univ.filter fun a => lev a < c + 1) (fun x y hyx hx => by
      rw [mem_filter] at hx ⊢
      exact ⟨mem_univ _, lt_of_le_of_lt (hm hyx) hx.2⟩) a
    rw [hcard] at this
    simpa using this
  have hle : m + d ≤ n := by
    rw [← hcard]
    exact (card_le_univ _).trans_eq (Fintype.card_fin n)
  have hmap : (univ.filter fun a => lev a = c).map Fin.valEmbedding = Finset.Ico m (m + d) := by
    ext k
    simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply, Finset.mem_Ico]
    constructor
    · rintro ⟨a, ha, rfl⟩
      have h1 := hlow a
      have h2 := hup a
      omega
    · rintro ⟨k1, k2⟩
      refine ⟨⟨k, by omega⟩, ?_, rfl⟩
      have h1 := hlow ⟨k, by omega⟩
      have h2 := hup ⟨k, by omega⟩
      simp only at h1 h2
      omega
  rw [← twice_sum_Ico, ← hmap, Finset.sum_map]
  rfl

section Alg

variable {W : Type} [AddCommGroup W] [Module ℂ W]

end Alg

section Spaces

variable {V : Type} [AddCommGroup V] [Module ℂ V]

end Spaces

end GlobalTheory.CompanionTheory.PairMult.Asm
