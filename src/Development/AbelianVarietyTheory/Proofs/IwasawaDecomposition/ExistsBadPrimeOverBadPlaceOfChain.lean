module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsPrimesOk
import Formalism.LocalToGlobal.Columns.BaseLemmas
public import Formalism.LocalToGlobal.Columns.RecLevelLocP
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.AdT

theorem exists_SBof_over : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (a : I.ι) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), v ∈ badG (I.rec7 l Z) ∨ I.UnderQ a v → ∃ P ∈ SBof I a, Formalism.L2.Col.IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P) := by
  classical
  intro B X I hOk l Z a v hv
  obtain ⟨-, hPr, -⟩ := base_fields_primes_ok B X
  rcases hv with hv | ⟨P, hP, rfl⟩
  · have key : ∀ (i : Fin 2), v ∈ plUnder (I.rec7 l Z).host.F (E := (I.rec7 l Z).host.E) ((B.primes X).vG i) ↔ ((B.primes X).g i : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal := by
      intro i
      have h0 : B.fields.conjO ((B.primes X).piG i) ≠ 0 := by
        intro h
        have h1 := hPr.piG_norm i
        rw [h, mul_zero] at h1
        exact (Nat.cast_ne_zero.2 (hPr.g_prime i).ne_zero) h1.symm
      refine mem_plUnder_iff_norm (I.rec7 l Z).sp.cm (fun P => mem_divs h0 P) ((B.primes X).g i) ?_ v
      have h2 : cO (I.rec7 l Z).host.E (B.fields.conjO ((B.primes X).piG i)) = (B.primes X).piG i := cO_cO ((B.primes X).piG i)
      rw [h2]
      have h3 : B.fields.conjO ((B.primes X).piG i) * (B.primes X).piG i = ((B.primes X).g i : 𝓞 B.fields.E) := by
        rw [mul_comm]
        exact hPr.piG_norm i
      exact h3
    have hv' : v ∈ plUnder (I.rec7 l Z).host.F (E := (I.rec7 l Z).host.E) (B.primes X).vGs := by
      rcases hv with h | h
      · obtain ⟨P, hP, hPv⟩ := (key 0).2 h
        exact ⟨P, Finset.mem_union_left _ hP, hPv⟩
      · obtain ⟨P, hP, hPv⟩ := (key 1).2 h
        exact ⟨P, Finset.mem_union_right _ hP, hPv⟩
    obtain ⟨P, hP, hPv⟩ := hv'
    refine ⟨P, Finset.mem_union_left _ hP, ?_⟩
    exact hPv
  · refine ⟨P, Finset.mem_union_right _ hP, ?_⟩
    exact rfl

end GlobalTheory.Mem.Col2.AdT
