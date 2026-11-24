module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
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

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.wtLin_of :
    FibFin → WtLin := by
  intro hF
  refine ⟨?_, ?_, ?_⟩
  · intro Z S p _ w w' h1 h2
    unfold IsWt at *
    intro A φ hφ
    obtain ⟨ψ1, hψ1, e1⟩ := h1 A φ hφ
    obtain ⟨ψ2, hψ2, e2⟩ := h2 A φ hφ
    refine ⟨ψ1 + ψ2, hψ1.add hψ2, ?_⟩
    intro Ω _ _ x
    haveI := A.finite
    have hfin := hF A.r Ω x
    rw [Pi.add_apply, e1, e2, ← finsum_mem_add_distrib hfin]
    refine finsum_congr fun z => finsum_congr fun _ => ?_
    show _ = (w Ω _ + w' Ω _) * _
    ring
  · intro Z S p _ d w h1
    unfold IsWt at *
    intro A φ hφ
    obtain ⟨ψ1, hψ1, e1⟩ := h1 A φ hφ
    refine ⟨(fun t => d * t) ∘ ψ1, hψ1.comp _, ?_⟩
    intro Ω _ _ x
    rw [Function.comp_apply, e1, mul_finsum_mem]
    refine finsum_congr fun z => finsum_congr fun _ => ?_
    show _ = d * w Ω _ * _
    ring
  · intro Z S p _ d
    unfold IsWt
    intro A φ hφ
    haveI : IsIso A.r := by
      rw [← A.pb.isoPullback_hom_snd]
      infer_instance
    refine ⟨(fun t => d * t) ∘ φ ∘ ⇑(inv A.r), (hφ.comp_continuous (inv A.r).continuous).comp _, ?_⟩
    intro Ω _ _ x
    have hs : fib A.r x = {x ≫ inv A.r} := by
      ext z
      show z ≫ A.r = x ↔ z = x ≫ inv A.r
      constructor
      · rintro rfl
        simp
      · rintro rfl
        simp
    rw [hs, finsum_mem_singleton, pt_comp]
    rfl
