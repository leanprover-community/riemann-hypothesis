module

public import Formalism.LocalToGlobal.TorsionIntegrality.ComplexLatticeClosure.ExistsTwoTorsionOffKernels
public import Formalism.LocalToGlobal.GlobalTheory.LinkTiesTh
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.QuasiPeriodConstUnique
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.GlobalTheory.LinkTiesOm

@[expose] public section

noncomputable section

namespace Formalism.L2.Th1.F2

open Formalism.L2.GlobalTheoryTheory Formalism.MainNotions

theorem im_pair (a b : ℂ) (m n p q : ℤ) :
    ((starRingEnd ℂ) ((m : ℂ) * a + (n : ℂ) * b) * ((p : ℂ) * a + (q : ℂ) * b)).im
      = ((m * q - n * p : ℤ) : ℝ) * ((starRingEnd ℂ) a * b).im := by
  simp only [map_add (f := _), map_mul, map_intCast, Complex.mul_im, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.intCast_re,
    Complex.intCast_im]
  push_cast
  ring

theorem area_eq_holds : AreaEq := by
  intro L
  have hpos : 0 < F.area L := F.areaPos L
  unfold TaylorLogMetric.area
  apply IsLeast.csInf_eq
  refine ⟨⟨hpos, L.ω₁, L.ω₁_mem_lattice, L.ω₂, L.ω₂_mem_lattice, rfl⟩, ?_⟩
  rintro a ⟨ha, u, hu, v, hv, rfl⟩
  obtain ⟨m, n, rfl⟩ := PeriodPair.mem_lattice.mp hu
  obtain ⟨p, q, rfl⟩ := PeriodPair.mem_lattice.mp hv
  rw [im_pair] at ha ⊢
  rw [abs_mul] at ha ⊢
  have h1 : (1 : ℝ) ≤ |((m * q - n * p : ℤ) : ℝ)| := by
    have h0 : (m * q - n * p : ℤ) ≠ 0 := by
      intro h
      rw [h] at ha
      simp at ha
    have := Int.one_le_abs h0
    exact_mod_cast this
  unfold F.area
  nlinarith [abs_nonneg ((starRingEnd ℂ) L.ω₁ * L.ω₂).im]

theorem koszul_homology_eq (L : PeriodPair) (z w : ℂ) : H1 L.lattice.toAddSubgroup z w = F.herm L z w := by
  unfold H1 F.herm
  rw [area_eq_holds L]

theorem thetaTranslationOperator_apply (L : PeriodPair) (x : ℂ) (G : ℂ → ℂ) (z : ℂ) : U1 L.lattice.toAddSubgroup x G z = F.opU L x G z := by
  unfold U1 F.opU
  simp only [koszul_homology_eq]

end Formalism.L2.Th1.F2
