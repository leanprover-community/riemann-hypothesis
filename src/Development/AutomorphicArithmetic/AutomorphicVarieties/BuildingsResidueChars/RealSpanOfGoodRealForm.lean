module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TupleActions.InstMulActionTup
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.SimpSpan
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Spanpsd
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open UpperTheory.V UpperTheory.V.KT UpperTheory.V.Af.BA in
theorem UpperTheory.real_span_of_good_real_form :
    UpperTheory.V.Af.BA.RePart → UpperTheory.V.Af.BA.ReInv → UpperTheory.V.Af.BA.GoodRe → UpperTheory.V.Af.BA.SpanRe := by
  intro hRP hRI hG L _ _ _ N σ hσ p t ht
  apply spanpsd
  intro k hk hzero
  obtain ⟨k', hk'q, hk'P⟩ := hRP L N σ hσ k
  obtain ⟨hk'psd, hk'0⟩ := hk'P hk
  apply hk'0
  refine ConeExtensionAcyclic.simp_span (hG L N σ hσ).locFin p t ht k' hk'psd ?_
  intro y hy
  have hM : ∀ (j : Fin (p + 1)), q (((t j : HR L N)) : HS L N) (y : Lat L N) = 1 := by
    intro j
    have := hy j
    rw [qr_apply] at this
    exact this
  have hinvq : ∀ (j : Fin (p + 1)), q (((t j : HR L N)) : HS L N) (sLat σ (y : Lat L N)) = 1 := by
    intro j
    rw [((hRI L N σ hσ).2 _ (t j).1.2).1 (y : Lat L N)]
    exact hM j
  rw [qr_apply, hk'q, hzero _ hM, hzero _ hinvq]
  norm_num
