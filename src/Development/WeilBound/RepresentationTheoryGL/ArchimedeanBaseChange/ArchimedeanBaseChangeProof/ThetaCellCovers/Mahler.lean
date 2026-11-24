module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.ThetaBasic
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.AdmissibleLeHolds
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.ContinuousPA
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.SquareIntegrableCovers.SetLIntegralLeOfCover
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace PositivityTheory.Rg.BcB.E1

theorem cellCover_holds : CellCover := cellCover_of cover_holds (conjCpt_of admissible_le_holds)

theorem cutBox_of' (h1 : DegBasis) (h2 : DegAdelic) (h3 : DegBdd) : CutBox := cutBox_of (degCell_of h1 h2 h3 torNorm_holds)

open PositivityTheory.Rg.Rs GlobalTheory.CuspRep in
theorem mahlerC_of_deg (h1 : DegBasis) (h2 : DegAdelic) (h3 : DegBdd) (h4 : DegRat) : D1.MahlerC := by
  intro E _ _ _ n c
  obtain ⟨Ω₀, hΩ, hc⟩ := cellCover_holds E n
  obtain ⟨C, -, hC⟩ := cutBox_of' h1 h2 h3 E n Ω₀ hΩ
  refine ⟨(fun p : (Fin n → ℝ) × GA E n => An.tor E p.1 * p.2) '' (Metric.closedBall 0 (C * (1 + |c|)) ×ˢ Ω₀),
    ((isCompact_closedBall _ _).prod hΩ).image ((JSqIntGlue.continuous_tor.comp continuous_fst).mul continuous_snd),
    fun g a1 a2 => ?_⟩
  obtain ⟨γ, m, o, ho, e⟩ := hc g
  refine ⟨ratGL E n γ⁻¹, ⟨_, rfl⟩, _, ⟨(_, o), ⟨mem_closedBall_zero_iff.2
    (hC (fun i => (m i : ℝ)) o ho _ (abs_nonneg c) (fun W hW => ?_) ?_), ho⟩, rfl⟩, ?_⟩
  · rw [← e, ← img_img_inv γ W, h4]
    exact (a1 _ (by rw [finrank_img, hW])).trans (le_abs_self c)
  · rw [← e, ← img_top γ, h4]
    linarith [le_abs_self c, (abs_le.1 a2).1]
  · simp only [← e, map_inv, inv_mul_cancel_left]

end PositivityTheory.Rg.BcB.E1
