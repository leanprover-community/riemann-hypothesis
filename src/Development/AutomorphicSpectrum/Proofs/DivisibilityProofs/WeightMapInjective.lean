module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
public import Mathlib.Order.Interval.Finset.Fin
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.SwapLoc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSuppAA

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Top.FlDeg

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Top.FlDeg

theorem aeval_tail_gapX {Ψ : Type} {N : ℕ} (p : Ψ × Fin N) :
    (aeval (fun q : Ψ × Fin N => ∑ s ∈ Finset.Ici q.2, (X (q.1, s) : MvPolynomial (Ψ × Fin N) ℝ)))
      (PB.gapX p) = X p := by
  obtain ⟨τ, i⟩ := p
  simp only [PB.gapX, map_sub, aeval_X]
  split_ifs with h
  · rw [aeval_X]
    have hI : Finset.Ici i = insert i (Finset.Ici (⟨(i : ℕ) + 1, h⟩ : Fin N)) := by
      ext s
      have := s.2
      simp only [Finset.mem_Ici, Finset.mem_insert, Fin.le_def, Fin.ext_iff]
      omega
    rw [hI, Finset.sum_insert (by simp [Fin.le_def])]
    ring
  · have hI : Finset.Ici i = {i} := by
      ext s
      have := s.2
      simp only [Finset.mem_Ici, Finset.mem_singleton, Fin.le_def, Fin.ext_iff]
      omega
    rw [map_zero, sub_zero, hI, Finset.sum_singleton]

theorem toWt_leftInverse_injective (Ψ : Type) (N : ℕ) :
    Function.Injective (PB.toWt : MvPolynomial (Ψ × Fin N) ℝ →ₐ[ℝ] MvPolynomial (Ψ × Fin N) ℝ) := by
  set T : MvPolynomial (Ψ × Fin N) ℝ →ₐ[ℝ] MvPolynomial (Ψ × Fin N) ℝ := aeval (fun q : Ψ × Fin N => ∑ s ∈ Finset.Ici q.2, (X (q.1, s) : MvPolynomial (Ψ × Fin N) ℝ)) with hT
  have hli : T.comp PB.toWt = AlgHom.id ℝ _ := by
    apply MvPolynomial.algHom_ext
    intro p
    simp only [AlgHom.comp_apply, AlgHom.id_apply, PB.toWt, aeval_X, hT]
    exact aeval_tail_gapX p
  intro a b hab
  have ha : T (PB.toWt a) = a := by rw [← AlgHom.comp_apply, hli, AlgHom.id_apply]
  have hb : T (PB.toWt b) = b := by rw [← AlgHom.comp_apply, hli, AlgHom.id_apply]
  rw [← ha, ← hb, hab]

end GlobalTheory.CompanionTheory.Ar.Top.FlDeg
