module

public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TranslateMomentsAllOfJetMomR
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormalisedFamilySatisfiesEquivarianceLaws
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SpanRangeEmb4EqTop
import Formalism.LocalToGlobal.GlobalTheory.GL3.DeterminantNormOneOfUnitDisc
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.MemMoveLevUloc
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.WittFractionToCpAlgebraMap
import Formalism.LocalToGlobal.InertKernelTheory.SecondKernelEntrywiseLastLevel
import Formalism.LocalToGlobal.InertKernelTheory.StatementInt
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.LtCNeZero
import Formalism.SharpRestriction.GrowthBounds.ChartComparison.NrmAMemAdForms
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.CoeffProdRename

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix

namespace GlobalTheory.SelfDualChiAlg

theorem chi_detId_and_chiFac_alg : ∀ (D : D7) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsChi D χ →
    (∀ (N : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)), Even N → IsSDLat D.host.E N L →
      χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D N) L) ∈ TaylorLogMetric.Qbar) ∧
    ∀ {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)),
      TaylorLogMetric.admitted D N N' L L' → Base.chiFac χ N N' L L' ∈ TaylorLogMetric.Qbar ∧ Base.chiFac χ N N' L L' ≠ 0 := by
  intro D χ hχ
  refine ⟨fun N L hN hL => ?_, fun L L' hA => ⟨GlobalTheory.MomT.FromComb.chiFac_mem hχ hA, ?_⟩⟩
  · exact GlobalTheory.MomT.FromComb.chi_mem hχ
      (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.relative_determinant_norm_one D N _ L hN (GlobalTheory.FourthRootStd.stdL_isSD D N) hL)
  · exact GlobalTheory.Mem.NatEqui.chiFac_ne_zero hχ hA.2.2.1 hA.2.2.2

end GlobalTheory.SelfDualChiAlg
