module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitaryGroupFiniteVolume
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SiegelWeilUnitaryConvergentOfSiegelWeilConvergen
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCuspidalNeZero
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SiegelSetUnitary
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU PositivityTheory.Rg.Mass

namespace GlobalTheory.CompanionTheory.MassCocompact

theorem coCpt : CoCpt := by
  intro F E _ _ _ _ _ σ J d b li lam μ 𝓕 mi m hCM hJ hA _ _ hμ h𝓕 _ _
  have hW : GlobalTheory.SiegelSet.IsWittFrame σ J (0 : Matrix (Fin 2) (Fin 0) E) 0 :=
    ⟨Subsingleton.elim _ _, Subsingleton.elim _ _, Subsingleton.elim _ _, fun z _ _ hz => hA z hz⟩
  obtain ⟨C, hC, hcov⟩ := GlobalTheory.SiegelSet.Model.compact_quotient GlobalTheory.CompanionTheory.SiegelRed.siegelSetUnitary hCM hJ hW
  refine ⟨⟨C, hC, fun h => ?_⟩, ?_, ?_⟩
  · obtain ⟨γ, hγ, c, hc, e⟩ := hcov h
    exact ⟨⟨γ, hγ⟩, c, hc, e⟩
  · exact (GlobalTheory.SiegelWeilConvCompare.measure_fundamentalDomain_pos F E σ 2 J μ hμ 𝓕 h𝓕).ne'
  · exact (((GlobalTheory.CompanionTheory.SW.finVol_unitaryGroup F E σ hCM 2 J hJ).2 μ hμ).2 𝓕 h𝓕).ne

end GlobalTheory.CompanionTheory.MassCocompact

end
