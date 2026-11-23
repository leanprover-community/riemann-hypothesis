module

public import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspFormRapidDecayStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspFormSiegelBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCompactIwasawa
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProjArchOfInfEmbArchPi
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SingleMulSingle
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryAdelicIwasawaCompactStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitarySiegelDomainExistsStatement
public import Development.WeilBound.ThetaLifts.Reductions.SiegelOfCore
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

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.SiegelRed

theorem siegelCore : SiegelCore := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y hW
  obtain ⟨K₁, h₁, c₁, i₁, g₁⟩ := GlobalTheory.CompanionTheory.SiegelArch.exists_kInf F E σ h n J hJ r X Y hW
  obtain ⟨K₂, h₂, c₂, i₂, g₂⟩ := GlobalTheory.T.unitary_adelic_iwasawa_compact F E σ h n J hJ r X Y hW
  obtain ⟨K, hK, hI, hG⟩ := GlobalTheory.CompanionTheory.SiegelAssemble.exists_compact_iwasawa F E σ h n J hJ r X Y hW K₁ K₂ h₁ h₂ c₁ c₂
    i₁ i₂ g₁ g₂
  obtain ⟨Ω, c, hΩ, hΩP, hc, hcov⟩ := GlobalTheory.T.unitary_siegel_domain_exists F E σ h n J hJ r X Y hW K hK hI hG
  exact ⟨K, Ω, c, hK, hΩ, hΩP, hc, hI, hG, hcov,
    GlobalTheory.CompanionTheory.SiegelConj.conj_compact F E σ h n J hJ r X Y hW Ω c hΩ hΩP hc,
    GlobalTheory.T.cusp_form_siegel_bound F E σ h n J hJ r X Y hW K Ω c hK hΩ hΩP hc,
    GlobalTheory.T.cusp_form_rapid_decay F E σ h n J hJ r X Y hW K Ω c hK hΩ hΩP hc⟩

theorem siegelSetUnitary : GlobalTheory.Published.SiegelSetUnitary :=
  siegel_of_core siegelCore

end GlobalTheory.CompanionTheory.SiegelRed
