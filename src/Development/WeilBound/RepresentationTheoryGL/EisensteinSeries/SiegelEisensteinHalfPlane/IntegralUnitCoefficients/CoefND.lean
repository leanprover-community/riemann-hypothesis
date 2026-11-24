module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
public import Development.WeilBound.CoreStatements.PublishedTheorems.SiegelWeilSchrodinger.SiegelWeilUnitarySchrodingerLit
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AnisotropyOfRangeStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DictionaryMaximalCompactPartsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FockSplittingMaximalCompactStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NondegenerateOfWhittakerStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaCoefficientOfConvergenceStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnfoldingHoldsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerAdditivityStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerMaximalCompactGeneralStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerNondegenerateOfIwasawaStatement
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.SchrodingerMatching.MatchMono
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.SphericalBigCell.IfrBAddOfWeilThetaConvergence
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.WhitGenLt
public import Development.WeilBound.CoreStatements.PublishedTheorems.SiegelWeilSchrodinger.Bridge
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.IntegralUnitCoefficients.GenAHf
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Top7
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.WlocTop
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Wtc
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace PositivityTheory.SiegelWeilCoefficients

open PositivityTheory.Rg.Sw.Glob PositivityTheory.PfSWUS

theorem coefND : CoefND :=
  GlobalTheory.T.nondegenerate_of_whittaker GlobalTheory.T.unfolding_holds (GlobalTheory.T.theta_coefficient_of_convergence wtc)
    (GlobalTheory.T.whittaker_nondegenerate_of_iwasawa (GlobalTheory.T.whittaker_maximal_compact_general whitGenLt (GlobalTheory.T.dictionary_maximal_compact_parts GlobalTheory.T.fock_splitting_maximal_compact GlobalTheory.T.whittaker_additivity
      (PositivityTheory.PfSWUS.HandIAdd.ifrBAdd_of_weilThetaConvergence wtc) PositivityTheory.PfSWUS.SwMatch.matchMono)
      GlobalTheory.T.anisotropy_of_range))

theorem lit : GlobalTheory.Published.SiegelWeilUnitarySchrodingerLit := by
  intro D n V a1 a2 a3 ψ hψ χ hχ hη θ hθ μ 𝓕 hμ ω hω H hH l hl s hs ν hν Φ hΦ g
  exact top7 genA_hf (gIdil_gen wtc genA_hf) coefND D n V ψ χ θ μ ω H l s ν Φ
    ⟨hψ, hχ, hη, hθ, ⟨𝓕, hμ⟩, hω, hH, hl, hs, hν, hΦ⟩ ⟨a1, a2, a3⟩ (by omega) g

theorem field : GlobalTheory.Published.SiegelWeilUnitarySchrodinger :=
  PositivityTheory.Lit1.SWUS.siegelWeilUnitarySchrodinger_of_lit lit wtc

end PositivityTheory.SiegelWeilCoefficients

end
