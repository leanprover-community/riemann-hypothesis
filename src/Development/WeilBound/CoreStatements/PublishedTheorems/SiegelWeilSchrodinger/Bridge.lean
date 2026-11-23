module

public import Development.WeilBound.CoreStatements.PublishedTheorems.SiegelWeilSchrodinger.SiegelWeilUnitarySchrodingerLit
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegrableStandardPairThetaWeilRangeStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDecompositionUnitary
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelParabolicUnnMatrixBlockUpperTriangular
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilSchrodingerRealParameter
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.LeftInvOfIsSection
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift

@[expose] public section

noncomputable section

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Lit1.SWUS

theorem siegelWeilUnitarySchrodinger_of_lit :
    GlobalTheory.Published.SiegelWeilUnitarySchrodingerLit → GlobalTheory.Published.WeilThetaConvergence →
      GlobalTheory.Published.SiegelWeilUnitarySchrodinger := by
  intro hL hW D n V a1 a2 a3 ψ hψ χ hχ hη θ hθ μ 𝓕 hμ ω hω H hH l hl s hs ν hν Φ hΦ
  have hn : 0 < n := by omega
  have hS := GlobalTheory.StdUnn.SiegelSection.fock_mem_degenerate D n V ψ hψ χ hχ hη θ hθ μ 𝓕 hμ ω hω l hl s hs Φ hΦ
  have e : ∀ z, sect ω H Φ z = stdSec H (fun g : G D n => (ω g Φ).1 0) (s0 V n) z :=
    fun z => funext fun g => mul_comm _ _
  refine ⟨fun g => GlobalTheory.T.integrable_standardPair_theta_weilRange hW D n V hn a3 θ hθ ω ν hν Φ g, fun z hz => ⟨?_, fun g => ?_⟩,
    hL D n V a1 a2 a3 ψ hψ χ hχ hη θ hθ μ 𝓕 hμ ω hω H hH l hl s hs ν hν Φ hΦ⟩
  · exact GlobalTheory.StdUnn.LeftInvSect.leftInv_sect D n (GlobalTheory.StdUnn.Iwasawa.exists_mul D n) V ψ χ θ μ ω hχ hω H hH Φ z
  · rw [e]; exact GlobalTheory.StdUnn.PolesModel.cosetConv_stdSec hH hS hz g

end PositivityTheory.Lit1.SWUS

end
