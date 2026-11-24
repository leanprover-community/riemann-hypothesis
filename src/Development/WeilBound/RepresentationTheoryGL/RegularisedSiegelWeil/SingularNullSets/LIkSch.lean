module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsParamFunOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicIwasawaDecompositionWittIsotropicStabilizeStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompactAverageSchwartzProjectionMemAdelicSchwartStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GoodMajorantLevelConjUnitaryAdelicMaximalCompactStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IkedaPartialFourierIntegralMemAdelicSchwartzStatement
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

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LIkSch

theorem isCompact_K {D : D7} {T T₀ : HSp D} {r : ℕ} (d : HypDec T T₀ r) {l : Lvl T} (hl : l.Good) :
    IsCompact (l.K : Set (GA D T)) := by
  exact (GlobalTheory.T.goodMajorantLevel_conj_unitaryAdelicMaximalCompact D T T₀ r d l.c hl.2.2
    (GlobalTheory.T.adelic_iwasawa_decomposition_wittIsotropicStabilizer D T T₀ r d l.c (fun v hv => GlobalTheory.Core.Rk.IP.Model.isSplit_two v hv) hl.2.2) l hl).2.1

end PositivityTheory.Rg.Rsw.L.LIkSch

namespace PositivityTheory.Rg.Rsw.L

theorem ikSch : IkSch := by
  intro D n t B W d I θ hθ Φ hΦ
  have hK : IsCompact (I.l.K : Set (GA D B)) := LIkSch.isCompact_K d I.good
  have h1 := GlobalTheory.T.compactAverageSchwartzProjection_mem_adelicSchwartz D θ hθ B n I.l.K hK I.νK I.probK Φ hΦ
  refine ⟨h1, ?_⟩
  obtain ⟨𝓕, h𝓕⟩ := I.cov₁
  exact GlobalTheory.T.ikedaPartialFourierIntegral_mem_adelicSchwartz D θ hθ B W t n d I.μ₁ 𝓕 h𝓕 _ h1

end PositivityTheory.Rg.Rsw.L
