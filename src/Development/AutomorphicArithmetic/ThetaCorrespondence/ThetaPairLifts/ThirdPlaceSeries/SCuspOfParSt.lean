module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaDataExists
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EsymmMapMulConst
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEigTrue
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProdXSubCScaleMemLifts
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsEigTrue
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GalPolLiftsOfSplit
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LowerLeftValuationEqZeroAllStages
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

@[expose] public section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.SCuspRows
theorem sCusp_of_parSt_alt_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.ParameterStatement hL → _root_.GlobalTheory.HeightCounting.Up.RationalityStatementThirdPlaceSeries hL → _root_.GlobalTheory.HeightCounting.Up.CuspStatement' hL := by
  intro hP hL hPar hRat
  refine allSt_mono' (allSt_and' (allSt_and' hPar hRat) (_root_.GlobalTheory.HeightCounting.Up.lowerLeftValuation_eq_zero_all_stages_alt hP)) ?_
  rintro K B f T w P x ⟨⟨hp, he⟩, hv⟩ l j hj1 hj2 σ hσ hg
  obtain ⟨π, hc, hr, hs, -, -, -⟩ := hp l j hj1 hj2 σ hσ hg
  obtain ⟨n⟩ := he l
  obtain ⟨Sb, hn⟩ := _root_.GlobalTheory.SCuspRows.exists_eigTrue_alt l n
  refine ⟨π, hc, hr, hs, ?_⟩
  have h2 := GlobalTheory.CuspFrobSplit.galPol_lifts_ae (Dof x) (cfOf x) l.a.A.row Sb n.In.eig hv hn j hj1 hj2 σ hσ hg π hc hs
  have h4 := _root_.GlobalTheory.GalAllPlaces.galPol_lpTw_mem_lifts_eventually hL hP.what₂.fin hP.what₂.gal hP.what₂.cheb (Dof x) l.a.A.wdT l.a.cg _ (embLL0 (Dof x)) π hc hr h2
  exact (GlobalTheory.TwistLift.galPol_lifts_tw_etaTinv (Dof x) (cfOf x) l.a.A.chr hv π h4).mono fun w hw => (Polynomial.mem_lifts _).1 hw
end GlobalTheory.SCuspRows
end
end
