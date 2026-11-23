module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharacterValuesInjectiveLength
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFiniteChosenSet
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SettingOfLive
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RowsExhaust

@[expose] public section



section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial
  GlobalTheory.EtaJoin GlobalTheory.CoefDuty
namespace GlobalTheory.OChoose
theorem oChoose_alt : GlobalTheory.TwSys.Cheb → ∀ (D : D7), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → GlobalTheory.SplitCoef.OSplit D → ∀ i : D.nd.Loc,
    ZDecomp D.nd i → Live D.nd i → ∃ S : Finset ℂ, Chosen D.nd D.naut i ↑S := by
  intro hC D hP hO i hZ hL
  classical
  obtain ⟨rep, ρ, hG, hS⟩ := _root_.GlobalTheory.AbsoluteIrreducibilityOfTraceSpan.setting_of_live_alt_alt hC D hP hO i hZ hL
  obtain ⟨g0, hg0⟩ := exists_wild_inertia_cyclotomic_generator D i
  have hcont : GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.RepCont D.nd i rep := fun x => (hG x).1
  have ha := (GlobalTheory.ConsExists.consExist D.nd i rep ρ (D.nd.O i) (D.nd.T i) rep ρ (D.nd.chi i) hcont
    (GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.isEnlargement_self D.nd i rep ρ) hS).1
  have hch : ∀ π : D.nd.Z i, ∃ q : (D.nd.X i → Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)) ×
      (D.nd.X i → Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)) ×
      (D.nd.X i → Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)),
      GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.IsChoice D.R.t (D.nd.T i) rep ρ (D.nd.chi i) π g0 0 q.1 q.2.1 q.2.2 := fun π => by
    obtain ⟨eB, e1, X0, h⟩ := ha π π.2 g0 hg0.1 0
    exact ⟨(eB, e1, X0), h⟩
  choose q hq using hch
  refine ⟨Finset.univ.biUnion fun π : D.nd.Z i => Finset.univ.biUnion fun x : D.nd.X i =>
    ((GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.blockPol ((q π).1 x) ((q π).2.2 x)).map (iotaO D.nd D.naut i)).roots.toFinset,
    rep, ρ, hG, hS, fun π hπ => ?_⟩
  refine ⟨g0, 0, (q ⟨π, hπ⟩).1, (q ⟨π, hπ⟩).2.1, (q ⟨π, hπ⟩).2.2, hg0, hq ⟨π, hπ⟩, fun x => ?_⟩
  obtain ⟨hm, hd⟩ := blockPol_iota D i hS (hq ⟨π, hπ⟩) x
  obtain ⟨α, hα, he⟩ := exists_fin_roots hm hd
  refine ⟨α, fun c => Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨⟨π, hπ⟩, Finset.mem_univ _,
    Finset.mem_biUnion.2 ⟨x, Finset.mem_univ _, Multiset.mem_toFinset.2 (hα c)⟩⟩), he⟩
end GlobalTheory.OChoose
end
end
