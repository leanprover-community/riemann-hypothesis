module

public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsCrisPOfIsCrisDR
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.H2EquivOfTorsionCharacter
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisOneSubFrobeniusSurjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecompletionPhiSubOneBijective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineBoundsCrystallineDeRhamAll
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FundamentalExactSequenceContinuityAllTheories
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FundamentalMapSurjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeNhds
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyThetaOnBdRPlusPeriodData
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateDeRhamFiltrationQuotientInvariants
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateDualDeRhamAndFilZeroDimAll
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyLocalPeriodRingsData
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation TensorProduct

namespace GlobalTheory.LocInputs


open TensorProduct in
theorem _root_.GlobalTheory.LocInputs.ties_and_inputs_of_duality_euler :
    _root_.Formalism.GaloisCohomology.LocalTateDualityK → _root_.Formalism.GaloisCohomology.LocalEulerCharK →
      ∀ (D : _root_.Formalism.BasicNotions.D7) (HW : _root_.Formalism.BasicNotions.HWOf D.loc) (F : _root_.Formalism.BasicNotions.FonOf D.loc D.locA HW),
        ∃ _J : _root_.Formalism.MainNotions.LocalSituation.Ties D.loc D.locA HW F, _root_.Formalism.MainNotions.LocalSituation.admitted D HW F := by
  intro hduality heuler D HW F
  refine ⟨⟨fun l _ => (_root_.GlobalTheory.ThetaTie.nonempty_thetaL D l).some⟩, ?_⟩
  refine ⟨?_, hduality, _root_.GlobalTheory.TateTop.tate_h2_of_local_duality hduality D, heuler,
    _root_.GlobalTheory.TateFilQuot.tate_fil_quot D, _root_.GlobalTheory.FundCont.fundamentalExactSequence_continuity_all_theories D,
    _root_.GlobalTheory.Per.FontaineAll.fontaine_bounds D, _root_.GlobalTheory.TateDualFil.main D, ?_⟩
  · refine _root_.GlobalTheory.FundSeq.surjective_half_of_onto (fun l _ => ?_) D
    obtain ⟨C⟩ := _root_.GlobalTheory.MemLoc.nonempty_core l
    exact _root_.GlobalTheory.FundSeq.ontoAt_of_core C
      (_root_.GlobalTheory.MemLoc.one_sub_phi_onto l C) (_root_.GlobalTheory.MemLoc.FundOnto.fundOnto l C)
  · intro l _ K s LL h
    exact ⟨_root_.GlobalTheory.Cyc.FontW.main D HW F l K s LL h,
      _root_.GlobalTheory.Decompl.decompletion D HW F l K s LL h⟩

end GlobalTheory.LocInputs
