module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormOneAtOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCompactOpenLatticeStabilizerAtPlaces
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartMemFrameStabilizerIffLocalStabilizer
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InstanceIotaReadoutRealTrivialStabilizerUnitary
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.KsetAt

theorem mem_Kset_iff_moves : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (v : GlobalTheory.FinPl.Pl D) (κ : GA D (D.sp.Y 0)), κ ∈ grpAt (D.sp.Y 0) (· = v) → ((iotaX X h κ).2 ∈ X.B.I.Kset ↔ Moves (D.sp.Y 0) κ (latS D) (latS D) (· = v)) := by
  intro D X h v κ hκ
  have hlat : Submodule.IsLattice D.host.E (latS D) :=
    GlobalTheory.StdFrames.isLattice_crdLat (D.sp.Y 0) (D.sp.Y 0).standardTuple_isLattice
  obtain ⟨β, hβ⟩ := GlobalTheory.StdFrames.exists_base (D.sp.Y 0)
  have hβ' : Formalism.L2.DIV.IsFrame β (latS D) := by
    change Formalism.L2.DIV.IsFrame β (Formalism.L2.Herm.crdLat (D.sp.Y 0) (D.sp.Y 0).L0)
    rw [hβ]
    exact GlobalTheory.StdFrames.isFrame_lat β
  have h1 := ((GlobalTheory.SeeConjReadIota.read_iota X h β hβ' κ).2.1)
  have h2 := GlobalTheory.ChainOnto.LStab.finE_mem_St_iff_of_fg (D.sp.Y 0) β (latS D) hβ' hlat.fg κ
  have h3 : κ ∈ GlobalTheory.AdelicU.levelOpen D.sp.cm.sig (D.sp.Y 0).gram (latS D) ↔
      Moves (D.sp.Y 0) κ (latS D) (latS D) (· = v) :=
    ⟨fun hk => GlobalTheory.FinPl.KOpen.moves_of_levelOpen (D.sp.Y 0) (latS D) hlat.fg (· = v) hk,
     fun hm => GlobalTheory.FinPl.KOpen.levelOpen_of_inK (D.sp.Y 0) (latS D) hlat.fg (· = v) ⟨hκ, hm⟩⟩
  exact h1.trans (h2.trans (GlobalTheory.AdelicU.mem_levelOpen.symm.trans h3))

end GlobalTheory.Core.Mi.KsetAt
