module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CommutingLevelOperators
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCharLab
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelCharacterTeichmullerLabelOfGoodTypes
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ParamsEx

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

theorem _root_.GlobalTheory.T.levelCharacter_teichmullerLabel_of_goodTypes : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks),
    GlobalTheory.IndefiniteRowSideFullHecke.CommutingLevelOperators.GoodTypes R → ∀ (k : Fin 2) (v : D.nd.PlG k) (i : Fin D.R.m) (PP : Pl D.host.E),
    R.C.P.Div k PP → ∀ (iso : ZMod (D.host.g k) ≃+* kP PP) (ε : ℤ), (ε = 1 ∨ ε = -1) →
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    ∃ L : GlobalTheory.GLq.LabelDatum (D.host.g k), (∀ f, D.ntypes.eSer k f = GlobalTheory.GLq.eSerC L D.R.r f) ∧
      ∃ c : ZMod (D.host.g k),
        GlobalTheory.GLp.IsCharLab L ((zpowGroupHom ε).comp ((R.chi ((i : ℕ) + 1) PP).comp
          (Units.map (iso : ZMod (D.host.g k) →* kP PP)))) c ∧
        (c = ((D.nd.chiT k v i : (ZMod (D.host.g k))ˣ) : ZMod (D.host.g k)) ∨
          c = (((D.nd.chiT k v i)⁻¹ : (ZMod (D.host.g k))ˣ) : ZMod (D.host.g k))) := by
  first | exact @GlobalTheory.CharLabTransport.charLab_of_goodTypes | exact GlobalTheory.CharLabTransport.charLab_of_goodTypes | (intros; apply GlobalTheory.CharLabTransport.charLab_of_goodTypes <;> assumption)
