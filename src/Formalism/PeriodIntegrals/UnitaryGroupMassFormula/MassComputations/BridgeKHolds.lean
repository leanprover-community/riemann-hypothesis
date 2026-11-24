module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.StrongApproxN
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.BridgeFinK
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.TypedSets
open Matrix

namespace MassDataMassesW.NBr

theorem incAf_finHA {D : Formalism.BasicNotions.D7} (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I)
    (x : X.B.I.Gf) :
    Formalism.L2.SG.Sub.incAf X.B.I.cm.sig X.B.I.J (finHA X hb x) =
      Formalism.UG.bc (Formalism.L2.SG.AdBridge.prF X.B.I)
        (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) X.B.I.cm.sig X.B.I.J
          (Formalism.L2.SG.AdBridge.toHA X.B.I hb (1, x))) := rfl

theorem bridgeK_holds : BridgeK := by
  intro D X hb x
  have hbr' : X.B.I.fmat x = _ := (hb.choose_spec (1, x)).2
  have hK : x ∈ X.B.I.Kset ↔
      Formalism.L2.SG.AdBridge.toHA X.B.I hb (1, x) ∈ Formalism.L2.SG.AdBridge.KfHA X.B.I := by
    refine Iff.trans ?_ (adelic_compact_finite_places X.B.I (Formalism.L2.SG.AdBridge.toHA X.B.I hb (1, x)))
    show (∀ y, y ∈ X.B.I.Lf ↔ X.B.I.fmat x *ᵥ y ∈ X.B.I.Lf) ↔ _
    rw [hbr']
    rfl
  refine hK.trans ?_
  simp only [KX, Formalism.L2.SG.Sub.Kf, Subgroup.mem_iInf, Subgroup.mem_comap, MonoidHom.comp_apply,
    incAf_finHA]
  rfl

end MassDataMassesW.NBr
