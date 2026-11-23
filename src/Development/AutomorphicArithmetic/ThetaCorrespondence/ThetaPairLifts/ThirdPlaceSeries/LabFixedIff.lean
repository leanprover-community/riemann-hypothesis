module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabFixedOfTypesTrue
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OPin
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
noncomputable section
namespace GlobalTheory.CoefDuty.OPinModel
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.HeightCounting GlobalTheory.Mem.Col2
theorem labFixed_iff_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch}
    (a : _root_.GlobalTheory.Mem.Top.Bl.NAtData hL D cf nch tp) : LabFixed D ↔ LabFixed a.nt.D := by
  have e : ∀ D', D' = withLoc a.nt.L → (LabFixed D' ↔ LabFixed a.nt.D) := by
    rintro _ rfl
    exact labFixed_withLoc _
  exact e D a.nt.eq
variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B}
theorem labDat_gen_tame_at_plGw {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch}
    {a : _root_.GlobalTheory.Mem.Top.Bl.NAtData hL D cf nch tp} (h : _root_.GlobalTheory.CoefDuty.OPinAlt a) (k : Fin 2) (v : a.nt.D.nd.PlG k) :
    @Formalism.L2.NT.TameCoupled _ _ _ _ _ (a.nt.D.nd.plOm.1 (a.nt.D.naut.plGw k v)) _ ⟨a.nt.D.host.g_prime k⟩ (a.nt.A.grp.kv k v)
      (a.nt.D.ntypes.tg k v) (@GlobalTheory.GLq.LabelDatum.gen _ ⟨a.nt.D.host.g_prime k⟩
        (@GlobalTheory.Mem.TypePl.labDat (a.nt.D.host.g k) ⟨a.nt.D.host.g_prime k⟩)) := by
  rw [← h.gen k]
  exact a.nt.A.grp.tg_tame k v
end GlobalTheory.CoefDuty.OPinModel
end
end
