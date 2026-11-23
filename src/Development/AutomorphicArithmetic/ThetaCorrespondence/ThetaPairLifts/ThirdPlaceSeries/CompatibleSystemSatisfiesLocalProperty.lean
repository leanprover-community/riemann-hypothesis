module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaDataExists
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AtMemberImp
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LabFixedIff
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalSeriesConcreteOfDzSwap
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OpinAtMemStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SpecializationAtMemberOfLayer
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ZlStableAtStatement
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
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
namespace GlobalTheory.SerFinished

theorem locComp_of_isRc_classMapD_cenLoc : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ _ _ _ _ => GlobalTheory.TypeLeaf.SerLoc (w.D Z) := by
  intro hP hL
  refine _root_.GlobalTheory.HeightCounting.Up.Model.AtMem.at_member_imp (_root_.GlobalTheory.HeightCounting.Up.Model.AtMem.and_z (_root_.GlobalTheory.T.exists_character_choice_pin_at_of_third_layer hP hL)
    (_root_.GlobalTheory.HeightCounting.Up.Model.AtMem.and_z (_root_.GlobalTheory.T.coefficient_duty_pin_at_each_member hL) (_root_.GlobalTheory.T.cenLoc_zlStable_cenInt_at_members hL))) ?_
  rintro K B f T w Z Wt p0 t nch n c ⟨⟨P, hPin⟩, hO, hC, -, -⟩
  have hlab : GlobalTheory.SerSys.LabTie (w.D Z) fun k => @GlobalTheory.Mem.TypePl.labDat ((w.D Z).host.g k) ⟨(w.D Z).host.g_prime k⟩ :=
    (_root_.GlobalTheory.CoefDuty.OPinModel.labFixed_iff_alt c.a).2 hO.lab
  have htame : ∀ D', D' = withLoc c.a.nt.L → ∀ k (v : D'.nd.PlG k),
      ∃ κ : IsLocalRing.ResidueField (D'.nd.plOm.1 (D'.naut.plGw k v)) ≃+* Formalism.CyclotomicNorms.Fbar (D'.host.g k),
        TameCoupled (D'.nd.plOm.1 (D'.naut.plGw k v)) κ (D'.ntypes.tg k v)
          (@GlobalTheory.Mem.TypePl.labDat (D'.host.g k) ⟨D'.host.g_prime k⟩).gen := by
    rintro _ rfl k v
    exact ⟨c.a.nt.A.grp.kv k v, _root_.GlobalTheory.CoefDuty.OPinModel.labDat_gen_tame_at_plGw hO k v⟩
  refine _root_.UpperTheory.Lit.Dz.compatibleSystemLocalProperty hP.what₂ hP.green hP.zel hL (w.D Z) P _ hlab (htame _ c.a.nt.eq) ?_
  rw [hPin.M_eq]
  exact hC
end GlobalTheory.SerFinished
end
section
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

theorem _root_.GlobalTheory.T.serLoc_at_member_of_published_inputs : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ _ _ _ _ => GlobalTheory.TypeLeaf.SerLoc (w.D Z) := by
  first | exact @_root_.GlobalTheory.SerFinished.locComp_of_isRc_classMapD_cenLoc | exact _root_.GlobalTheory.SerFinished.locComp_of_isRc_classMapD_cenLoc | (intros; apply _root_.GlobalTheory.SerFinished.locComp_of_isRc_classMapD_cenLoc <;> assumption)
end
end
