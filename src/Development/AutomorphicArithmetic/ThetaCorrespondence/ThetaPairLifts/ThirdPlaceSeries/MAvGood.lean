module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NormalIntegrality
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompAtEqOneOfTameAt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MembersGood
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.Multi
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MTwinA
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem UpperTheory.One.M.good_cls_of_isLocS_av {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (i : D.nd.Loc) (Q : D.naut.AV i)
    (s : SplitPlace D.host.E) (σ : GlobalTheory.SmGL.IrrRep (GL (Fin D.R.nV) (s.w.adicCompletion D.host.E)))
    (hσ : IsLocS (P.H.av.S i Q) s σ) : UpperTheory.Zero.LLC.Good (GlobalTheory.LocLanglands.cls σ) :=
  GlobalTheory.AVGood.members_good UpperTheory.Zero.LLC.Pr.zel UpperTheory.Zero.LLC.Pr.bz D P.M P.tp.tup P.H.av P.H.level
    (GlobalTheory.AVGood.tameAtG_of_tupTied D P.cf P.tp) i Q s σ hσ
theorem UpperTheory.One.M.cls_eq_of_locV_eq' (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (i : D.nd.Loc)
    (Q Q' : D.naut.AV i) (sp : SplitPlace D.host.E)
    (σ σ' : GlobalTheory.SmGL.IrrRep (GL (Fin D.R.nV) (sp.w.adicCompletion D.host.E)))
    (hσ : IsLocS (P.H.av.S i Q) sp σ) (hσ' : IsLocS (P.H.av.S i Q') sp σ')
    (he : D.naut.locV i Q sp.w = D.naut.locV i Q' sp.w) :
    GlobalTheory.LocLanglands.cls σ = GlobalTheory.LocLanglands.cls σ' :=
  _root_.UpperTheory.One.M.local_component_class_eq_of_good hL D P i Q Q' sp σ σ' hσ hσ' he (_root_.UpperTheory.One.M.good_cls_of_isLocS_av P i Q' sp σ' hσ')
end
section
namespace GlobalTheory.ConjPlaceDual
end GlobalTheory.ConjPlaceDual
end
end
