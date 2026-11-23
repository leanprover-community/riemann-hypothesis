module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabFixedOfTypesTrue
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RootsOfUnityRingLeWittIntegers
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic

@[expose] public section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
namespace GlobalTheory.GoodFirst

abbrev _root_.GlobalTheory.GoodFirst.FirstTermConditionAllStagesAlt : Prop := ∀ (hG : GlobalTheory.GLq.Green) (hZ : GlobalTheory.Published.ZelevinskyPolynomialRing)
    (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (cf : CharFrame D) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r)
    (a : _root_.GlobalTheory.HeightCounting.HeightCountingBaseData hL D cf rep) (hlab : GlobalTheory.CoefDuty.OPinModel.LabFixed D)
    (hloc : ∀ (I : GlobalTheory.TypeRec.Ident D) cp, GlobalTheory.TypeRec.IsComp I rep cp → ∀ σ, ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V)
      (ρ : Representation ℂ (G0g D.nd) V) (W : Submodule ℂ V) (x : V),
      (∀ k v, GlobalTheory.GoodTypes.ConjIn ρ W (GlobalTheory.GoodTypes.facHom D k v) (cp σ k v).ρ) ∧ x ≠ 0 ∧
        (∀ b, ρ.asAlgebraHom b x ∈ W) ∧ ρ.asAlgebraHom D.ntypes.e0 x = x),  GoodFTAll D
end GlobalTheory.GoodFirst
end
end
