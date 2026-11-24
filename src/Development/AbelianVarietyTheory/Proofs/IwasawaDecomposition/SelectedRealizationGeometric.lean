module

public import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.RatDatOfReal
public import Formalism.LocalToGlobal.IndefiniteReal.WeakCharacterisationWithError
public import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DivisionPairOfAdelicFormsFaceColumnsData
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
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotBaseCondFalse
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThetaChr
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SetUnipotentTranslate
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunKilled
import Development.AutomorphicArithmetic.PrimeDiscriminants.Scales

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw

open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.Mem.R3

attribute [local instance] GlobalTheory.Mem.R3.TwIn.grp GlobalTheory.Mem.R3.TwIn.fin GlobalTheory.Mem.R3.TwIn.alg

namespace GlobalTheory.Mem.R3.SelRealIn

open Formalism.L2.SG.RowsJoinPinned Formalism.IndefR.AutomorphicEvaluation Formalism.L2.Theta GlobalTheory.Mem.Top.Bl

section Gen
open Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]



theorem nexp_upd (R : RealDat3 D A3 Ks) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (S : RatDat D.ntw) (n : NExpRealS R cG S)
    (lam : type_of% R.lam3) (err : type_of% R.err0) :
    ∃ (Sx : RatDat D.ntw) (n' : NExpRealS ((R.updS R.kap lam).withErr err) cG Sx), HEq Sx S ∧ HEq n'.eF n.eF ∧ HEq n'.fi n.fi :=
  ⟨S, ⟨n.fi, n.geq, n.rho, n.chi, n.eF, n.bsup, n.act⟩, HEq.rfl, HEq.rfl, HEq.rfl⟩
end Gen

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {p : Prm hL} {K : Ctx}



end GlobalTheory.Mem.R3.SelRealIn
