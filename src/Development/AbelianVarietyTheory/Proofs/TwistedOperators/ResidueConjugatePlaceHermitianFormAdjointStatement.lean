module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CPAsIdeal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ResidueConjugatePlaceHermitianFormAdjoint
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
import Formalism.LocalToGlobal.IndefiniteReal.AutomorphicEvaluation
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead


theorem _root_.GlobalTheory.T.residue_conjugatePlace_hermitianForm_adjoint : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (PP : Pl D.host.E) (κ : GA D (Yc D 0)) (x y : Fin (Yc D 0).rank → EAf D), (GlobalTheory.SeeConjChar.hT X h x (Matrix.mulVec (finE (Yc D 0) κ).val y) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔ GlobalTheory.SeeConjChar.hT X h y (Matrix.mulVec ((finE (Yc D 0) κ)⁻¹).val x) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) ∧ GlobalTheory.SeeConjChar.resT (GlobalTheory.IdemSupport.cP PP) (GlobalTheory.SeeConjChar.hT X h x (Matrix.mulVec (finE (Yc D 0) κ).val y)) = GlobalTheory.SeeConjChar.conjRes PP (GlobalTheory.SeeConjChar.resT PP (GlobalTheory.SeeConjChar.hT X h y (Matrix.mulVec ((finE (Yc D 0) κ)⁻¹).val x))) := by
  first | exact @GlobalTheory.SeeConjAdj.resCP_adjoint | exact GlobalTheory.SeeConjAdj.resCP_adjoint | (intros; apply GlobalTheory.SeeConjAdj.resCP_adjoint <;> assumption)
