module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomMapApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOrientedVacuumIsometryMovedLattices
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.isOrientedVacuum_isometry_moved_lattices : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : Formalism.IndefR.Datum.InfFam D) (ε : Bool) {S S' T T' : HSp D} (IS : GlobalTheory.Mem.Isom.IsoMat S S') (IT : GlobalTheory.Mem.Isom.IsoMat T T') (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (LS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f : WO S T → ℂ),
  IsVacO ψ θ (GlobalTheory.Grid.sgn ε S) T (fun τ => GlobalTheory.Grid.sgnM ε (sS τ)) sT LS LT f →
  IsVacO ψ θ (GlobalTheory.Grid.sgn ε S') T' (fun τ => GlobalTheory.Grid.sgnM ε (GlobalTheory.TriMove.cartMove (S' := S') IS τ (sS τ))) (fun τ => GlobalTheory.TriMove.cartMove (S' := T') IT τ (sT τ)) (GlobalTheory.TriMove.latMove (S' := S') IS LS) (GlobalTheory.TriMove.latMove (S' := T') IT LT) (GlobalTheory.TriMove.trH (S := S) (S' := S') (T := T) (T' := T') IS IT f) := by
  first | exact @GlobalTheory.VacMove.isVacO_move | exact GlobalTheory.VacMove.isVacO_move | (intros; apply GlobalTheory.VacMove.isVacO_move <;> assumption)
