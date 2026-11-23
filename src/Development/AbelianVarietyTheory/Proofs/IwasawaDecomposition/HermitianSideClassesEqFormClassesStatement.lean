module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianSideClassesEqFormClasses
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

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.hermitianSide_classes_eq_formClasses : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∀ u, ∃ (lattice₂ : ((I.rec7 l Z).fm u).clsP → Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).sp.X'.V) (levP : Formalism.L2.Herm.StepLevel0 (I.rec7 l Z).sp.cm (I.rec7 l Z).sp.X' (I.rec7 l Z).host.g (Formalism.L2.Herm.crdLat (I.rec7 l Z).sp.X' (I.rec7 l Z).sp.X'.L0)) (clsP : Formalism.L2.Herm.ClassTie (I.rec7 l Z).sp.cm (I.rec7 l Z).sp.X' (Formalism.L2.Herm.crdLat (I.rec7 l Z).sp.X' (I.rec7 l Z).sp.X'.L0) levP.U ((I.rec7 l Z).fm u).stabilizer₂ lattice₂), SameCar (rankP (I.rec7 l Z)) (Formalism.L2.Herm.crdLat (I.rec7 l Z).sp.X' (I.rec7 l Z).sp.X'.L0) (F u).clsP.lev.Lb levP.Uloc (F u).clsP.lev.Uloc levP.U (F u).clsP.lev.U (fun c => (clsP.y c).1) (fun c => ((F u).clsP.y c).1) (fun c s => (clsP.stabI c s).1) (fun c s => ((F u).clsP.stabI c s).1) ∧ ∀ c, (F u).clsP.lat c = (lattice₂ c).map ((crdP (I.rec7 l Z) : (I.rec7 l Z).sp.X'.V →ₗ[(I.rec7 l Z).host.E] (Fin ((I.rec7 l Z).R.N (I.rec7 l Z).R.m - 1) → (I.rec7 l Z).host.E)).restrictScalars (𝓞 (I.rec7 l Z).host.E)) := by
  first | exact @GlobalTheory.Mem.Col2.HAt.clsP_hermitian | exact GlobalTheory.Mem.Col2.HAt.clsP_hermitian | (intros; apply GlobalTheory.Mem.Col2.HAt.clsP_hermitian <;> assumption)
