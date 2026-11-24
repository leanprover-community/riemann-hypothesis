module

public import Formalism.LocalToGlobal.GroupLattices.Joint0
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemberRepresentativeMovedAtTwistEqTupleFrames
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ReadsMove

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.memberRepresentative_moved_at_twist_eq_tupleFrames : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) {Ch0 : ℕ → Type} {chOf0 : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch0 i} (F : FormsTiedSym (I.rec7 l Z) u Ch0 chOf0) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))), (∀ v, v ∈ Q ↔ I.UnderQ a v) → I.StdF l Z u F → ∀ (k : GA B (B.R.N 0)), I.Reads u I.mu0 0 (fun _ => ()) (fun _ => F.to0.cls0.lev.Lb) (fun _ => F.to0.cls0.lev.U) (fun _ => F.to0.cls0.lev.chi) (fun c => (F.to0.cls0.y c).1) (fun c s => (F.to0.cls0.stabI c s).1) (fun _ => k) → ∀ c, ∃ κ : F.to0.cls0.lev.U, (∀ v, v ∉ Q → bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) ∧ F.to0.cls0.lev.chi κ = 1 ∧ PtOf (B := B) ((show GA B (B.R.N 0) from (F.to0.cls0.y c).1 * κ.1) * k) (extTo I.SQ ((I.stp u a 0).rep (I.eCls0 l u a c)).1.1) := by
  first | exact @GlobalTheory.Mem.Col2.ZeroMove.main | exact GlobalTheory.Mem.Col2.ZeroMove.main | (intros; apply GlobalTheory.Mem.Col2.ZeroMove.main <;> assumption)
