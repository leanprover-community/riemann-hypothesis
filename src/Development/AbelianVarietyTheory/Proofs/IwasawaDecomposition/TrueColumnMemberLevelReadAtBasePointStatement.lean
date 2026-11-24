module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NeZeroTop
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Formalism.LocalToGlobal.Columns.RecLevel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnMemberLevelReadAtBasePoint
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

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.trueColumn_member_level_read_at_base_point : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → Pins B X → ∀ (l : I.Laws) (Z : Later B (I.cols l)) (u : B.Word) (a : I.ι) (K : ClsTied (D := (I.rec7 l Z)) u B.R.m le_rfl) (k : Unit → GA B (B.R.N B.R.m)), I.Reads u I.mu0 B.R.m (fun _ => ()) (fun _ => K.lev.Lb) (fun _ => K.lev.U) (fun _ => K.lev.chi) (fun c => (K.y c).1) (fun c s => (K.stabI c s).1) k → let U : Subgroup (GA B (B.R.N B.R.m)) := K.lev.U; let Lb : Submodule (𝓞 B.host.E) (Fin (B.R.N B.R.m) → B.host.E) := K.lev.Lb; let chi : U →* ℂˣ := K.lev.chi; (∀ x ∈ UAd B.sp.cm (B.R.N B.R.m), x ∈ U ↔ (k ())⁻¹ * x * k () ∈ levU B.sp.cm (B.R.N B.R.m) ((B.primes X).vT u) (B.primes X).vGs ((I.Tp a).levG B.R.m).grp) ∧ (∀ (x : U) (z : J0 B.sp.cm (B.R.N B.R.m) ((B.primes X).vT u)) (h : ((I.Tp a).levG B.R.m).grp), z.1 = (k ())⁻¹ * x.1 * k () → redG B.sp.cm (B.R.N B.R.m) ((B.primes X).vT u) (B.primes X).vGs z = h.1⁻¹ → chi x = Units.map (B.embLL : B.LL →* ℂ) (((I.Tp a).levG B.R.m).chr h)) ∧ ∀ x : Fin (B.R.N B.R.m) → B.host.E ⊗[B.host.F] FiniteAdeleRing (𝓞 B.host.F) B.host.F, x ∈ latS (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F) (tensInt (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F) (intOE B.host.E) (intAd B.host.F)) Lb ↔ ((k ())⁻¹ : GL (Fin (B.R.N B.R.m)) (AfE B.host.F B.host.E)).1 *ᵥ x ∈ latS (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F) (tensInt (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F) (intOE B.host.E) (intAd B.host.F)) (baseLb B.host.E (B.R.N B.R.m) ((B.primes X).vT u)) := by
  first | exact @GlobalTheory.Mem.Col2.TopCh.kread_member | exact GlobalTheory.Mem.Col2.TopCh.kread_member | (intros; apply GlobalTheory.Mem.Col2.TopCh.kread_member <;> assumption)
