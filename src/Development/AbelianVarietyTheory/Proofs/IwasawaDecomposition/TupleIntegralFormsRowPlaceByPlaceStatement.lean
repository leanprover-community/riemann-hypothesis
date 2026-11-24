module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EWtApply
public import Formalism.LocalToGlobal.HermitianForms.TiedTwP
public import Formalism.LocalToGlobal.HermitianForms.TiedTwPGen
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupleIntegralFormsRowPlaceByPlace
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

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.tuple_integralForms_row_place_by_place : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (I.fm l u a) (badQ (I.rec7 l Z) Q)), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ v ∈ Q, ((((I.rec7 l Z).mem u).A.T : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal ∧ ∀ j, ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal) → I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → ∀ w, Formalism.L2.Forms.okPT (I.rec7 l Z) Q ((I.rec7 l Z).mem u).A.T w → ∀ x : (I.fm l u a).ptLat.V, x ∈ (I.fm l u a).SP w ↔ ∀ (c : (I.fm l u a).clsP) (Bm : GL (Fin ((I.rec7 l Z).R.N (I.rec7 l Z).R.m - 1)) (I.rec7 l Z).host.E), IsLocBasis ((I.rec7 l Z).what₂.places.resChar w) (K.lat c : Set _) Bm → ∃ Pc ∈ IntSpan (I.rec7 l Z) w (I.fm l u a).sg, GlobalTheory.Mem.Col2.TwP.eWt I l Z u a ((I.fm l u a).ptEmb x) c = fnOf _ (shiftOf (sgTG (I.fm l u a))) (atInf (Formalism.L2.Forms.embT (I.rec7 l Z)) (Bm⁻¹ : GL (Fin ((I.rec7 l Z).R.N (I.rec7 l Z).R.m - 1)) (I.rec7 l Z).host.E).1) Pc := by
  first | exact @GlobalTheory.Mem.Col2.TC.tw_lat_at | exact GlobalTheory.Mem.Col2.TC.tw_lat_at | (intros; apply GlobalTheory.Mem.Col2.TC.tw_lat_at <;> assumption)
