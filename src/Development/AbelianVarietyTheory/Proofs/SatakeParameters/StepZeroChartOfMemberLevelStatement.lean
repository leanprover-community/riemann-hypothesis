module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ReadsMove
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepZeroChartOfMemberLevel
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

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.stepZeroChart_of_memberLevel : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClsTied (D := (I.rec7 l Z)) u 0 (Nat.zero_le _)) (κ : (I.stp u I.mu0 0).Cl → K.lev.U), (∀ c s, (K.stabI c s).1 = (I.stp u I.mu0 0).gam c.1 s.1) → ∃ K0 : Fam I l Z u a 0 (Nat.zero_le _) (badQ (I.rec7 l Z) Q) (fun _ => ()), (K0 ()).lev.Lb = K.lev.Lb ∧ (K0 ()).lev.Uloc = K.lev.Uloc ∧ (K0 ()).lev.U = K.lev.U ∧ (∀ (x : (K0 ()).lev.U) (x' : K.lev.U), x.1 = x'.1 → (K0 ()).lev.chi x = K.lev.chi x') ∧ (∀ c, ((K0 ()).y ⟨I.eCls0 l u a c, rfl⟩).1 = (K.y c).1 * (κ c).1) ∧ ∀ c s, ((K0 ()).stabI c s).1 = (I.stp u a 0).gam c.1.1 s.1 := by
  first | exact @GlobalTheory.TwU.AtTrue.ZeroChart.chart_of_member | exact GlobalTheory.TwU.AtTrue.ZeroChart.chart_of_member | (intros; apply GlobalTheory.TwU.AtTrue.ZeroChart.chart_of_member <;> assumption)
