module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ReadsMove
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunKilled
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartLastStepTwistBasePointStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartsRebasedOneOffLevelPrimeKilledStatement
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

noncomputable section

namespace GlobalTheory.TwU.AtTrue



theorem chart_last_good : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) {Ch0 : ℕ → Type} {chOf0 : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch0 i} (F : FormsTiedSym (I.rec7 l Z) u Ch0 chOf0) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))), (∀ v, v ∈ Q ↔ I.UnderQ a v) → I.StdF l Z u F → ∃ (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u a B.R.m).Cl → Ch) (Kc : Fam I l Z u a B.R.m le_rfl (badQ (I.rec7 l Z) Q) chOf), ReadsOne I l Z u a B.R.m le_rfl chOf Kc ∧ ∀ β, FunKilled (Kc β).lev (X.piT u) ∧ ∃ n : ℕ, 0 < n ∧ ∀ κ, (Kc β).lev.chi κ ^ n = 1 := by
  intro B X I hI hP l Z u Ch0 chOf0 F a Q hQ hF
  obtain ⟨K1, hR, -, -, hfin, -⟩ := GlobalTheory.T.chart_lastStep_twistBasePoint I hI hP l Z u a Q (F.cls B.R.m le_rfl (Or.inr rfl)) hQ
    (hF.ends B.R.m le_rfl (Or.inr rfl))
  obtain ⟨k, hk, -⟩ := hR
  obtain ⟨Kc, h1, h2⟩ := GlobalTheory.T.charts_rebased_one_off_levelPrime_killed I hI hP l Z u a B.R.m le_rfl (badQ (I.rec7 l Z) Q) Unit (fun _ => ()) K1 ⟨k, hk⟩
    (fun β => by cases β; exact hfin)
  exact ⟨Unit, inferInstance, fun _ => (), Kc, h1, h2⟩

end GlobalTheory.TwU.AtTrue

end
