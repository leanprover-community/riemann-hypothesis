module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ReadsMove
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunKilled
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InclMulInvMul
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartsReadingStepMoveBasePointsOneOffLevelPrimeStatement
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar



theorem GlobalTheory.TwU.AtTrue.charts_funKilled_one : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 B.host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K0 : Fam I l Z u a i hi bad chOf), I.ReadsK l Z u a i hi chOf K0 → (∀ β, ∃ n : ℕ, 0 < n ∧ ∀ κ, (K0 β).lev.chi κ ^ n = 1) → ∃ Kc : Fam I l Z u a i hi bad chOf, ReadsOne I l Z u a i hi chOf Kc ∧ ∀ β, FunKilled (Kc β).lev (X.piT u) ∧ ∃ n : ℕ, 0 < n ∧ ∀ κ, (Kc β).lev.chi κ ^ n = 1 := by
  intro B X I hI hP l Z u a i hi bad Ch chOf K0 hK hfin
  obtain ⟨K', hK', hprop⟩ := TC.charts_funKilled I hI hP l Z u a i hi bad Ch chOf K0 hK
  obtain ⟨k, hk⟩ := GlobalTheory.T.chartsReadingStep_moveBasePoints_one_offLevelPrime I hI hP l Z u a i hi bad Ch chOf K' hK'
  refine ⟨fun β => moveChart (K' β) (k β), hk, fun β => ⟨(hprop β).1, ?_⟩⟩
  obtain ⟨hF, -, -, hU, hchi, -, -⟩ := hprop β
  obtain ⟨n, hn, hn'⟩ := hfin β
  refine ⟨n, hn, fun κ => ?_⟩
  have hm : (k β).1 * κ.1 * (k β).1⁻¹ ∈ (K0 β).lev.U := hU ▸ κ.2
  show ((K' β).lev.chi ⟨(k β).1 * κ.1 * (k β).1⁻¹, κ.2⟩) ^ n = 1
  have e := hchi ⟨(k β).1 * κ.1 * (k β).1⁻¹, κ.2⟩ ⟨_, hm⟩ rfl
  exact e.symm ▸ hn' _
