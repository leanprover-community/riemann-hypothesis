module

public import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.FourierColumnIndicator
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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

@[expose] public section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.IndefiniteRowSideFullHecke.FourierColumnIndicator

noncomputable section

namespace GlobalTheory.LastSteps

def ChainDataGuarded : Prop :=
  ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S)
    (cst : LocCst X (rowSG Pr sel mu)) (m2 : ℕ), Pr.Ok → cst.Ok → R.m = m2 + 2 →
    ∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs →
      (∀ hal ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) m2 P.1), SplitAt Ch sel mu cst m2 P hal) ∧
      (∀ f : Sp X.E (R.N (m2 + 1)) → X.K, ColFn P.1 f → DualFn P.1 (fhat sel mu cst P f)) ∧
      (∀ f : Sp X.E (R.N (m2 + 1)) → X.K, ColFn P.1 f → FnMod P.1 (topDatum Ch sel mu cst m2 P f)) ∧
      (∀ (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (al : L.β m2),
        L.h m2 al P ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) m2 P.1) →
        ∀ (u : Pr.Word) (p₀ : ChPt (R := R) sel mu u m2) (p : ChPt (R := R) sel mu u (m2 + 1)),
        ∀ Y ∈ ybSet sel mu cst p.deco.1.N,
          FnModAt P.1 p₀.deco.1.N p.deco.1.N (facPen Ch sel mu cst L m2 al p₀ p Y P)) ∧
      (∀ (u : Pr.Word), (∀ w : rowSG Pr sel mu, Pr.piT u ∉ w.1.asIdeal) →
        ∀ (p : ChPt (R := R) sel mu u (m2 + 1)) (d : RowPt Pr R sel mu),
        ∀ Y ∈ ybSet sel mu cst p.deco.1.N,
          FnModAt P.1 p.deco.1.N (tilQ sel mu u d).1.N (facTop Ch sel mu cst m2 p Y d P))

end GlobalTheory.LastSteps
