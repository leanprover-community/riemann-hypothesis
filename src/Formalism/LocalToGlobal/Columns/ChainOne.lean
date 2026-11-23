module

public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section One

variable {X : Fields} {Pr : Primes X} {R : Ranks}

def oneIdx (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs) (Q : Finset (HeightOneSpectrum (𝓞 X.E))) (m2 : ℕ) : ChIdx X Pr R Q where
  β j := {_u : Unit // j ≤ m2 + 1}
  h _ _ _ := 1
  levG j _ := Λ j
  levQ j _ := LevQFam.top X.E X.K (R.N j) Q

variable (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs)


open Classical in
def OneYbSym (m2 : ℕ) : Prop :=
  ∀ (P : rowSG Pr sel mu), P.1 ∈ Pr.vGs → ∀ (x₀ : HomE X.E (R.N m2) (R.N (m2 + 1))) (y' : Sp X.E (R.N (m2 + 1))),
    PsiAt Ch sel mu cst m2 P 1 x₀ y' ≠ 0 →
      ∀ l : Fin (R.N (m2 + 1)), IntAt P.1 ((qOf P.1 : X.E) * y' l) ∧ redP P.1 ((qOf P.1 : X.E) * y' l) = if l.1 = R.k then 1 else 0

variable {Ch sel mu cst Λ}

end One

end Formalism.L2.Col
