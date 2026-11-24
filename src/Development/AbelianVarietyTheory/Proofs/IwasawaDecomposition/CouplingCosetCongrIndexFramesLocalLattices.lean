module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
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

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.UG.P Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix

namespace GlobalTheory.Mem.Col2

theorem cosetIn_congr : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ} (p p' : PtAt R sel mu cst u j), p.1.2 = p'.1.2 → p.1.1.fr = p'.1.1.fr → (∀ w : Pr.vGs, localization₂ w.1.asIdeal p.1.1.deco.1.N = localization₂ w.1.asIdeal p'.1.1.deco.1.N ∧ p.1.1.deco.1.be w = p'.1.1.deco.1.be w) → cosetIn p = cosetIn p' := by
  intro X Pr R sel S mu cst u j p p' h2 hfr hloc
  have hF : ∀ P, frsF sel mu p.1.1 P = frsF sel mu p'.1.1 P := by
    intro P
    unfold frsF
    split_ifs with h
    · have e1 := (hloc ⟨P.1, h⟩).1
      have e2 := (hloc ⟨P.1, h⟩).2
      unfold Deco.liftFr Deco.at
      rw [e1, e2]
    · rw [hfr]
  funext P
  unfold cosetIn
  rw [h2, hF P]

end GlobalTheory.Mem.Col2
