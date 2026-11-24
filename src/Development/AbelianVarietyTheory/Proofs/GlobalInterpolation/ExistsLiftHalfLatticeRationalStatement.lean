module

public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TranslateMomentsAll
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsLiftHalfLatticeRational
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

theorem _root_.GlobalTheory.T.exists_lift_halfLattice_rational : ∀ (X : Fields) (A : Amb X) (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 X.E))) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (cA c : ℕ), A.AA.FG → A.AA ≠ ⊥ → (∀ P ∈ S, conjPrime₂ P ∉ S) → A.AAUnit S → IsSdLat N → IsSdLat N' → 0 < cA → 0 < c → ∀ x ∈ divLat cA (homAt S N N'), ∃ t ∈ halfAO S (per A N N') (cA * c), t - x ∈ mulLat c (homAt S N N') := by
  first | exact @GlobalTheory.MomT.exists_lift_halfAO | exact GlobalTheory.MomT.exists_lift_halfAO | (intros; apply GlobalTheory.MomT.exists_lift_halfAO <;> assumption)
