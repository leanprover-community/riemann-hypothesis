module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCliff
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.IsCoreMod
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParthasarathyRaoVaradarajan
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

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount

theorem _root_.GlobalTheory.T.parthasarathy_rao_varadarajan : ∀ n : ℕ, ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (c : Fin n → Fin n → Matrix ι ι ℂ), IsCliff c ∧
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (Kf : Fin n → Fin n → Module.End ℂ V)
      (S : Submodule ℂ V) (ν : Fin n → ℤ) (v : V), Formalism.REAL.GlRel Kf →
      (∀ a b (x y : V), ⟪Kf a b x, y⟫_ℂ = ⟪x, Kf b a y⟫_ℂ) → FiniteDimensional ℂ S → (∀ a b, ∀ w ∈ S, Kf a b w ∈ S) →
      v ∈ S → v ≠ 0 → Formalism.REAL.KHighest (fun _ => true) Kf (wtR ν) v →
      ∃ w : Equiv.Perm (Fin n), Antitone (fun a => wtR ν (w a) - rhoV n (w a)) ∧ ∃ x : ι → V, x ≠ 0 ∧
        Formalism.REAL.KHighest (fun _ => true) (yF Kf c) (fun a => wtR ν (w a) - rhoV n (w a)) x := by
  first | exact @GlobalTheory.CompanionTheory.SpinPRV.spin_parthasarathy_rao_varadarajan | exact GlobalTheory.CompanionTheory.SpinPRV.spin_parthasarathy_rao_varadarajan | (intros; apply GlobalTheory.CompanionTheory.SpinPRV.spin_parthasarathy_rao_varadarajan <;> assumption)
