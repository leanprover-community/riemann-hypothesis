module

public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ParabolicSubgroupEquality
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FiniteNetOfGradedProjections
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

open Matrix
open CompanionTheory.RgExh.Dec (IsGrad)
open GlobalTheory.CompanionTheory.PSubFlag (Pm Pp)

theorem _root_.GlobalTheory.T.finite_net_of_graded_projections :
    ∀ (n : ℕ) (ε : Fin n → Bool),
      ∃ (m : ℕ) (A : Fin m → Matrix (Fin n) (Fin n) ℂ), (∀ j, IsGrad ε (A j)) ∧
        ∀ A' : Matrix (Fin n) (Fin n) ℂ, IsGrad ε A' →
          ∃ j, Formalism.REAL.hs (Pm (A j) - Pm A') ≤ 1 / 4 ∧
            Formalism.REAL.hs (Pp (A j) - Pp A') ≤ 1 / 4 :=
  GlobalTheory.CompanionTheory.UGeo.GradNet.exists_net
