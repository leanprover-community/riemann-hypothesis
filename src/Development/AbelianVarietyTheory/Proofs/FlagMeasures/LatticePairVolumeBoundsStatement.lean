module

public import Formalism.HarderNarasimhan.StatementPl
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DifferentSmulMemOfTraceIntegral
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HilbertSchmidtLowerBoundInverseDifferent
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticeCoveringOfTraceDualLowerBoundStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticePairVolumeBounds
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DualPl
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.SizeWindowBrackets.ChainSlopeWindows.ExistsNsmulMem
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Formalism.HermitianLattices.StatementLat

@[expose] public section

open Formalism.HN Formalism.HermitianLatticesTheory Matrix NumberField Finset
open GlobalTheory.HomCover in

theorem _root_.GlobalTheory.T.lattice_pair_volume_bounds :
    ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (a b : ℕ)
      (X : InfinitePlace K → Matrix (Fin a) (Fin a) ℂ)
      (X' : InfinitePlace K → Matrix (Fin b) (Fin b) ℂ)
      (A : Submodule (𝓞 K) (Fin a → K)) (B : Submodule (𝓞 K) (Fin b → K)) (lo hi : ℝ),
      (∀ w, IsUnit (X w).det) → (∀ w, IsUnit (X' w).det) → A.FG → B.FG →
      Submodule.span K (A : Set (Fin a → K)) = ⊤ →
      Submodule.span K (B : Set (Fin b → K)) = ⊤ → 0 < lo → 0 < hi →
      (∀ N, N ≤ A → N ≠ ⊥ → lo ≤ Formalism.HN.size (Pi.basisFun K (Fin a)) X N) →
      Formalism.HN.largestSize (Pi.basisFun K (Fin b)) X' B ≤ hi →
      ∀ T : InfinitePlace K → Matrix (Fin b) (Fin a) ℂ,
        ∃ φ : Matrix (Fin b) (Fin a) K, (∀ y ∈ A, φ *ᵥ y ∈ B) ∧
          Real.sqrt (∑ w, ∑ i, ∑ j, ‖(T w - (X' w)⁻¹ * φ.map w.embedding * X w) i j‖ ^ 2) ≤
            (a : ℝ) * b * Real.sqrt (Formalism.HN.nPl K) *
              |(discr K : ℝ)| ^ ((1 : ℝ) / (2 * (Formalism.HN.nPl K : ℝ))) * hi / (2 * lo) := by
  apply _root_.GlobalTheory.HomCover.exists_hom_near <;> assumption
