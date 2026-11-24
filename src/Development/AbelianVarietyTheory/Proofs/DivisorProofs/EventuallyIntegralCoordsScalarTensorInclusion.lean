module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntCZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
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
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical

noncomputable section
namespace GlobalTheory.FinClsLoc
open IsDedekindDomain

theorem ratAdicInt_eventually (q : ℚ) :
    ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite,
      algebraMap ℚ (v.adicCompletion ℚ) q ∈ v.adicCompletionIntegers ℚ := by
  have h := (algebraMap ℚ (FiniteAdeleRing ℤ ℚ) q).2
  filter_upwards [h] with v hv
  exact hv

theorem intC_inC_eventually : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (c : G.C), ∀ᶠ w : AwayP p in Filter.cofinite,
    IntC G w (inC G (w.1.adicCompletion ℚ) c) := by
  intro p _ G c
  have hall : ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite, ∀ i : Fin (Module.finrank ℚ G.C),
      algebraMap ℚ (v.adicCompletion ℚ) ((Module.finBasis ℚ G.C).repr c i) ∈ v.adicCompletionIntegers ℚ :=
    Filter.eventually_all.2 fun i => ratAdicInt_eventually _
  have ht : Filter.Tendsto (Subtype.val : AwayP p → HeightOneSpectrum ℤ) Filter.cofinite Filter.cofinite :=
    Subtype.val_injective.tendsto_cofinite
  filter_upwards [ht.eventually hall] with w hw
  intro i
  have : coordL G w (inC G (w.1.adicCompletion ℚ) c) i =
      algebraMap ℚ (w.1.adicCompletion ℚ) ((Module.finBasis ℚ G.C).repr c i) := by
    have e : inC G (w.1.adicCompletion ℚ) c = (1 : w.1.adicCompletion ℚ) ⊗ₜ[ℚ] c := rfl
    rw [coordL, e, Algebra.TensorProduct.basis_repr_tmul, one_smul, Finsupp.mapRange_apply]
  rw [this]; exact hw i

end GlobalTheory.FinClsLoc
