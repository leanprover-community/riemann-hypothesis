module

public import Formalism.HarderNarasimhan.StatementPl
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SizeMu
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.HermitianLattices.StatementLat
import Formalism.LocalToGlobal.GlobalTheory.HLatOps
import Formalism.LocalToGlobal.LatticeGeometry.OperatorNormFibers.StExtInv
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

open Module NumberField TensorProduct

noncomputable section

namespace Formalism.L2.Geo.ExtensionFiltration.ExtInvMu

open Formalism.BasicNotions Formalism.HN Formalism.HermitianLatticesTheory Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.L2.Geo.ExtensionFiltration.ExtInvSk

section Places

variable (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']


open Classical in
theorem card_fiber [_root_.NumberField.IsTotallyComplex K] (v : InfinitePlace K) :
    (Finset.univ.filter fun v' : InfinitePlace K' => v'.comap (algebraMap K K') = v).card =
      finrank K K' := by
  classical
  have h := InfinitePlace.unramifedPlacesOver_ncard_add_eq_finrank K' v
  have h0 : InfinitePlace.ramifiedPlacesOver K' v = ∅ := by
    ext w
    simp only [InfinitePlace.ramifiedPlacesOver, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
      iff_false]
    rintro ⟨_, hw⟩
    exact InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex _)
      (InfinitePlace.isRamified_iff.1 hw).2
  have h1 : InfinitePlace.unramifiedPlacesOver K' v =
      ((Finset.univ.filter fun v' : InfinitePlace K' => v'.comap (algebraMap K K') = v :
        Finset (InfinitePlace K')) : Set (InfinitePlace K')) := by
    ext w
    simp only [InfinitePlace.unramifiedPlacesOver, Set.mem_ofPred_eq, Finset.coe_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hw, _⟩
      exact InfinitePlace.LiesOver.comap_eq w v
    · rintro rfl
      refine ⟨⟨?_⟩, ?_⟩
      · ext x
        rfl
      · by_contra hr
        exact InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex _)
          (InfinitePlace.isRamified_iff.1 hr).2
  rw [h0, h1, Set.ncard_empty, mul_zero, add_zero, Set.ncard_coe_finset] at h
  exact h

theorem nPl_ext [_root_.NumberField.IsTotallyComplex K] [_root_.NumberField.IsTotallyComplex K'] : nPl K' = finrank K K' * nPl K := by
  have h1 := sizeMu_finrank_eq K
  have h2 := sizeMu_finrank_eq K'
  have h3 := Module.finrank_mul_finrank ℚ K K'
  rw [h1, h2] at h3
  linarith

end Places

end Formalism.L2.Geo.ExtensionFiltration.ExtInvMu
