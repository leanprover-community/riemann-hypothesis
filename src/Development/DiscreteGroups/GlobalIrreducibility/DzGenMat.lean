module

public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.NotIsGenericDetRepTwo

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.Whittaker GlobalTheory.SplitWeil ValuativeRel Matrix

namespace DiscreteGroups.sglob.DzType


variable {R : Type} [CommRing R] {m : ℕ}


section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {m : ℕ}

theorem det_unip {u : GL (Fin m) k} (hu : u ∈ unipB k (Fin m)) : (u : Matrix (Fin m) (Fin m) k).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (fun i j hij => ((mem_unipB _).1 hu).1 i j hij)]
  simp [((mem_unipB _).1 hu).2]

theorem mem_KO_of_unip {u : GL (Fin m) k} (hu : u ∈ unipB k (Fin m))
    (h : ∀ i j, valuation k ((u : Matrix (Fin m) (Fin m) k) i j) ≤ 1) : u ∈ KO k (Fin m) := by
  rw [GlobalTheory.SplitFlip.mem_KO_iff]
  refine ⟨fun i j => (Valuation.mem_integer_iff _ _).2 (h i j), fun i j => ?_⟩
  have hinv : ((u⁻¹ : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) = (u : Matrix (Fin m) (Fin m) k).adjugate := by
    rw [Matrix.coe_units_inv, Matrix.inv_def, det_unip hu, Ring.inverse_one, one_smul]
  let A : Matrix (Fin m) (Fin m) 𝒪[k] := fun i j => ⟨(u : Matrix (Fin m) (Fin m) k) i j,
    (Valuation.mem_integer_iff _ _).2 (h i j)⟩
  have hA : (algebraMap 𝒪[k] k).mapMatrix A = (u : Matrix (Fin m) (Fin m) k) := by ext i j; rfl
  show ((u⁻¹ : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) i j ∈ 𝒪[k]
  rw [hinv, ← hA, ← RingHom.map_adjugate]
  exact (A.adjugate i j).2

end Local

end DiscreteGroups.sglob.DzType
