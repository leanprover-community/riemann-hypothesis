module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CommutativeHeckeActsByScalarOnFixedVectors
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

open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun

theorem _root_.GlobalTheory.T.commutative_hecke_acts_by_scalar_on_fixed_vectors : ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V) (K : Subgroup G), IsCompact (K : Set G) → IsCommensurated K → (∀ f₁ ∈ Hecke ℂ K, ∀ f₂ ∈ Hecke ℂ K, conv K f₁ f₂ = conv K f₂ f₁) → GlobalTheory.LGrp.IsIrrSmooth π → FiniteDimensional ℂ (fixed π K) → ∀ h ∈ Hecke ℂ K, ∃ c : ℂ, ∀ x ∈ fixed π K, heckeVec π K h x = c • x := by
  first | exact @GlobalTheory.LFun.HeckeScalar.exists_scalar | exact GlobalTheory.LFun.HeckeScalar.exists_scalar | (intros; apply GlobalTheory.LFun.HeckeScalar.exists_scalar <;> assumption)
