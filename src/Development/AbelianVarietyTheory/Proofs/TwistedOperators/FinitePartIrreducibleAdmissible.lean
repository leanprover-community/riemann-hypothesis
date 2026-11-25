module

public import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Formalism.SharpRestriction.Divisibility.KudlaSiegelWeil
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicUnitaryClosureLocalComponentsOpen
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsFactorisationCuspidal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalFixed
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IrreducibleUnitaryRepEqFiniteSmoothPartTensorDisStatement
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Formalism.LocalRingCardinality.DataHost
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.Nat.Choose.Multinomial
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.Definitions.Foundations.InnerEqZeroOfNotUEquiv
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHilbertSchmidtOfFiniteDimensional
import Development.AbelianVarietyTheory.Definitions.Foundations.MeasurePreservingRmulQuotMeas
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyAlgebraMapMemIntegers
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsOpenIsCompactLevelOffFinEmpty

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesFactorLocalStable, Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesFactorLocalStableStatement, Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFinsetSumTranslatesFixedCompactSubgroup, Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFinsetSumTranslatesFixedCompactSubgroupStatement, Development.AbelianVarietyTheory.Proofs.TwistedOperators.FactorisableRestrictedTensorLevel, Development.AbelianVarietyTheory.Proofs.TwistedOperators.FactorisableRestrictedTensorLevelStatement, Development.AbelianVarietyTheory.Proofs.TwistedOperators.SpanValuesDenseFinitePartSubrep, Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinitePartIrreducibleAdmissible

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesFactorLocalStable =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesFactorLocalStable", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\npublic import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData\nimport Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec\n\n"}
section -- clump:auto
@[expose] public section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace
open Formalism.MainNotions.KudlaSiegelWeil (Restr)

noncomputable section

namespace GlobalTheory.PureDS

section Comb

variable {α β ι : Type} {Hs : α ⊕ β → Type} {E : ι → Type}

open Classical in
def comb (p : ι → α) (A : ∀ i, E i → Hs (.inl (p i))) (y0 : ∀ v, Hs v) (z : ∀ i, E i) : ∀ v, Hs v
  | .inl a => if h : ∃ i, p i = a then cast (congrArg (fun a => Hs (.inl a)) h.choose_spec) (A h.choose (z h.choose))
      else y0 (.inl a)
  | .inr b => y0 (.inr b)

variable {p : ι → α} {A : ∀ i, E i → Hs (.inl (p i))} {y0 : ∀ v, Hs v} {z : ∀ i, E i}

end Comb

end GlobalTheory.PureDS

end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesFactorLocalStable =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesFactorLocalStableStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesFactorLocalStableStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff\npublic import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesFactorLocalStable\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\npublic import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData\nimport Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec\n\n"}
section -- clump:auto
@[expose] public section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace
open Formalism.MainNotions.KudlaSiegelWeil (Restr)

end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesFactorLocalStableStatement =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFinsetSumTranslatesFixedCompactSubgroup =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFinsetSumTranslatesFixedCompactSubgroup", "h": "module\n\npublic import Mathlib.Basic.Complex.Basic\npublic import Mathlib.RepresentationTheory.Basic\npublic import Mathlib.Topology.Algebra.Group.Defs\nimport Formalism.LocalRingCardinality.DataHost\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\npublic import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData\nimport Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec\nimport Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne\nimport Development.AbelianVarietyTheory.Definitions.Foundations.InnerEqZeroOfNotUEquiv\nimport Development.AbelianVarietyTheory.Definitions.Foundations.IsHilbertSchmidtOfFiniteDimensional\nimport Development.AbelianVarietyTheory.Definitions.Foundations.MeasurePreservingRmulQuotMeas\nimport Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull\npublic import Formalism.SharpRestriction.Divisibility.KudlaSiegelWeil\n\n"}
section -- clump:auto
@[expose] public section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace
open Formalism.MainNotions.KudlaSiegelWeil (Restr)

namespace GlobalTheory

theorem exists_finset_sum_translate_fixed {G X : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ G X)
    (K : Subgroup G) (hK : IsCompact (K : Set G)) (x : X) (hx : IsOpen {g | ρ g x = x}) :
    ∃ s : Finset G, (∀ g ∈ s, g ∈ K) ∧ s.Nonempty ∧
      ∀ k ∈ K, ρ k (∑ g ∈ s, ρ g x) = ∑ g ∈ s, ρ g x := by
  classical
  have hmul : ∀ (a b : G) (y : X), ρ (a * b) y = ρ a (ρ b y) := fun a b y => by
    rw [map_mul, Module.End.mul_apply]
  have hinv : ∀ (a : G) (y : X), ρ a⁻¹ (ρ a y) = y := fun a y => by
    rw [← hmul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hinv' : ∀ (a : G) (y : X), ρ a (ρ a⁻¹ y) = y := fun a y => by
    rw [← hmul, mul_inv_cancel, map_one, Module.End.one_apply]
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover
    (fun i : K => (fun g => (i : G)⁻¹ * g) ⁻¹' {g | ρ g x = x})
    (fun i => hx.preimage (continuous_const.mul continuous_id))
    (fun k hk => Set.mem_iUnion.2 ⟨⟨k, hk⟩, show ρ (k⁻¹ * k) x = x by
      rw [inv_mul_cancel, map_one, Module.End.one_apply]⟩)
  let F : Finset X := t.image (fun i : K => ρ (i : G) x)
  have hFmem : ∀ y, y ∈ F ↔ ∃ k ∈ K, ρ k x = y := by
    intro y
    constructor
    · intro hy
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hy
      exact ⟨i, i.2, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      obtain ⟨i, hi, hki⟩ := Set.mem_iUnion₂.1 (ht hk)
      refine Finset.mem_image.2 ⟨i, hi, ?_⟩
      have h1 : ρ ((i : G)⁻¹ * k) x = x := hki
      calc ρ (i : G) x = ρ (i : G) (ρ ((i : G)⁻¹ * k) x) := by rw [h1]
        _ = ρ k x := by rw [← hmul, mul_inv_cancel_left]
  let f : X → G := fun y => if h : ∃ k ∈ K, ρ k x = y then h.choose else 1
  have hf : ∀ y ∈ F, f y ∈ K ∧ ρ (f y) x = y := by
    intro y hy
    have h := (hFmem y).1 hy
    simp only [f, dif_pos h]
    exact h.choose_spec
  refine ⟨F.image f, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hg
    exact (hf y hy).1
  · exact Finset.Nonempty.image ⟨x, (hFmem x).2 ⟨1, K.one_mem, by
      rw [map_one, Module.End.one_apply]⟩⟩ f
  · have hsum : ∑ g ∈ F.image f, ρ g x = ∑ y ∈ F, y := by
      rw [Finset.sum_image]
      · exact Finset.sum_congr rfl (fun y hy => (hf y hy).2)
      · intro y hy y' hy' h
        rw [← (hf y hy).2, ← (hf y' hy').2]
        exact congrArg (fun g => ρ g x) h
    intro k hk

    rw [hsum, map_sum]
    refine Finset.sum_nbij' (fun y => ρ k y) (fun y => ρ k⁻¹ y) ?_ ?_ ?_ ?_ (fun _ _ => rfl)
    · intro y hy
      obtain ⟨k', hk', rfl⟩ := (hFmem y).1 hy
      exact (hFmem _).2 ⟨k * k', K.mul_mem hk hk', hmul _ _ _⟩
    · intro y hy
      obtain ⟨k', hk', rfl⟩ := (hFmem y).1 hy
      exact (hFmem _).2 ⟨k⁻¹ * k', K.mul_mem (K.inv_mem hk) hk', hmul _ _ _⟩
    · intro y _
      exact hinv k y
    · intro y _
      exact hinv' k y

end GlobalTheory
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFinsetSumTranslatesFixedCompactSubgroup =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFinsetSumTranslatesFixedCompactSubgroupStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFinsetSumTranslatesFixedCompactSubgroupStatement", "h": "module\n\npublic import Mathlib.Basic.Complex.Basic\npublic import Mathlib.RepresentationTheory.Basic\npublic import Mathlib.Topology.Algebra.Group.Defs\npublic import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFinsetSumTranslatesFixedCompactSubgroup\nimport Formalism.LocalRingCardinality.DataHost\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\npublic import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData\nimport Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec\nimport Development.AbelianVarietyTheory.Definitions.Foundations.InnerEqZeroOfNotUEquiv\n\n"}
section -- clump:auto
@[expose] public section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace
open Formalism.MainNotions.KudlaSiegelWeil (Restr)

end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFinsetSumTranslatesFixedCompactSubgroupStatement =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.TwistedOperators.FactorisableRestrictedTensorLevel =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.TwistedOperators.FactorisableRestrictedTensorLevel", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\npublic import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData\nimport Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec\n\n"}
section -- clump:auto
@[expose] public section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace
open Formalism.MainNotions.KudlaSiegelWeil (Restr)

namespace GlobalTheory.FixedSpan

def fixedSub {G X : Type} [Group G] [NormedAddCommGroup X] [InnerProductSpace ℂ X] (ρ : G →* (X →L[ℂ] X))
    (K : Subgroup G) : Submodule ℂ X := ⨅ k ∈ K, LinearMap.ker ((ρ k - 1 : X →L[ℂ] X) : X →ₗ[ℂ] X)

end GlobalTheory.FixedSpan
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.TwistedOperators.FactorisableRestrictedTensorLevel =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.TwistedOperators.FactorisableRestrictedTensorLevelStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.TwistedOperators.FactorisableRestrictedTensorLevelStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff\npublic import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FactorisableRestrictedTensorLevel\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\npublic import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData\nimport Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec\n\n"}
section -- clump:auto
@[expose] public section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace
open Formalism.MainNotions.KudlaSiegelWeil (Restr)

end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.TwistedOperators.FactorisableRestrictedTensorLevelStatement =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.TwistedOperators.SpanValuesDenseFinitePartSubrep =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.TwistedOperators.SpanValuesDenseFinitePartSubrep", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff\nimport Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyAlgebraMapMemIntegers\npublic import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicUnitaryClosureLocalComponentsOpen\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\npublic import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData\nimport Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace
open Formalism.MainNotions.KudlaSiegelWeil (Restr)

namespace GlobalTheory.TrFinDense

theorem span_values_dense : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : GA D V →* (H →L[ℂ] H)), IsIrrUnitary π → ∀ hU : IsSubrep π ⊤, ∀ N : Subrepresentation (finPartDSSm M hU), N ≠ ⊥ → (Submodule.span ℂ {z | ∃ Φ ∈ N.toSubmodule, ∃ y, z = ((Φ : homDS M π ⊤) : ContinuousMultilinearMap ℂ M.H H) y}).topologicalClosure = ⊤ := by
  intro D V S M H _ _ _ π hπ hU N hN
  classical
  set Sv : Set H := {z | ∃ Φ ∈ N.toSubmodule, ∃ y, z = ((Φ : homDS M π ⊤) : ContinuousMultilinearMap ℂ M.H H) y}
    with hSv
  set W : Submodule ℂ H := Submodule.span ℂ Sv with hW

  let Mon : Submonoid (GA D V) :=
    { carrier := {g | Sv ⊆ W.comap (π g : H →ₗ[ℂ] H)}
      mul_mem' := by
        intro a b ha hb z hz
        have hbz : π b z ∈ W := hb hz
        have : W ≤ W.comap (π a : H →ₗ[ℂ] H) := Submodule.span_le.2 ha
        show π (a * b) z ∈ W
        rw [map_mul]
        exact this hbz
      one_mem' := by
        intro z hz
        show π 1 z ∈ W
        rw [map_one]
        exact Submodule.subset_span hz }
  have hfin : ∀ g : GfC V, (g : GA D V) ∈ Mon := by
    rintro g _ ⟨Φ, hΦ, y, rfl⟩
    refine Submodule.subset_span ⟨finPartDSSm M hU g Φ, N.apply_mem_toSubmodule g hΦ, y, rfl⟩
  have hinf : ∀ w x, embW V w x ∈ Mon := by
    intro w x
    obtain ⟨τ, rfl⟩ := (placeOf_bijective D).2 w
    rintro _ ⟨Φ, hΦ, y, rfl⟩
    refine Submodule.subset_span ⟨Φ, hΦ, Function.update y τ (dsRep M τ x (y τ)), ?_⟩
    exact (((Φ : homDS M π ⊤).2).2 τ x y).symm
  haveI : Submodule.IsFullLattice D.host.E (stdLattice D.host.E V.rank) := isLattice_stdLattice
  have htop : Mon = ⊤ := GlobalTheory.PlaceGen.eq_top_of_local D.sp.cm.sig V.gram (stdLattice D.host.E V.rank) Mon ∅
    (fun v x => hfin (locFin V v x)) hinf (fun k hk => hfin ⟨k, (mem_levelOff.1 hk).1⟩)
  have hinvW : ∀ g, ∀ v ∈ W, π g v ∈ W := fun g v hv =>
    (Submodule.span_le.2 (show g ∈ Mon from htop ▸ trivial)) hv
  have hsub := isSubrep_topologicalClosure (π := π) hinvW
  rcases hπ.irred.2 _ hsub with h | h
  · exfalso
    obtain ⟨Φ, hΦ, hΦ0⟩ : ∃ Φ ∈ N.toSubmodule, Φ ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hN (Subrepresentation.toSubmodule_injective (eq_bot_iff.2 fun Φ hΦ => (Submodule.mem_bot ℂ).2 (hc Φ hΦ)))
    have : ((Φ : homDS M π ⊤) : ContinuousMultilinearMap ℂ M.H H) ≠ 0 := by
      intro e
      exact hΦ0 (Subtype.ext (Subtype.ext e))
    obtain ⟨y, hy⟩ : ∃ y, ((Φ : homDS M π ⊤) : ContinuousMultilinearMap ℂ M.H H) y ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact this (ContinuousMultilinearMap.ext hc)
    have hmem : ((Φ : homDS M π ⊤) : ContinuousMultilinearMap ℂ M.H H) y ∈ W.topologicalClosure :=
      W.le_topologicalClosure (Submodule.subset_span ⟨Φ, hΦ, y, rfl⟩)
    rw [h] at hmem
    exact hy ((Submodule.mem_bot ℂ).1 hmem)
  · exact h

end GlobalTheory.TrFinDense
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.TwistedOperators.SpanValuesDenseFinitePartSubrep =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinitePartIrreducibleAdmissible =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinitePartIrreducibleAdmissible", "h": "module\n\npublic import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsFactorisationCuspidal\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalFixed\nimport Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice\nimport Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsOpenIsCompactLevelOffFinEmpty\npublic import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicUnitaryClosureLocalComponentsOpen\npublic import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesFactorLocalStableStatement\npublic import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFinsetSumTranslatesFixedCompactSubgroupStatement\npublic import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FactorisableRestrictedTensorLevelStatement\npublic import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IrreducibleUnitaryRepEqFiniteSmoothPartTensorDisStatement\npublic import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff\npublic import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SpanValuesDenseFinitePartSubrep\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\npublic import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData\nimport Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec\n\n"}
section -- clump:auto
@[expose] public section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace

open Formalism.MainNotions.KudlaSiegelWeil (Restr)

namespace GlobalTheory.FinPartIrrAdm

open GlobalTheory.PRep (fixed smoothPart smoothRep IsSmooth)

alias mem_fixed_iff := _root_.GlobalTheory.LGrp.mem_fixed

def stabGroup {G X : Type} [Group G] [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ G X) (x : X) :
    Subgroup G :=
    { carrier := {g | ρ g x = x}
      mul_mem' := fun {a b} (ha : ρ a x = x) (hb : ρ b x = x) => by
        change ρ (a * b) x = x
        rw [map_mul, Module.End.mul_apply, hb, ha]
      one_mem' := by change ρ 1 x = x; simp
      inv_mem' := fun {a} (ha : ρ a x = x) => by
        change ρ a⁻¹ x = x
        conv_lhs => rw [← ha]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }

end GlobalTheory.FinPartIrrAdm

namespace GlobalTheory.FinPartIrrAdm
open GlobalTheory.PRep (fixed smoothPart smoothRep IsSmooth)

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {H : Type} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] {π : GA D V →* (H →L[ℂ] H)}

noncomputable abbrev valMap (hU : IsSubrep π ⊤) : smoothPart (finPartDS M hU) →ₗ[ℂ] ContinuousMultilinearMap ℂ M.H H :=
  (homDS M π ⊤).subtype ∘ₗ (smoothPart (finPartDS M hU)).subtype

theorem valMap_injective (hU : IsSubrep π ⊤) : Function.Injective (valMap (M := M) hU) := fun a b e =>
  Subtype.ext (Subtype.ext e)

theorem irreducible [CompleteSpace H] (hπ : IsIrrUnitary π) (hD : HasDSComp M π) (hU : IsSubrep π ⊤)
    (hadm : IsAdmissible (finPartDSSm M hU)) : (finPartDSSm M hU).IsIrreducible := by
  classical
  have hunit : IsUnitaryRep π := hπ.unitary
  haveI : Nontrivial H := hπ.irred.1
  let u : ∀ τ, M.H τ := fun τ => unitVec (H := M.H τ)
  obtain ⟨ev, hevd⟩ : ∃ ev : smoothPart (finPartDS M hU) →ₗ[ℂ] H,
      ev = (ContinuousMultilinearMap.apply ℂ M.H H u).toLinearMap ∘ₗ valMap hU := ⟨_, rfl⟩
  have hev : ∀ (g : GfC V) Φ, ev (finPartDSSm M hU g Φ) = π g (ev Φ) := fun g Φ => by subst hevd; rfl
  have hinner : ∀ (Φ Φ' : smoothPart (finPartDS M hU)) y y',
      ⟪valMap hU Φ' y', valMap hU Φ y⟫_ℂ = ⟪ev Φ', ev Φ⟫_ℂ * ∏ τ, ⟪y' τ, y τ⟫_ℂ := fun Φ Φ' y y' => by
    subst hevd
    exact inner_eq_bePi (fun τ => isIrrUnitary_dsRep M τ) hunit (Φ : homDS M π ⊤).2 (Φ' : homDS M π ⊤).2 y y'

  have hne : ∃ w : smoothPart (finPartDS M hU), w ≠ 0 := by
    obtain ⟨T, -, -, hTd⟩ := GlobalTheory.T.irreducibleUnitaryRep_eq_finiteSmoothPart_tensor_discreteSeries D V S M H π hπ hD hU
    by_contra hc
    push_neg at hc
    have h0 : Submodule.span ℂ {v | ∃ w y, v = T w y} = ⊥ := by
      rw [Submodule.span_eq_bot]
      rintro _ ⟨w, y, rfl⟩
      rw [hc w, map_zero]
      rfl
    have hb : (⊥ : Submodule ℂ H).topologicalClosure = ⊥ :=
      IsClosed.submodule_topologicalClosure_eq (by simp)
    rw [h0, hb] at hTd
    exact bot_ne_top hTd
  obtain ⟨w0, hw0⟩ := hne
  haveI : Nontrivial (smoothPart (finPartDS M hU)) := ⟨⟨w0, 0, hw0⟩⟩
  haveI : Nontrivial (Subrepresentation (finPartDSSm M hU)) :=
    ⟨⊥, ⊤, fun e => bot_ne_top (congrArg Subrepresentation.toSubmodule e :)⟩
  refine ⟨fun N => ?_⟩
  by_cases hN : N = ⊥
  · exact Or.inl hN
  refine Or.inr (Subrepresentation.toSubmodule_injective (eq_top_iff.2 fun Φ _ => ?_))
  have hdense := _root_.GlobalTheory.TrFinDense.span_values_dense D V S M H π hπ hU N hN
  obtain ⟨K0, hK0o, hK0c⟩ := GlobalTheory.CuspDec.exists_compact_open V
  have hΦo : IsOpen ((stabGroup (finPartDSSm M hU) Φ : Subgroup (GfC V)) : Set (GfC V)) := by
    have e : {g : GfC V | finPartDSSm M hU g Φ = Φ} = {g | finPartDS M hU g Φ = Φ} :=
      Set.ext fun _ => Subtype.ext_iff
    change IsOpen {g : GfC V | finPartDSSm M hU g Φ = Φ}
    rw [e]
    exact Φ.2
  obtain ⟨K, hKd⟩ : ∃ K : Subgroup (GfC V), K = K0 ⊓ stabGroup (finPartDSSm M hU) Φ := ⟨_, rfl⟩
  have hKo : IsOpen (K : Set (GfC V)) := hKd ▸ hK0o.inter hΦo
  have hKc : IsCompact (K : Set (GfC V)) := hKd ▸ hK0c.inter_right (Subgroup.isClosed_of_isOpen _ hΦo)
  have hKΦ : ∀ k ∈ K, finPartDSSm M hU k Φ = Φ := fun k hk => by
    rw [hKd] at hk
    exact hk.2
  haveI : FiniteDimensional ℂ (fixed (finPartDSSm M hU) K) := hadm.2 K hKo hKc
  obtain ⟨E, hEd⟩ : ∃ E : Submodule ℂ (smoothPart (finPartDS M hU)), E = N.toSubmodule ⊓ fixed (finPartDSSm M hU) K :=
    ⟨_, rfl⟩
  haveI : FiniteDimensional ℂ E := hEd ▸ Submodule.finiteDimensional_of_le inf_le_right
  have hEN : ∀ x ∈ E, x ∈ N.toSubmodule := fun x hx => by rw [hEd] at hx; exact hx.1
  have hEK : ∀ x ∈ E, x ∈ fixed (finPartDSSm M hU) K := fun x hx => by rw [hEd] at hx; exact hx.2
  have hEmem : ∀ x ∈ N.toSubmodule, x ∈ fixed (finPartDSSm M hU) K → x ∈ E := fun x h1 h2 => by
    rw [hEd]; exact ⟨h1, h2⟩
  obtain ⟨Eh, hEhd⟩ : ∃ Eh : Submodule ℂ H, Eh = E.map ev := ⟨_, rfl⟩
  haveI : FiniteDimensional ℂ Eh := hEhd ▸ inferInstance
  haveI : CompleteSpace Eh := FiniteDimensional.complete ℂ Eh
  have hpm := Eh.starProjection_apply_mem (ev Φ)
  have hpo := Eh.sub_starProjection_mem_orthogonal (ev Φ)
  generalize Eh.starProjection (ev Φ) = p at hpm hpo
  rw [hEhd] at hpm
  obtain ⟨n0, hn0E, hn0⟩ := hpm
  have horth : ev (Φ - n0) ∈ Ehᗮ := by
    rw [map_sub, hn0]
    exact hpo
  have hΦ1fix : ∀ k ∈ K, finPartDSSm M hU k (Φ - n0) = Φ - n0 := fun k hk => by
    have h1 : finPartDSSm M hU k Φ = Φ := hKΦ k hk
    have h2 : finPartDSSm M hU k n0 = n0 := mem_fixed_iff.1 (hEK _ hn0E) k hk
    exact (map_sub (finPartDSSm M hU k) Φ n0).trans (congrArg₂ (· - ·) h1 h2)
  have hinv : ∀ k ∈ K, ∀ a, ⟪π k a, ev (Φ - n0)⟫_ℂ = ⟪a, ev (Φ - n0)⟫_ℂ := fun k hk a => by
    conv_lhs => rw [← hΦ1fix k hk, hev]
    exact inner_map_map hunit _ _ _
  have hall : ∀ n ∈ N.toSubmodule, ⟪ev n, ev (Φ - n0)⟫_ℂ = 0 := by
    intro n hn
    obtain ⟨s, hsK, hsne, hsfix⟩ := _root_.GlobalTheory.exists_finset_sum_translate_fixed (finPartDSSm M hU) K hKc n (isSmooth_smoothRep _ n)
    have hmem : ∑ g ∈ s, finPartDSSm M hU g n ∈ E :=
      hEmem _ (Submodule.sum_mem _ fun g _ => N.apply_mem_toSubmodule g hn) (mem_fixed_iff.2 hsfix)
    have h1 := (Submodule.mem_orthogonal _ _).1 horth (ev (∑ g ∈ s, finPartDSSm M hU g n))
      (by rw [hEhd]; exact ⟨_, hmem, rfl⟩)
    have hterm : ∀ g ∈ s, ⟪ev (finPartDSSm M hU g n), ev (Φ - n0)⟫_ℂ = ⟪ev n, ev (Φ - n0)⟫_ℂ := fun g hg => by
      rw [hev]; exact hinv g (hsK g hg) _

    rw [map_sum, sum_inner, Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul] at h1
    exact (mul_eq_zero.1 h1).resolve_left (Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 hsne))
  have hzero : ∀ y', valMap hU (Φ - n0) y' = 0 := by
    intro y'
    have hle : Submodule.span ℂ {z | ∃ Ψ ∈ N.toSubmodule, ∃ y,
        z = ((Ψ : homDS M π ⊤) : ContinuousMultilinearMap ℂ M.H H) y} ≤ (ℂ ∙ valMap hU (Φ - n0) y')ᗮ := by
      rw [Submodule.span_le]
      rintro _ ⟨Ψ, hΨ, y, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right]
      change ⟪valMap hU (Φ - n0) y', valMap hU Ψ y⟫_ℂ = 0
      rw [hinner Ψ (Φ - n0) y y', ← inner_conj_symm, hall Ψ hΨ, map_zero, zero_mul]
    have hcl := Submodule.topologicalClosure_minimal _ hle (Submodule.isClosed_orthogonal _)
    rw [hdense] at hcl
    exact inner_self_eq_zero.1 (Submodule.mem_orthogonal_singleton_iff_inner_right.1 (hcl Submodule.mem_top))
  have h0 : Φ - n0 = 0 := valMap_injective hU (by rw [map_zero]; exact ContinuousMultilinearMap.ext hzero)
  rw [sub_eq_zero.1 h0]
  exact hEN _ hn0E

end GlobalTheory.FinPartIrrAdm

namespace GlobalTheory.FinPartIrrAdm

theorem irreducible_admissible : GlobalTheory.Published.FlathFactorisation → ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : GA D V →* (H →L[ℂ] H)), IsIrrUnitary π → HasDSComp M π → ∀ hU : IsSubrep π ⊤, (finPartDSSm M hU).IsIrreducible ∧ IsAdmissible (finPartDSSm M hU) := by
  intro hF D V S M H _ _ _ π hπ hD hU
  exact ⟨irreducible hπ hD hU (admissible hF hπ hD hU), admissible hF hπ hD hU⟩

end GlobalTheory.FinPartIrrAdm
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinitePartIrreducibleAdmissible =====
