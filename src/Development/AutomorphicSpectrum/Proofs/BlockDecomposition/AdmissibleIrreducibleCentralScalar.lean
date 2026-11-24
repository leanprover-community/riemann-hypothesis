module

public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.Topology.Instances.Matrix
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
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
public import Mathlib.LinearAlgebra.Eigenspace.Basic

@[expose] public section

open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.SchurCentre

theorem scalar_acts_by_scalar : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → π.IsIrreducible → IsAdmissible π → ∀ t : kˣ, ∃ c : ℂ, ∀ v, π (Matrix.GeneralLinearGroup.scalar (Fin N) t) v = c • v := by
  intro k _ _ _ _ N V _ _ π hs hirr hadm t
  haveI := hirr

  have hz : ∀ g : GL (Fin N) k, g * Matrix.GeneralLinearGroup.scalar (Fin N) t =
      Matrix.GeneralLinearGroup.scalar (Fin N) t * g := by
    intro g
    ext i j
    simp [Matrix.GeneralLinearGroup.scalar, Matrix.mul_apply, Matrix.diagonal_apply, mul_comm]
  set z := Matrix.GeneralLinearGroup.scalar (Fin N) t with hzdef
  have hcomm : ∀ (g : GL (Fin N) k) (w : V), π g (π z w) = π z (π g w) := by
    intro g w
    rw [← Module.End.mul_apply, ← map_mul, hz g, map_mul, Module.End.mul_apply]

  obtain ⟨v, hv⟩ : ∃ v : V, v ≠ 0 := by
    by_contra h
    push Not at h
    apply (bot_ne_top : (⊥ : Subrepresentation π) ≠ ⊤)
    apply Subrepresentation.toSubmodule_injective
    change (⊥ : Submodule ℂ V) = ⊤
    ext u
    simp [h u]

  let S : Subgroup (GL (Fin N) k) :=
    { carrier := {g | π g v = v}
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
        rw [hb, ha]
      one_mem' := by simp
      inv_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at *
        conv_lhs => rw [← ha]
        rw [← Module.End.mul_apply, ← map_mul]
        simp }
  let K : Subgroup (GL (Fin N) k) := GlobalTheory.SplitWeil.KO k (Fin N) ⊓ S
  have hKo : IsOpen (K : Set (GL (Fin N) k)) :=
    (GlobalTheory.SplitFlip.isOpen_KO (k := k) (n := Fin N)).inter (hs v)
  have hKc : IsCompact (K : Set (GL (Fin N) k)) :=
    (GlobalTheory.SplitFlip.isCompact_KO (k := k) (n := Fin N)).of_isClosed_subset
      (Subgroup.isClosed_of_isOpen K hKo) (fun _ h => h.1)
  haveI hfd : FiniteDimensional ℂ (fixed π K) := hadm.2 K hKo hKc
  have hmem : ∀ w : V, w ∈ fixed π K ↔ ∀ h : K, π (h : GL (Fin N) k) w = w := by
    intro w
    show (∀ h : K, _ = _) ↔ _
    simp
  have hvK : v ∈ fixed π K := (hmem v).2 fun h => h.2.2
  haveI : Nontrivial (fixed π K) :=
    ⟨⟨⟨v, hvK⟩, 0, fun h => hv (congrArg Subtype.val h)⟩⟩
  have hst : ∀ w ∈ fixed π K, π z w ∈ fixed π K := by
    intro w hw
    refine (hmem _).2 fun h => ?_
    rw [hcomm, (hmem w).1 hw h]
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue ((π z).restrict hst)
  obtain ⟨w, hw⟩ := hc.exists_hasEigenvector
  have hw0 : (w : V) ≠ 0 := fun h => hw.2 (Subtype.ext h)
  have hwc : π z (w : V) = c • (w : V) := by
    have := congrArg Subtype.val hw.apply_eq_smul
    simpa using this

  let f : Representation.IntertwiningMap π π :=
    { toLinearMap := π z - c • LinearMap.id
      isIntertwining' := by
        intro g
        ext u
        simp [hcomm] }
  refine ⟨c, fun u => ?_⟩
  rcases Representation.IsIrreducible.bijective_or_eq_zero f with hb | h0
  · exfalso
    apply hw0
    apply hb.1
    show π z (w : V) - c • (w : V) = f 0
    rw [hwc, sub_self, map_zero]
  · have := congrArg (fun F : Representation.IntertwiningMap π π => F u) h0
    have h1 : π z u - c • u = 0 := this
    exact sub_eq_zero.1 h1

end GlobalTheory.CompanionTheory.SchurCentre
