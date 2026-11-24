module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.StandardOrderExtendedBasisApplyLowBlock
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeUnipotentHaarAndModulus
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtXCastAdd
import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.VolBridge

namespace GlobalTheory.UnipLevelTopo

theorem isOpen_inf_isCompact : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {A : Type} [Fintype A] [DecidableEq A] {c : ℕ} (J : Subgroup (GL (A ⊕ Fin c) k)) (g : GL (A ⊕ Fin c) k), IsOpen (J : Set (GL (A ⊕ Fin c) k)) → IsCompact (J : Set (GL (A ⊕ Fin c) k)) → IsOpen ((((Cgrp J g).subgroupOf (N k A c 1)) ⊓ ((KO k (A ⊕ Fin c)).subgroupOf (N k A c 1)) : Subgroup (N k A c 1)) : Set (N k A c 1)) ∧ IsCompact (((Cgrp J g).subgroupOf (N k A c 1) : Subgroup (N k A c 1)) : Set (N k A c 1)) ∧ IsCompact (((KO k (A ⊕ Fin c)).subgroupOf (N k A c 1) : Subgroup (N k A c 1)) : Set (N k A c 1)) := by
  intro k _ _ _ _ A _ _ c J g hJo hJc
  obtain ⟨h1, h2⟩ := isOpen_isCompact_conj g hJo hJc
  have hemb : Topology.IsClosedEmbedding (Subtype.val : N k A c 1 → GL (A ⊕ Fin c) k) :=
    (GlobalTheory.RootEx.VolN.isClosed_N (k := k) (n := A) (c := c) 1).isClosedEmbedding_subtypeVal
  have eC : (((Cgrp J g).subgroupOf (N k A c 1) : Subgroup (N k A c 1)) : Set (N k A c 1)) =
      Subtype.val ⁻¹' (J.comap (MulAut.conj g⁻¹).toMonoidHom : Set (GL (A ⊕ Fin c) k)) := by
    ext x
    simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf, Set.mem_preimage, Cgrp, Subgroup.mem_inf]
    exact ⟨fun h => h.2, fun h => ⟨Subgroup.mem_sup_right x.2, h⟩⟩
  have eK : (((KO k (A ⊕ Fin c)).subgroupOf (N k A c 1) : Subgroup (N k A c 1)) : Set (N k A c 1)) =
      Subtype.val ⁻¹' (KO k (A ⊕ Fin c) : Set (GL (A ⊕ Fin c) k)) := by
    ext x; simp [Subgroup.mem_subgroupOf]
  refine ⟨?_, ?_, ?_⟩
  · rw [Subgroup.coe_inf, eC, eK]
    exact (h1.inter GlobalTheory.SplitFlip.isOpen_KO).preimage continuous_subtype_val
  · rw [eC]; exact hemb.isCompact_preimage h2
  · rw [eK]; exact hemb.isCompact_preimage GlobalTheory.SplitFlip.isCompact_KO

end GlobalTheory.UnipLevelTopo
