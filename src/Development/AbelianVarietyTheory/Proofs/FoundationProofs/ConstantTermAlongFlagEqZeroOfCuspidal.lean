module

public import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasurePreservingConj
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemExtSubSpanDepth
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.Mem.Th GlobalTheory.Cusp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Cusp

theorem constTerm_eq_zero_of_mem_cuspCont (D : D7) (V : HSp D) (φ : GA D V → ℂ) (h : φ ∈ cuspCont V) (𝔉 : IsoFlag V)
    (h𝔉 : 𝔉.Proper) : constTerm 𝔉 φ = 0 := by
  have hi : (⟨1, Nat.succ_lt_succ h𝔉⟩ : Fin (𝔉.k + 1)) ≠ 0 := Fin.ne_of_val_ne one_ne_zero
  have h0 : constTermOn (GQ V) (NA (.single (𝔉.isIsotropic hi))) φ = 0 :=
    (isCuspFun_iff h.2.1).1 h.2.2 _ (𝔉.isIsotropic hi)
  funext x
  refine (Stages.constTermOn_stages (GA D V) (GQ V) (NA 𝔉) (NA (.single (𝔉.isIsotropic hi)))
    (𝔉.unip_single_le D.sp.cm _ hi) (fun p hp n hn => IsoFlag.conj_mem_unip ?_ hn) (cocompact_flag D V 𝔉)
    (cocompact_single _) φ h.2.1 h.1 x).trans ?_
  · rw [IsoFlag.par_single]
    exact 𝔉.par_le_parab D.sp.cm _ _ (𝔉.unip_le_par D.sp.cm _ hp)
  · rw [h0]
    exact (cocompact_flag D V 𝔉).constTermOn_const 0 x

end GlobalTheory.Cusp
