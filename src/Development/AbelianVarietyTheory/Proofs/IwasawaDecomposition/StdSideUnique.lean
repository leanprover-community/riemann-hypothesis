module

public import Formalism.LocalToGlobal.IndefiniteReal.BridgeTie
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicSplit
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemClosureUnitary
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsDiscriminantTwelfthRootOfIdealLatticeIffDelta1
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.Foundations.RayPrimes

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Col Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.R3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.StdUnique

theorem closed_eq_univ {D : D7} (V : HSp D) (C : Set (GA D V)) (hC : IsClosed C) (hQ : ∀ γ ∈ GQ V, γ ∈ C)
    (hf : ∀ h, ∀ k ∈ GfC V, h ∈ C → h * k ∈ C) (h : GA D V) : h ∈ C := by
  obtain ⟨e, he⟩ := GlobalTheory.Mem.VolSplit.exists_adelic_split D.host.F D.host.E D.sp.cm.sig V.rank V.gram
  have hfin : ∀ h : GA D V, (e h).2 = 1 → h ∈ GinfC V := fun h H =>
    MonoidHom.mem_ker.2 (Units.ext ((he h).1.symm.trans (by rw [H]; rfl)))
  have hinf : ∀ h : GA D V, (e h).1 = 1 → h ∈ GfC V := fun h H =>
    MonoidHom.mem_ker.2 (Units.ext ((he h).2.symm.trans (by rw [H]; rfl)))
  have hu : e.symm ((e h).1, 1) ∈ C := by
    by_contra hn
    obtain ⟨γ, hγ, k, hk, hU, -⟩ := GlobalTheory.RealApprox.weak_approx_real V _ (hfin _ (by rw [e.apply_symm_apply])) Cᶜ
      hC.isOpen_compl hn
    exact hU (hf γ k hk (hQ γ hγ))
  have hk : e.symm (1, (e h).2) ∈ GfC V := hinf _ (by rw [e.apply_symm_apply])
  have := hf _ _ hk hu
  rwa [← map_mul, Prod.mk_mul_mk, mul_one, one_mul, Prod.mk.eta, e.symm_apply_apply] at this

variable {D : D7} {V : HSp D} (c : CoefA V) (hc : c.Is)
include hc

theorem bot_or_top (U : Submodule ℂ c.W) (hU : ∀ γ ∈ GQ V, ∀ w ∈ U, c.ρ γ w ∈ U) : U = ⊥ ∨ U = ⊤ := by
  refine hc.2.2.2.2 U fun h => ?_
  rintro _ ⟨w, hw, rfl⟩
  refine closed_eq_univ V {h | c.ρ h w ∈ U} (U.closed_of_finiteDimensional.preimage (hc.2.2.1 w))
    (fun γ hγ => hU γ hγ w hw) (fun h k hk H => ?_) h
  show c.ρ (h * k) w ∈ U
  rw [map_mul, hc.1 k hk, mul_one]
  exact H


omit hc in
theorem exists_ratMat (γ : GQ V) : ∃ γE, Bridge.IsRatMat V γ γE := by
  obtain ⟨γ, ⟨g, -, hg⟩⟩ := γ
  exact ⟨g, hg.symm⟩

omit hc

end GlobalTheory.Mem.StdUnique

end
