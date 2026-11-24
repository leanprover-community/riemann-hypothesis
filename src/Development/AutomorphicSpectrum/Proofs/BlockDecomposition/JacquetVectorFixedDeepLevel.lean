module

public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CongruenceSubgroupBasisNhdsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeOperatorExists
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModulusTrivialOnLeviCompactStatement
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

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil ValuativeRel

namespace GlobalTheory.CompanionTheory.JacSmooth

theorem jac_fixed_of_smooth : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) (hd : ∑ _a : Fin n, 1 = n) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π →
    ∀ w : Jacquet π (unipRad k (stdBlocks (fun _ : Fin n => 1) hd)), ∃ m, 1 ≤ m ∧
      ∀ u ∈ PositivityTheory.Lbc.KM k n (Zls.Km k n m) (fun _ : Fin n => 1) hd,
        jac (stdBlocks (fun _ : Fin n => 1) hd) π u w = w := by
  intro k _ _ _ _ n hd V _ _ π hπ w
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  obtain ⟨m, hm, hK⟩ := GlobalTheory.T.congruence_subgroup_basis_nhds k n {g | π g v = v} (hπ v) (by simp)
  refine ⟨m, hm, fun u hu => ?_⟩
  have hδ : deltaHalf k (PositivityTheory.Lbc.Bl (fun _ : Fin n => 1)) u = 1 :=
    GlobalTheory.T.modulus_trivial_on_levi_compact k n n (fun _ : Fin n => 1) hd (Zls.Km k n m) (GlobalTheory.CompanionTheory.HeckeKm.isCompact_Km n m) u hu
  have hv : π (leviEmb k (stdBlocks (fun _ : Fin n => 1) hd) u) v = v := hK hu
  rw [jac_mk, hv, hδ]
  simp

end GlobalTheory.CompanionTheory.JacSmooth

end
