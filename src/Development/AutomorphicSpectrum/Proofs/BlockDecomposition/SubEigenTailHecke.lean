module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.CosetCount
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubquotientOfEigencharacter
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.CuspRep PositivityTheory.Rg.BcB.F.Tail.PExp GlobalTheory.CompanionTheory.SubEig

namespace GlobalTheory.CompanionTheory.SubEigIrr

theorem mem_fixed_iff {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
    {K : Subgroup G} {v : V} : v ∈ fixed ρ K ↔ ∀ k ∈ K, ρ k v = v := by
  constructor
  · intro h k hk
    have := h ⟨k, hk⟩
    simpa using this
  · intro h k
    simpa using h k.1 k.2

theorem hkS_eq_sum {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (K : Subgroup G) (f : G → ℂ) (hf : {q : G ⧸ K | f q.out ≠ 0}.Finite) (v : V) :
    hkS ρ K f v = ∑ q ∈ hf.toFinset, f q.out • ρ q.out v := by
  unfold hkS
  refine finsum_eq_sum_of_support_subset _ fun q hq => ?_
  simp only [Set.Finite.coe_toFinset]
  intro h0
  exact hq (by simp [h0])

theorem hkS_map {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (φ : Representation.IntertwiningMap ρ σ)
    (K : Subgroup G) (f : G → ℂ) (hf : {q : G ⧸ K | f q.out ≠ 0}.Finite) (v : V) :
    φ (hkS ρ K f v) = hkS σ K f (φ v) := by
  rw [hkS_eq_sum ρ K f hf, hkS_eq_sum σ K f hf]
  show φ.toLinearMap _ = _

  rw [map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [map_smul]
  congr 1
  exact φ.isIntertwining _ _ q.out v

theorem subEig : SubEig := by
  intro G _ _ _ V _ _ ρ hρ K X f e hfin u hu hu0 heig
  let S := cyc ρ u
  let u' : S.toSubmodule := ⟨u, mem_cyc ρ u⟩
  have hu' : u' ≠ 0 := fun h => hu0 (congrArg Subtype.val h)
  obtain ⟨T, huT, hmax⟩ := exists_max_avoid S.toRepresentation hu'
  have hst : ∀ g, T.toSubmodule ≤ T.toSubmodule.comap (S.toRepresentation g) :=
    fun g _ hv => T.apply_mem_toSubmodule g hv
  let τ := S.toRepresentation.quotient T.toSubmodule hst
  have hirr : τ.IsIrreducible := quot_irred S.toRepresentation T huT hmax (cyc_gen ρ u) hst
  have hsm : IsSmooth τ := smooth_quot (smooth_sub hρ S) _ hst
  let p := mkI S.toRepresentation T.toSubmodule hst
  let w : S.toSubmodule ⧸ T.toSubmodule := p u'
  have hw0 : w ≠ 0 := by
    show (Submodule.Quotient.mk u' : S.toSubmodule ⧸ T.toSubmodule) ≠ 0
    rwa [Ne, Submodule.Quotient.mk_eq_zero]
  have hsub : IsSubquotient τ ρ := by
    refine ⟨S, p, fun y => ?_⟩
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact ⟨x, rfl⟩
  refine ⟨⟨_, τ, hsm, hirr⟩, hsub, w, ?_, hw0, fun x => ?_⟩
  · refine mem_fixed_iff.2 fun k hk => ?_
    have hh' : S.toRepresentation k u' = u' := Subtype.ext (mem_fixed_iff.1 hu k hk)
    have := p.isIntertwining _ _ k u'
    rw [hh'] at this
    exact this.symm
  · have h1 : hkS S.toRepresentation K (f x) u' = e x • u' := by
      apply Subtype.ext
      have := hkS_map (inclI S) K (f x) (hfin x) u'
      exact this.trans (heig x)
    have := hkS_map p K (f x) (hfin x) u'
    rw [h1, map_smul] at this
    exact this.symm

end GlobalTheory.CompanionTheory.SubEigIrr

end
