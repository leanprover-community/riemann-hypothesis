module

public import Development.AbelianVarietyTheory.Definitions.Foundations.SgC
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SgDistribution
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelUnitInTowerAnEqSiegelUnitOnComplexStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped UpperHalfPlane MatrixGroups
open GlobalTheory.KZ GlobalTheory.Sieg

noncomputable section

namespace GlobalTheory.KZDist

lemma isAdmissibleSmoothingFactor_divided_indices (c m : ℕ) (x : Fin 2 → ℚ) (a b : ℕ) (hA : admitted c x) (hm : 0 < m) :
    admitted c ![(x 0 + a) / m, (x 1 + b) / m] := by
  obtain ⟨hc1, hc6, hnot⟩ := hA
  refine ⟨hc1, hc6, ?_⟩
  rintro ⟨⟨k, hk⟩, ⟨l, hl⟩⟩
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at hk hl
  apply hnot
  refine ⟨⟨m * k - c * a, ?_⟩, ⟨m * l - c * b, ?_⟩⟩
  · push_cast; rw [hk]; field_simp; ring
  · push_cast; rw [hl]; field_simp; ring

lemma isOpen_Hs' : IsOpen Hs := isOpen_lt continuous_const Complex.continuous_im

lemma codiscreteWithin_Hs_neBot : (Filter.codiscreteWithin Hs).NeBot := by
  rw [← Filter.forall_mem_nonempty_iff_neBot]
  intro s hs
  have hI : Complex.I ∈ Hs := by simp [Hs]
  have h1 := (mem_codiscreteWithin_iff_forall_mem_nhdsNE.1 hs) _ hI
  have h2 : Hs ∈ nhdsWithin Complex.I {Complex.I}ᶜ := mem_nhdsWithin_of_mem_nhds (isOpen_Hs'.mem_nhds hI)
  obtain ⟨z, hz1, hz2⟩ := Filter.nonempty_of_mem (Filter.inter_mem h1 h2)
  rcases hz1 with h | h
  · exact ⟨z, h⟩
  · exact absurd hz2 h

theorem siegel_distribution : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Tower Ω ε)
    (c : ℕ) (m : ℕ) (x : Fin 2 → ℚ), admitted c x → 0 < m → Nat.Coprime c m →
    ∏ a ∈ Finset.range m, ∏ b ∈ Finset.range m, siegel T c ![(x 0 + a) / m, (x 1 + b) / m] = siegel T c x := by
  intro Ω _ _ _ ε T c m x hA hm hcm
  haveI := codiscreteWithin_Hs_neBot
  apply T.an.injective
  rw [map_prod, GlobalTheory.T.siegelUnitInTower_an_eq_siegelUnitOnComplex Ω ε T c x hA]
  simp_rw [map_prod]
  have h1 : ∀ a ∈ Finset.range m, ∏ b ∈ Finset.range m, T.an (siegel T c ![(x 0 + a) / m, (x 1 + b) / m])
      = Filter.Germ.coeRingHom _ (∏ b ∈ Finset.range m, sgC c ![(x 0 + a) / m, (x 1 + b) / m]) := by
    intro a _
    rw [map_prod]
    refine Finset.prod_congr rfl fun b _ => ?_
    rw [GlobalTheory.T.siegelUnitInTower_an_eq_siegelUnitOnComplex Ω ε T c _ (isAdmissibleSmoothingFactor_divided_indices c m x a b hA hm)]
    rfl
  rw [Finset.prod_congr rfl h1, ← map_prod]
  show ((∏ a ∈ Finset.range m, ∏ b ∈ Finset.range m, sgC c ![(x 0 + a) / m, (x 1 + b) / m] : ℂ → ℂ) : Mero) = _
  congr 1
  funext z
  simpa only [Finset.prod_apply, sgC] using
    GlobalTheory.SiegDist.sg_distribution c m x (UpperHalfPlane.ofComplex z) hA hm hcm

end GlobalTheory.KZDist
