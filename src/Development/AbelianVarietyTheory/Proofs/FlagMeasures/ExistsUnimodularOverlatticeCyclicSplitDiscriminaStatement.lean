module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
public import Formalism.HermitianLattices.StatementMass
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnimodularOverlatticeCyclicSplitDiscrimina
import Formalism.HermitianLattices.HermitianLatticesProofs.DualBasic
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
private theorem full_of_unimodular {K V : Type} [Field K] [NumberField K] [StarRing K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : h.IsSymm)
    {L : Submodule (𝓞 K) V} (hL : Submodule.IsLattice K L) (hu : IsUnimodular h L) :
    Submodule.IsFullLattice K L := by
  letI := hL
  refine { span_eq_top := ?_ }
  let W := Submodule.span K (L : Set V)
  change W = ⊤
  by_contra hw
  let b := Module.finBasis K V
  let e : V ≃ₗ⋆[K] V := (b.equivFun.trans (starLinearEquiv K)).trans b.equivFun.symm
  let g : V →ₗ[K] Module.Dual K W :=
    (LinearMap.domRestrict' W).comp (h.comp e.toLinearMap)
  have hd : Module.finrank K (Module.Dual K W) < Module.finrank K V := by
    rw [Subspace.dual_finrank_eq]
    exact Submodule.finrank_lt hw
  obtain ⟨x, hx, hx0⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hd)
  have hm (a : K) : a • e x ∈ L := by
    rw [← hu, dualBasic_mem_dual]
    intro y hy
    have hz : h (e x) y = 0 :=
      congrArg (fun f : Module.Dual K W => f ⟨y, Submodule.subset_span hy⟩)
        (LinearMap.mem_ker.mp hx)
    have hz' : h y (e x) = 0 := by
      exact hs.eq_iff.mp hz
    simp [LinearMap.map_smul, hz']
  let i : K →ₗ[𝓞 K] L :=
    ((LinearMap.toSpanSingleton K _ (e x)).restrictScalars (𝓞 K)).codRestrict L hm
  letI : Module.Finite (𝓞 K) L := Module.Finite.iff_fg.mpr hL.fg
  letI : Module.Finite (𝓞 K) K := Module.Finite.of_injective i fun a b hab =>
    smul_left_injective K (fun hzero => hx0 (e.map_eq_zero_iff.mp hzero))
      (congrArg Subtype.val hab)
  exact RingOfIntegers.not_isField K
    (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 K) K) (Field.toIsField K))


theorem _root_.GlobalTheory.T.exists_unimodular_overlattice_cyclic_split_discriminant : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → h.Nondegenerate → ∀ (𝔓 : Ideal (𝓞 K)), 𝔓 ≠ ⊥ → IsCoprime 𝔓 (conjIdeal (K := K) 𝔓) → (∀ L : Submodule (𝓞 K) V, IsIntLat h L → Nonempty ((↥(dual h L) ⧸ L.comap (dual h L).subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ 𝔓 * conjIdeal (K := K) 𝔓)) → ∃! M : Submodule (𝓞 K) V, Submodule.IsFullLattice K M ∧ IsUnimodular h M ∧ L ≤ M ∧ Nonempty ((↥M ⧸ L.comap M.subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ 𝔓))) ∧ ∀ M L : Submodule (𝓞 K) V, Submodule.IsFullLattice K M → IsUnimodular h M → L ≤ M → Nonempty ((↥M ⧸ L.comap M.subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ 𝔓)) → IsIntLat h L ∧ Nonempty ((↥(dual h L) ⧸ L.comap (dual h L).subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ 𝔓 * conjIdeal (K := K) 𝔓)) := by
  first
  | exact @GlobalTheory.Mass.SplitOver.main
  | intro K V _ _ _ _ _ _ _ _ h hc hs hn P hp hcop
    obtain ⟨forward, backward⟩ := GlobalTheory.Mass.SplitOver.main K V h hc hs hn P hp hcop
    constructor
    · intro L hL he
      obtain ⟨M, ⟨hM, hu, hl, heM⟩, unique⟩ := forward L hL he
      exact ⟨M, ⟨full_of_unimodular h hs hM hu, hu, hl, heM⟩,
        fun N hN => unique N ⟨hN.1.toIsLattice, hN.2⟩⟩
    · intro M L hM hu hl he
      exact backward M L hM.toIsLattice hu hl he
