module

public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletedLatticeStabilizerCompactOpen
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

namespace GlobalTheory.AdelicU

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E))

omit [NumberField E] in
theorem mem_levelOpen_iff_projFin {g : GAd σ J} :
    g ∈ levelOpen σ J L ↔ projFin σ J g ∈ levelOffFin σ J L ∅ := by
  simp [mem_levelOpen, mem_levelOffFin]

omit [NumberField E] in
theorem mem_stabLoc_iff_embLocFin {v : HeightOneSpectrum (𝓞 F)} {g : GLoc σ J v} :
    g ∈ stabLoc σ J L v ↔ embLocFin σ J v g ∈ levelOffFin σ J L ∅ := by
  rw [mem_levelOffFin]
  refine ⟨fun h => ⟨by simp, fun u _ => ?_⟩, fun h => by simpa using h.2 v (by simp)⟩
  by_cases e : u = v
  · subst e; simpa using h
  · rw [projFinLoc_embLocFin_ne σ J e]; exact one_mem _

omit [NumberField E] in
theorem image_ofFin_levelOffFin (S : Finset (HeightOneSpectrum (𝓞 F))) :
    ofFin σ J '' (levelOffFin σ J L S : Set (GFin σ J)) = (levelOff σ J L S : Set (GAd σ J)) := by
  ext g
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hg
    have h : g ∈ (ofFin σ J).range := by rw [range_ofFin]; exact (mem_levelOff.1 hg).1
    obtain ⟨y, rfl⟩ := h
    exact ⟨y, hg, rfl⟩

variable [Submodule.IsFullLattice E L]

theorem isOpen_isCompact_levelOffFin_empty :
    IsOpen (levelOffFin σ J L ∅ : Set (GFin σ J)) ∧ IsCompact (levelOffFin σ J L ∅ : Set (GFin σ J)) := by
  have hfg : L.FG := Submodule.IsLattice.fg (A := E) L
  obtain ⟨K, hK, ho, hc⟩ := GlobalTheory.Mem.Vol.StabGroup.exists_compact_open_stab F E σ n J L hfg
    Submodule.IsFullLattice.span_eq_top
  have e : levelOffFin σ J L ∅ = K := by
    ext g
    have h := mem_levelOpen_iff_latHat σ J hfg (ofFin σ J g)
    have h2 : Formalism.MainNotions.StandardLattice.finMat σ J (ofFin σ J g) = (HA.mat (Af F) σ J g).1 :=
      congrArg (fun x => (HA.mat (Af F) σ J x).1) (projFin_ofFin σ J g)
    rw [mem_levelOpen_iff_projFin, projFin_ofFin, h2] at h
    exact h.trans (hK g).symm
  rw [e]
  exact ⟨ho, hc⟩

theorem isOpen_levelOffFin_empty : IsOpen (levelOffFin σ J L ∅ : Set (GFin σ J)) :=
  (isOpen_isCompact_levelOffFin_empty σ J L).1

theorem isOpen_levelOpen : IsOpen (levelOpen σ J L : Set (GAd σ J)) := by
  have : (levelOpen σ J L : Set (GAd σ J)) = projFin σ J ⁻¹' (levelOffFin σ J L ∅ : Set (GFin σ J)) :=
    Set.ext fun _ => mem_levelOpen_iff_projFin σ J L
  rw [this]
  exact (isOpen_levelOffFin_empty σ J L).preimage (continuous_projFin σ J)

theorem isOpen_stabLoc (v : HeightOneSpectrum (𝓞 F)) : IsOpen (stabLoc σ J L v : Set (GLoc σ J v)) := by
  have : (stabLoc σ J L v : Set (GLoc σ J v)) = embLocFin σ J v ⁻¹' (levelOffFin σ J L ∅ : Set (GFin σ J)) :=
    Set.ext fun _ => mem_stabLoc_iff_embLocFin σ J L
  rw [this]
  exact (isOpen_levelOffFin_empty σ J L).preimage (continuous_embLocFin σ J v)

theorem isCompact_stabLoc (v : HeightOneSpectrum (𝓞 F)) : IsCompact (stabLoc σ J L v : Set (GLoc σ J v)) := by
  have : (stabLoc σ J L v : Set (GLoc σ J v)) = embLocFin σ J v ⁻¹' (levelOffFin σ J L ∅ : Set (GFin σ J)) :=
    Set.ext fun _ => mem_stabLoc_iff_embLocFin σ J L
  rw [this]
  exact (Function.LeftInverse.isClosedEmbedding (projFinLoc_embLocFin_self σ J v) (continuous_projFinLoc σ J v)
    (continuous_embLocFin σ J v)).isCompact_preimage (isOpen_isCompact_levelOffFin_empty σ J L).2

theorem isCompact_levelOffFin (S : Finset (HeightOneSpectrum (𝓞 F))) :
    IsCompact (levelOffFin σ J L S : Set (GFin σ J)) := by
  have : (levelOffFin σ J L S : Set (GFin σ J)) =
      (levelOffFin σ J L ∅ : Set (GFin σ J)) ∩ ofFin σ J ⁻¹' (awayPts σ J S : Set (GAd σ J)) := by
    ext g
    change ofFin σ J g ∈ levelOff σ J L S ↔ ofFin σ J g ∈ levelOff σ J L ∅ ∧ ofFin σ J g ∈ awayPts σ J S
    simp only [levelOff_eq, finAwayPts, Subgroup.mem_inf, awayPts_empty, Subgroup.mem_top]
    tauto
  rw [this]
  exact (isOpen_isCompact_levelOffFin_empty σ J L).2.inter_right
    ((isClosed_awayPts σ J S).preimage (continuous_ofFin σ J))

theorem isCompact_levelOff (S : Finset (HeightOneSpectrum (𝓞 F))) :
    IsCompact (levelOff σ J L S : Set (GAd σ J)) := by
  rw [← image_ofFin_levelOffFin]
  exact (isCompact_levelOffFin σ J L S).image (continuous_ofFin σ J)

theorem isCompact_levelFin : IsCompact (levelFin σ J L : Set (GAd σ J)) := isCompact_levelOff σ J L ∅

end GlobalTheory.AdelicU
