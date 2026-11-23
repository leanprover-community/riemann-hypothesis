module

public import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.GaussCM
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.EqZeroOfIsIsoSub
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open NumberField GroundTheory.Heights₂.Heights.LowerBoundFree

section Torus

variable {Em : Type} [Field Em] [NumberField Em] {K : Type} [Field K] [NumberField K] {N : ℕ}

def baseChangeLat (K : Type) [Field K] [NumberField K] (I : Submodule (𝓞 Em) (Fin N → Em)) :
    Submodule (𝓞 K) ((Em →+* K) → Fin N → K) :=
  Submodule.span (𝓞 K) ((fun v σ a => σ (v a)) '' (I : Set (Fin N → Em)))


open Classical in
def eigenLat (I : Submodule (𝓞 Em) (Fin N → Em)) (s : Em →+* K) : Submodule (𝓞 K) (Fin N → K) :=
  (baseChangeLat K I).comap (LinearMap.single (𝓞 K) (fun _ : Em →+* K => Fin N → K) s)

def familyLat (s : Em →+* K) {ρ : ℕ} (v : Fin ρ → Fin N → Em) : Submodule (𝓞 K) (Fin N → K) :=
  Submodule.span (𝓞 K) (Set.range fun a i => s (v a i))

def genIndex {M : Type*} [AddCommGroup M] (P Q : AddSubgroup M) : ℝ :=
  (Q.relIndex P : ℝ) / (P.relIndex Q : ℝ)

def familyIndex (I : Submodule (𝓞 Em) (Fin N → Em)) {ρ : ℕ} (v : Fin ρ → Fin N → Em) : ℕ :=
  (Submodule.span (𝓞 Em) (Set.range v)).toAddSubgroup.relIndex I.toAddSubgroup

end Torus

def TorusIndex.Statement : Prop :=
  ∀ (Em : Type) [Field Em] [NumberField Em] (K : Type) [Field K] [NumberField K] (ι : K →+* ℂ),
    (∀ σ : Em →+* ℂ, ∃ t : Em →+* K, ι.comp t = σ) →
    ∀ (N : ℕ) (I : Submodule (𝓞 Em) (Fin N → Em)) (ρ : ℕ) (v : Fin ρ → Fin N → Em), IsNzFamily I ρ v →
    ∀ s : Em →+* K,
      genIndex (eigenLat I s).toAddSubgroup (familyLat s v).toAddSubgroup =
        ((familyIndex I v : ℝ) / |(discr Em : ℝ)| ^ ρ) ^ ((Module.finrank ℚ K : ℝ) / Module.finrank ℚ Em)

namespace Gauss

open Gauss

theorem split (ι σ : Em →+* ℂ) : ∃ t : Em →+* Em, ι.comp t = σ := by
  have hcc : (ι.comp (cc : Em →+* Em)) ζ = -ι ζ := by
    rw [RingHom.comp_apply]
    change ι (cc ζ) = -ι ζ
    rw [cc_ζ, map_neg]
  rcases emb_ζ σ with h | h <;> rcases emb_ζ ι with h0 | h0
  · exact ⟨RingHom.id _, ringHom_ext (by rw [RingHom.comp_id, h, h0])⟩
  · exact ⟨_, ringHom_ext (by rw [hcc, h, h0, neg_neg])⟩
  · exact ⟨_, ringHom_ext (by rw [hcc, h, h0])⟩
  · exact ⟨RingHom.id _, ringHom_ext (by rw [RingHom.comp_id, h, h0])⟩

def isoVec : Fin 2 → Em := fun _ => 1

def isoLine : Submodule (𝓞 Em) (Fin 2 → Em) := Submodule.span (𝓞 Em) {isoVec}

def isoFam : Fin 1 → Fin 2 → Em := fun _ => isoVec

theorem span_isoFam : Submodule.span (𝓞 Em) (Set.range isoFam) = isoLine := by
  show Submodule.span (𝓞 Em) (Set.range fun _ : Fin 1 => isoVec) = isoLine
  rw [Set.range_const]
  rfl

theorem isoFam_nz : IsNzFamily isoLine 1 isoFam := by
  refine ⟨le_rfl, fun _ => Submodule.subset_span rfl, ?_, ?_⟩
  · refine linearIndependent_unique_iff.2 ?_
    intro h
    have := congrFun h 0
    simp [isoFam, isoVec] at this
  · rw [span_isoFam, AddSubgroup.relIndex_self]
    exact one_ne_zero

end Gauss

end GroundTheory.Heights₂.Heights.NineStatements
