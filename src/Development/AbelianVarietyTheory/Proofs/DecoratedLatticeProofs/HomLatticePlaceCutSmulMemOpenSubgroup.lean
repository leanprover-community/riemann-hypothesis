module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LatLevel


open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes in
theorem exists_finset_of_nhds_zero {F : Type} [Field F] [NumberField F] (V : Set (Af F)) (hV : IsOpen V)
    (h0 : (0 : Af F) ∈ V) :
    ∃ s : Finset (HeightOneSpectrum (𝓞 F)), ∀ γ ∈ Formalism.MainNotions.StandardLattice.intAf F, (∀ v ∈ s, evalV F v γ = 0) → γ ∈ V := by
  set f := RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite with hf
  have hc : Continuous f := (RestrictedProduct.isOpenEmbedding_structureMap
    (fun v => Valued.isOpen_integer _)).continuous
  have hO : IsOpen (f ⁻¹' V) := hV.preimage hc
  have hz : (0 : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F) ∈ f ⁻¹' V := h0
  obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.mp hO _ hz
  refine ⟨I, fun γ hγ hs => ?_⟩
  let x : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F := fun v => ⟨γ v, hγ v⟩
  have hx : x ∈ (I : Set _).pi u := by
    intro v hv
    have h1 : x v = 0 := Subtype.ext (hs v hv)
    rw [h1]
    exact (hu v hv).2
  have := hsub hx
  exact this

end GlobalTheory.LatLevel

namespace GlobalTheory.LatLevel

theorem smul_mem_open_of_vanish : ∀ (D : D7) (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (P : Pl D → Prop) (U : AddSubgroup (WO S T)), IsOpen (U : Set (WO S T)) → ∀ u ∈ latO S T LS LT P, ∃ s : Finset (Pl D), ∀ γ ∈ intAf D.host.F, (∀ v ∈ s, evalV D.host.F v γ = 0) → pairA D.host.F 0 γ • u ∈ U := by
  intro D S T LS LT P U hU u _hu
  letI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have hg : Continuous fun β : Af D.host.F => (pairA D.host.F 0 β) • u := by
    have h1 : Continuous fun β : Af D.host.F => pairA D.host.F 0 β :=
      continuous_const.prodMk continuous_id
    exact h1.smul continuous_const
  obtain ⟨s, hs⟩ := exists_finset_of_nhds_zero _ (hU.preimage hg)
    (by
      show pairA D.host.F 0 0 • u ∈ (U : Set (WO S T))
      have : pairA D.host.F 0 0 = 0 := rfl
      rw [this, zero_smul]
      exact U.zero_mem)
  exact ⟨s, fun γ hγ hv => hs γ hγ hv⟩

end GlobalTheory.LatLevel
