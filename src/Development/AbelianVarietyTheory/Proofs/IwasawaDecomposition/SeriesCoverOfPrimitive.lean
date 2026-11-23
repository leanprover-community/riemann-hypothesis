module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteTwistFrameExtraExcludedOverSmallPrimes
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsReadsAtOfCover
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Choice
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
import Mathlib.RingTheory.PicardGroup
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotBaseCondFalse
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunKilled
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.GoodPartLeTypeSubspace

@[expose] public section

noncomputable section

namespace GlobalTheory.HeightCounting.Up.ChoiceEx

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice

theorem readsAt_conj {D : D7} (hs : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) {i : D.ntw.Tw} {b : Bool} {w : D.what₂.places.Pl}
    (h : ReadsAt i b w) : ReadsAt i (!b) (D.what₂.places.conj w) := fun x => by
  have h2 : IsIntegral ℤ (star ((x : ↥D.LL0) : D.what₂.LL)) :=
    IsIntegral.map_of_comp_eq (RingHom.id ℤ) ((starRingEnd D.what₂.LL).comp (algebraMap ↥D.LL0 D.what₂.LL))
      (RingHom.ext_int _ _) (RingOfIntegers.isIntegral_coe x)
  let y : 𝓞 ↥D.LL0 := ⟨⟨_, hs x⟩, (isIntegral_algebraMap_iff ).1 h2⟩
  have hy : ((y : ↥D.LL0) : D.what₂.LL) = star ((x : ↥D.LL0) : D.what₂.LL) := rfl
  rw [sideEmb_not i b hy, D.conj_val, ← hy]
  exact h y

theorem exists_settings_conj {D : D7} (hs : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0)
    (hc : ∀ w : D.what₂.places.Pl, ∃ i, D.ntw.l i = D.what₂.places.resChar w ∧ GlobalTheory.HeightCounting.SidePl D w i true) :
    ∃ s : D.what₂.places.Pl → D.ntw.Tw, (∀ v, ∃ b, ReadsAt (s v) b v) ∧ ∀ v, s (D.what₂.places.conj v) = s v := by
  choose t _ ht using hc
  have hr : ∀ w, ReadsAt (t w) true w := fun w x => Formalism.L2.emb0_mem_maximalIdeal_iff_val_pos_of_sidePl D w (t w) (ht w) (x : D.LL0)
  obtain ⟨o, ho⟩ := exists_orbitRep (D := D)
  refine ⟨fun v => t (o v), fun v => ?_, fun v => by simp only [(ho v).2]⟩
  rcases (ho v).1 with h | h
  · exact ⟨true, by simpa only [h] using hr v⟩
  · have h1 := readsAt_conj hs (hr (D.what₂.places.conj v))
    rw [D.what₂.places.conj_conj] at h1
    exact ⟨_, by simpa only [h] using h1⟩

end GlobalTheory.HeightCounting.Up.ChoiceEx

end
