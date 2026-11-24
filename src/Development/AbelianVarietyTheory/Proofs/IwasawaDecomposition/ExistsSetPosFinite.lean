module

public import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpqLocallyCompactGroup
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
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

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

namespace GlobalTheory.Mem.VolUnique

theorem haar_eq_of_eq_on_set {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ μ' : Measure G) [μ.IsHaarMeasure] [μ'.IsHaarMeasure] (S : Set G) (h : μ S = μ' S)
    (h0 : μ' S ≠ 0) (ht : μ' S ≠ ⊤) : μ = μ' := by
  have hμ := Measure.isMulLeftInvariant_eq_smul μ μ'
  have hc : ((Measure.haarScalarFactor μ μ' : NNReal) : ENNReal) = 1 := by
    have h1 : μ S = (Measure.haarScalarFactor μ μ' : ENNReal) * μ' S := by
      conv_lhs => rw [hμ]
      simp
    rw [h] at h1
    exact ((ENNReal.mul_left_inj h0 ht).1 (by rw [one_mul]; exact h1)).symm
  have hc' : Measure.haarScalarFactor μ μ' = 1 := by exact_mod_cast hc
  rw [hμ, hc', one_smul]

theorem exists_set_pos_finite (cd : CDHaar) (P Q : ℕ) :
    ∃ B : Set (UpqT P Q), MeasurableSet B ∧ cd.cd P Q B ≠ 0 ∧ cd.cd P Q B ≠ ⊤ := by
  obtain ⟨_, _, _, _, _, _⟩ := GlobalTheory.UpqTopology.upq_lcsc P Q
  haveI := cd.haar P Q
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : UpqT P Q)
  exact ⟨K, hK.measurableSet, (Measure.measure_pos_of_mem_nhds _ hK1).ne', hK.measure_lt_top.ne⟩

theorem volMeas_unique : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (I : Type) [Fintype I] (τ : I → (E →+* ℂ)) (cd : CDHaar) (W : HSpace E), IsCMFam τ → W.SigOK → ∀ μ μ', IsVolMeasF cm τ cd W (fun ρ => (W.sig (τ ρ)).1) (fun ρ => (W.sig (τ ρ)).2) μ → IsVolMeasF cm τ cd W (fun ρ => (W.sig (τ ρ)).1) (fun ρ => (W.sig (τ ρ)).2) μ' → μ = μ' := by
  intro F E _ _ _ _ _ _ cm I _ τ cd W _ _ μ μ' hμ hμ'
  obtain ⟨hH, ⟨θ, hθ⟩, hall⟩ := hμ
  obtain ⟨hH', -, hall'⟩ := hμ'
  obtain ⟨⟨A, hA⟩, hB⟩ := hall θ hθ
  have hB' := (hall' θ hθ).2 A hA
  have hB := hB A hA
  choose B hBm hB0 hBt using fun ρ : I => exists_set_pos_finite cd (W.sig (τ ρ)).1 (W.sig (τ ρ)).2
  obtain ⟨_, _, _⟩ := GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary F E cm.sig W.rank W.gram
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : IsTopologicalGroup (HA (AF F) cm.sig W.gram) :=
    inferInstanceAs (IsTopologicalGroup (HR (AF F) cm.sig W.gram))
  haveI : BorelSpace (HA (AF F) cm.sig W.gram) := ⟨rfl⟩
  refine haar_eq_of_eq_on_set μ μ' _ ((hB B hBm).trans (hB' B hBm).symm) ?_ ?_
  · rw [hB' B hBm]
    exact Finset.prod_ne_zero_iff.2 fun ρ _ => hB0 ρ
  · rw [hB' B hBm]
    exact ENNReal.prod_ne_top fun ρ _ => hBt ρ

end GlobalTheory.Mem.VolUnique
