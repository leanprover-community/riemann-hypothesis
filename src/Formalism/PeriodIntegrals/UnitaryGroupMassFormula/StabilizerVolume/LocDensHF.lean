module

import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensHF
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensHSt
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.HenselCountHolds
import Aesop.Main
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace PI.VolStabS

open MeasureTheory Topology Filter Set Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

section Core

variable {V X Y : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V]
  [MeasurableSpace V] [BorelSpace V] [AddCommGroup X] [TopologicalSpace X]
  [IsTopologicalAddGroup X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]

theorem fib_of_ratio (μ : Measure V) (ν : Measure X) [ν.IsAddHaarMeasure]
    (f : V → Y) (ι : X → Y) (hι : Function.Injective ι) (G : V → X) (hGc : Continuous G)
    (hfG : ∀ x, f x = ι (G x)) (U : Set V) (B : Set X) (fib : X → Measure V)
    (hfib : IsFibreFamily μ f ι U ν B fib) (T : X) (hB : B ∈ 𝓝 T) (Nb : Set X) (hNb : Nb ∈ 𝓝 T)
    (hNbU : ∀ x, G x ∈ Nb → x ∈ U) (Q : Set V) (hQo : IsOpen Q) (hQcl : IsClosed Q)
    (hQc : IsCompact Q) (H : ℕ → AddSubgroup X) (hHo : ∀ n, IsOpen (H n : Set X))
    (hHc : ∀ n, IsCompact (H n : Set X)) (hHb : ∀ N' ∈ 𝓝 (0 : X), ∃ n, (H n : Set X) ⊆ N')
    (κ : ℝ) (hratio : ∀ n, μ.real (Q ∩ G ⁻¹' {z | z - T ∈ H n}) = κ * ν.real (H n)) :
    ∫ x, Q.indicator (1 : V → ℂ) x ∂(fib T) = (κ : ℂ) := by
  apply (config := { allowSynthFailures := true }) PI.VolStabSW.fib_of_ratio <;> assumption

end Core

section Lat

variable {V X : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [MeasurableSpace V] [BorelSpace V] [AddCommGroup X] [TopologicalSpace X]
  [IsTopologicalAddGroup X] [MeasurableSpace X] [BorelSpace X]

omit [TopologicalSpace V] [IsTopologicalAddGroup V] [MeasurableSpace V] [BorelSpace V]
  [TopologicalSpace X] [IsTopologicalAddGroup X] [MeasurableSpace X] [BorelSpace X] in
theorem cos_inter_eq (Λ0 : AddSubgroup V) (Hn : AddSubgroup X) (G : V → X) (y : V) (T : X) :
    {x | x - y ∈ Λ0} ∩ G ⁻¹' {z | z - T ∈ Hn} = (fun x => -y + x) ⁻¹' hlev Λ0 Hn G y T := by
  ext x
  simp only [mem_inter_iff, mem_setOf_eq, mem_preimage, hlev, neg_add_eq_sub, add_sub_cancel]

theorem cos_ratio (μ : Measure V) (ν : Measure X) [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]
    (Λ : ℕ → AddSubgroup V) (H : ℕ → AddSubgroup X) (hΛo : ∀ n, IsOpen (Λ n : Set V))
    (hΛa : Antitone Λ) (hHo : ∀ n, IsOpen (H n : Set X)) (hHc : ∀ n, IsCompact (H n : Set X))
    (D : V →+ X) (hD : ∀ n, (Λ n).map D = H n) (G : V → X) (y : V)
    (hG : ∀ n, ∀ Z ∈ Λ 0, ∀ W ∈ Λ n, G (y + Z + W) - G (y + Z) - D W ∈ H (n + 1))
    (T : X) (hyT : G y - T ∈ H 0) (n : ℕ) :
    μ ({x | x - y ∈ Λ 0} ∩ G ⁻¹' {z | z - T ∈ H n}) * ν (H 0) = μ (Λ 0) * ν (H n) := by
  rw [cos_inter_eq, measure_preimage_add]
  have hh : T - G y ∈ H 0 := by
    have := (H 0).neg_mem hyT
    rwa [neg_sub] at this
  exact hensel_main μ ν Λ H hΛo hΛa hHo hHc D hD G y hG T hh n

end Lat

section Fin

variable {V X Y : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V]
  [MeasurableSpace V] [BorelSpace V] [AddCommGroup X] [TopologicalSpace X]
  [IsTopologicalAddGroup X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]

theorem fibCos (μ : Measure V) (ν : Measure X) [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]
    (f : V → Y) (ι : X → Y) (hι : Function.Injective ι) (G : V → X) (hGc : Continuous G)
    (hfG : ∀ x, f x = ι (G x)) (U : Set V) (B : Set X) (fib : X → Measure V)
    (hfib : IsFibreFamily μ f ι U ν B fib) (T : X) (hB : B ∈ 𝓝 T) (Nb : Set X) (hNb : Nb ∈ 𝓝 T)
    (hNbU : ∀ x, G x ∈ Nb → x ∈ U)
    (Λ : ℕ → AddSubgroup V) (H : ℕ → AddSubgroup X) (hΛo : ∀ n, IsOpen (Λ n : Set V))
    (hΛc : ∀ n, IsCompact (Λ n : Set V)) (hΛa : Antitone Λ) (hHo : ∀ n, IsOpen (H n : Set X))
    (hHc : ∀ n, IsCompact (H n : Set X)) (hHb : ∀ N' ∈ 𝓝 (0 : X), ∃ n, (H n : Set X) ⊆ N')
    (D : V →+ X) (hD : ∀ n, (Λ n).map D = H n) (y : V)
    (hG : ∀ n, ∀ Z ∈ Λ 0, ∀ W ∈ Λ n, G (y + Z + W) - G (y + Z) - D W ∈ H (n + 1))
    (hyT : G y - T ∈ H 0) :
    ∫ x, {x | x - y ∈ Λ 0}.indicator (1 : V → ℂ) x ∂(fib T) =
      (((μ (Λ 0 : Set V)) / ν (H 0)).toReal : ℂ) := by
  have hQe : {x | x - y ∈ Λ 0} = (fun x => x + -y) ⁻¹' (Λ 0 : Set V) := by
    ext x; simp [sub_eq_add_neg]
  have hQo : IsOpen {x | x - y ∈ Λ 0} := (hΛo 0).preimage (continuous_id.sub continuous_const)
  have hQcl : IsClosed {x | x - y ∈ Λ 0} :=
    (AddSubgroup.isClosed_of_isOpen _ (hΛo 0)).preimage (continuous_id.sub continuous_const)
  have hQc : IsCompact {x | x - y ∈ Λ 0} := by
    have : {x | x - y ∈ Λ 0} = (fun w => w + y) '' (Λ 0 : Set V) := by
      ext z
      simp only [mem_setOf_eq, mem_image, SetLike.mem_coe]
      constructor
      · intro hz
        exact ⟨z - y, hz, by abel⟩
      · rintro ⟨w, hw, rfl⟩
        simpa using hw
    rw [this]
    exact (hΛc 0).image (continuous_id.add continuous_const)
  have hν0 : 0 < ν.real (H 0) := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos ((hHo 0).measure_pos ν ⟨0, (H 0).zero_mem⟩).ne'
      (hHc 0).measure_lt_top.ne
  have hratio : ∀ n, μ.real ({x | x - y ∈ Λ 0} ∩ G ⁻¹' {z | z - T ∈ H n}) =
      μ.real (Λ 0 : Set V) / ν.real (H 0) * ν.real (H n) := by
    intro n
    have e := cos_ratio μ ν Λ H hΛo hΛa hHo hHc D hD G y hG T hyT n
    have e' := congrArg ENNReal.toReal e
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul] at e'
    simp only [← measureReal_def] at e'
    field_simp
    linarith
  rw [fib_of_ratio μ ν f ι hι G hGc hfG U B fib hfib T hB Nb hNb hNbU _ hQo hQcl hQc H hHo hHc
    hHb _ hratio, ENNReal.toReal_div, measureReal_def, measureReal_def]

end Fin

theorem fibLat_holds : FibLat := by
  intro V X Y _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ μ ν hμ hν f ι hι G hGc hfG U B fib hfib T hB Nb hNb
    hNbU L hLo hLc Λ H hΛL hΛo hΛc hΛa hHo hHc hHb hyp
  have := hμ
  have := hν
  have hLcl : IsClosed (L : Set V) := AddSubgroup.isClosed_of_isOpen _ hLo
  have hScl : ∀ n, IsClosed {z | z - T ∈ H n} := fun n =>
    (AddSubgroup.isClosed_of_isOpen _ (hHo n)).preimage (continuous_id.sub continuous_const)
  set Pn : ℕ → Set V := fun n => (L : Set V) ∩ G ⁻¹' {z | z - T ∈ H n} with hPndef
  have hPcl : ∀ n, IsClosed (Pn n) := fun n => hLcl.inter ((hScl n).preimage hGc)
  have hPo : ∀ n, IsOpen (Pn n) := fun n =>
    hLo.inter (((hHo n).preimage (continuous_id.sub continuous_const)).preimage hGc)
  have hPc : ∀ n, IsCompact (Pn n) := fun n => hLc.of_isClosed_subset (hPcl n) inter_subset_left
  have hν0 : 0 < ν.real (H 0) := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos ((hHo 0).measure_pos ν ⟨0, (H 0).zero_mem⟩).ne'
      (hHc 0).measure_lt_top.ne
  by_cases hne : (Pn 0).Nonempty
  · obtain ⟨y0, hy0⟩ := hne
    obtain ⟨D0, hD0, _⟩ := hyp y0 hy0.1 hy0.2
    have hHa : ∀ n, H n ≤ H 0 := by
      intro n
      rw [← hD0, ← hD0]
      exact AddSubgroup.map_mono (hΛa (Nat.zero_le n))
    have hsat : ∀ y ∈ Pn 0, ∀ Z ∈ Λ 0, y + Z ∈ Pn 0 := by
      rintro y ⟨hyL, hyS⟩ Z hZ
      obtain ⟨D, hD, hG⟩ := hyp y hyL hyS
      refine ⟨L.add_mem hyL (hΛL hZ), ?_⟩
      have h1 := hG 0 0 (Λ 0).zero_mem Z hZ
      simp only [add_zero] at h1
      have h2 : D Z ∈ H 0 := hD 0 ▸ AddSubgroup.mem_map_of_mem D hZ
      have hyS' : G y - T ∈ H 0 := hyS
      show G (y + Z) - T ∈ H 0
      have e : G (y + Z) - T = (G (y + Z) - G y - D Z) + D Z + (G y - T) := by abel
      rw [e]
      exact (H 0).add_mem ((H 0).add_mem (hHa 1 h1) h2) hyS'
    have : DiscreteTopology (V ⧸ Λ 0) := QuotientAddGroup.discreteTopology (hΛo 0)
    let q : V → V ⧸ Λ 0 := QuotientAddGroup.mk
    have hq : Continuous q := continuous_quot_mk
    have hfin : (q '' Pn 0).Finite := ((hPc 0).image hq).finite_of_discrete
    set Tf := hfin.toFinset with hTf
    have hmemT : ∀ p, p ∈ Tf ↔ ∃ y ∈ Pn 0, q y = p := by
      intro p
      simp [hTf]
    have hcos : ∀ y, q ⁻¹' {q y} = {x | x - y ∈ Λ 0} := by
      intro y
      ext x
      simp only [mem_preimage, mem_singleton_iff, mem_setOf_eq, q]
      exact QuotientAddGroup.eq_iff_sub_mem
    have hcount : ∀ n, μ (Pn n) * ν (H 0) = (Tf.card : ENNReal) * (μ (Λ 0) * ν (H n)) := by
      intro n
      have hdec : Pn n = ⋃ p ∈ Tf, (Pn n ∩ q ⁻¹' {p}) := by
        ext x
        simp only [mem_iUnion, exists_prop]
        constructor
        · intro hx
          refine ⟨q x, (hmemT _).2 ⟨x, ⟨hx.1, hHa n hx.2⟩, rfl⟩, hx, rfl⟩
        · rintro ⟨_, _, hx, _⟩
          exact hx
      have hdisj : PairwiseDisjoint (↑Tf : Set (V ⧸ Λ 0)) (fun p => Pn n ∩ q ⁻¹' {p}) :=
        fun p _ p' _ hne => ((disjoint_singleton.2 hne).preimage q).mono inter_subset_right
          inter_subset_right
      have hmeas : ∀ p ∈ Tf, MeasurableSet (Pn n ∩ q ⁻¹' {p}) := fun p _ =>
        (hPo n).measurableSet.inter
          ((isOpen_discrete ({p} : Set (V ⧸ Λ 0))).preimage hq).measurableSet
      have hval : ∀ p ∈ Tf, μ (Pn n ∩ q ⁻¹' {p}) * ν (H 0) = μ (Λ 0) * ν (H n) := by
        intro p hp
        obtain ⟨y, hy, rfl⟩ := (hmemT p).1 hp
        obtain ⟨D, hD, hG⟩ := hyp y hy.1 hy.2
        have e : Pn n ∩ q ⁻¹' {q y} = {x | x - y ∈ Λ 0} ∩ G ⁻¹' {z | z - T ∈ H n} := by
          rw [hcos]
          ext x
          simp only [hPndef, mem_inter_iff, mem_setOf_eq, mem_preimage]
          constructor
          · rintro ⟨⟨_, hxS⟩, hxy⟩
            exact ⟨hxy, hxS⟩
          · rintro ⟨hxy, hxS⟩
            refine ⟨⟨?_, hxS⟩, hxy⟩
            have := L.add_mem hy.1 (hΛL hxy)
            rwa [add_sub_cancel] at this
        rw [e]
        exact cos_ratio μ ν Λ H hΛo hΛa hHo hHc D hD G y hG T hy.2 n
      conv_lhs => rw [hdec]
      rw [measure_biUnion_finset hdisj hmeas, Finset.sum_mul, Finset.sum_congr rfl hval,
        Finset.sum_const, nsmul_eq_mul]
    have hreal : ∀ n, μ.real (Pn n) * ν.real (H 0) = (Tf.card : ℝ) * (μ.real (Λ 0 : Set V) * ν.real (H n)) := by
      intro n
      have e' := congrArg ENNReal.toReal (hcount n)
      simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast, ← measureReal_def] at e'
      exact e'
    have hratio : ∀ n, μ.real ((L : Set V) ∩ G ⁻¹' {z | z - T ∈ H n}) =
        μ.real (Pn 0) / ν.real (H 0) * ν.real (H n) := by
      intro n
      have h0 := hreal 0
      have hn := hreal n
      show μ.real (Pn n) = _
      have e0 : μ.real (Pn 0) = (Tf.card : ℝ) * μ.real (Λ 0 : Set V) := by
        have h' : μ.real (Pn 0) * ν.real (H 0) =
            ((Tf.card : ℝ) * μ.real (Λ 0 : Set V)) * ν.real (H 0) := by
          rw [h0]
          ring
        exact mul_right_cancel₀ hν0.ne' h'
      rw [e0]
      field_simp
      linarith
    rw [fib_of_ratio μ ν f ι hι G hGc hfG U B fib hfib T hB Nb hNb hNbU _ hLo hLcl hLc H hHo hHc
      hHb _ hratio, ENNReal.toReal_div, measureReal_def, measureReal_def]
  · have hP0 : Pn 0 = ∅ := not_nonempty_iff_eq_empty.1 hne
    have hP0' : (L : Set V) ∩ G ⁻¹' {z | z - T ∈ H 0} = ∅ := hP0
    rw [hP0', measure_empty, ENNReal.zero_div, ENNReal.toReal_zero, Complex.ofReal_zero]
    have hpre : f ⁻¹' {ι T} = G ⁻¹' {T} := by
      ext x
      simp [hfG, hι.eq_iff]
    have hm : G ⁻¹' {T} ∩ U ∈ ae (fib T) := by
      rw [mem_ae_iff, ← hpre]
      exact hfib.1 T
    have hae : ∀ᵐ x ∂(fib T), (L : Set V).indicator (1 : V → ℂ) x = 0 := by
      filter_upwards [hm] with x hx
      have hxT : G x = T := hx.1
      by_cases hxL : x ∈ (L : Set V)
      · exfalso
        have : x ∈ Pn 0 := ⟨hxL, by
          show G x - T ∈ H 0
          rw [hxT, sub_self]
          exact (H 0).zero_mem⟩
        rw [hP0] at this
        exact this
      · exact indicator_of_notMem hxL _
    rw [integral_congr_ae hae, integral_zero]

end PI.VolStabS
