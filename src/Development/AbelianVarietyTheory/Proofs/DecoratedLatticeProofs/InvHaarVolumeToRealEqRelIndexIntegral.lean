module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOpenKerUnramMulTame
import Development.AbelianVarietyTheory.Definitions.Foundations.SecondCountableAndT2LocalField
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped ENNReal

namespace GlobalTheory.HaarIdx

open MeasureTheory

theorem inv_toReal_eq_relIndex {Γ : Type*} [Group Γ] [MeasurableSpace Γ] [MeasurableMul Γ] (μ : Measure Γ) [μ.IsMulLeftInvariant]
    (K H : Subgroup Γ) (hHK : H ≤ K) (hH : MeasurableSet (H : Set Γ)) (hK : μ (K : Set Γ) = 1)
    (hn : H.relIndex K ≠ 0) : ((μ (H : Set Γ)).toReal)⁻¹ = (H.relIndex K : ℝ) := by
  have hmeas : ∀ g : Γ, AEMeasurable (fun x => g * x) μ :=
    fun g => (measurable_const_mul g).aemeasurable
  have hpre : ∀ g : Γ, μ ((fun x => g * x) ⁻¹' (H : Set Γ)) = μ H := by
    intro g
    rw [← Measure.map_apply_of_aemeasurable (hmeas g) hH, map_mul_left_eq_self μ g]
  set L := H.subgroupOf K
  haveI : L.FiniteIndex := ⟨hn⟩
  haveI : Fintype (K ⧸ L) := Fintype.ofFinite _
  let C : (K ⧸ L) → Set Γ := fun q => (fun x => ((q.out : K) : Γ)⁻¹ * x) ⁻¹' (H : Set Γ)
  have hcov : (K : Set Γ) = ⋃ q, C q := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe, C]
    constructor
    · intro hx
      refine ⟨(QuotientGroup.mk (⟨x, hx⟩ : K) : K ⧸ L), ?_⟩
      obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul L (⟨x, hx⟩ : K)
      rw [hh]
      have : (((⟨x, hx⟩ : K) * (h : K) : K) : Γ)⁻¹ * x = ((h : K) : Γ)⁻¹ := by
        simp [_root_.mul_inv_rev, mul_assoc]
      rw [this]
      exact H.inv_mem (Subgroup.mem_subgroupOf.mp h.2)
    · rintro ⟨q, hq⟩
      have h1 : ((q.out : K) : Γ)⁻¹ * x ∈ K := hHK hq
      have h2 : ((q.out : K) : Γ) ∈ K := (q.out : K).2
      have := K.mul_mem h2 h1
      simpa [mul_assoc] using this
  have hdisj : Pairwise (Function.onFun (AEDisjoint μ) C) := by
    intro q q' hqq'
    apply Disjoint.aedisjoint
    rw [Set.disjoint_left]
    intro y hy hy'
    simp only [Set.mem_preimage, SetLike.mem_coe, C] at hy hy'
    apply hqq'
    rw [← Quotient.out_eq q, ← Quotient.out_eq q']
    change (QuotientGroup.mk q.out : K ⧸ L) = QuotientGroup.mk q'.out
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have := H.mul_mem hy (H.inv_mem hy')
    simpa [_root_.mul_inv_rev, mul_assoc] using this
  have hnull : ∀ q, NullMeasurableSet (C q) μ := fun q =>
    (hmeas _).nullMeasurableSet_preimage hH
  have hsum : μ (K : Set Γ) = (Fintype.card (K ⧸ L) : ℝ≥0∞) * μ H := by
    rw [hcov, measure_iUnion₀ hdisj hnull, tsum_fintype]
    simp [C, hpre, Finset.sum_const, nsmul_eq_mul]
  have hcard : (Fintype.card (K ⧸ L) : ℕ) = H.relIndex K := by
    rw [Fintype.card_eq_nat_card]; rfl
  rw [hK, hcard] at hsum
  have hne : μ (H : Set Γ) ≠ ⊤ := by
    intro h; rw [h, ENNReal.mul_top (by exact_mod_cast hn)] at hsum; exact ENNReal.one_ne_top hsum
  have hr := congrArg ENNReal.toReal hsum
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_one] at hr
  have hpos : (μ (H : Set Γ)).toReal ≠ 0 := by
    intro h; rw [h, mul_zero] at hr; exact one_ne_zero hr
  field_simp
  linarith [hr]

end GlobalTheory.HaarIdx

namespace GlobalTheory


theorem QTw.QExt.m_inv_toReal_eq_relIndex : ∀ {D : D7} {c : Comm D} {v : VCom c} {B : GlobalTheory.Fam.Base c} {PP : Formalism.L2.DIV.Pl D.host.E} (G : GlobalTheory.QTw.QGeo v B PP) (χ : ℕ → (AE D)ˣ →* Circle) (E : GlobalTheory.QTw.QExt G χ) (j : ℕ) (H : Subgroup (GL (XIx (Fin D.R.k) (Fin D.R.t) j) G.k)), H ≤ KO G.k _ → MeasurableSet (H : Set (GL (XIx (Fin D.R.k) (Fin D.R.t) j) G.k)) → H.relIndex (KO G.k _) ≠ 0 → ((((E.m j H).toReal)⁻¹ : ℝ) : ℂ) = (H.relIndex (KO G.k _) : ℂ) := by
  intro D c v B PP G χ E j H hHK hH hn
  letI : MeasurableSpace (Matrix (XIx (Fin D.R.k) (Fin D.R.t) j) (XIx (Fin D.R.k) (Fin D.R.t) j) G.k) := Formalism.DoubleCosetMeasures.instMeasMat
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := G.k)
  haveI : BorelSpace (GL (XIx (Fin D.R.k) (Fin D.R.t) j) G.k) := GlobalTheory.SplitFlip.borel_GL
  haveI : SecondCountableTopology (GL (XIx (Fin D.R.k) (Fin D.R.t) j) G.k) := GlobalTheory.SplitFlip.secondCountable_GL
  haveI : MeasurableMul (GL (XIx (Fin D.R.k) (Fin D.R.t) j) G.k) := ⟨
    fun g => (continuous_const.mul continuous_id).measurable,
    fun g => (continuous_id.mul continuous_const).measurable⟩
  haveI := (E.haar j).1
  rw [HaarIdx.inv_toReal_eq_relIndex (E.m j) _ H hHK hH (E.haar j).2 hn]
  push_cast
  rfl

end GlobalTheory
