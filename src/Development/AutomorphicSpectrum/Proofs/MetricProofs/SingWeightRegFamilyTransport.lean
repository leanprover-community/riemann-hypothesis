module

import Development.WeilBound.CoreStatements.PluriharmonicCharts.XCGradAtlas
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
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
public import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PartialFlagBlocks
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Operations
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.IsFieldIntersection
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FA GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.Transport

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem isOpen_compl_bdry (A : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ)
    (hs : IsSection A L s) : IsOpen (bdry s)ᶜ := by
  apply PositivityTheory.Xgp.c_grad_atlas.isOpen_compl_bdry <;> assumption

theorem contDiffAt_two {A : FinHolAtlas e X} {U : Set X} {f : X → ℝ} (h : A.SmoothOn U f)
    (hU : IsOpen U) (j : Fin A.n) {y : Fin e → ℂ} (hy : y ∈ (A.chart j).target)
    (hyU : (A.chart j).symm y ∈ U) : ContDiffAt ℝ 2 (f ∘ (A.chart j).symm) y :=
  ((h j).contDiffAt (((A.chart j).isOpen_inter_preimage_symm hU).mem_nhds ⟨hy, hyU⟩)).of_le
    ENat.LEInfty.out

theorem levi_eq_of_sub_re (A : FinHolAtlas e X) (j : Fin A.n) {y : Fin e → ℂ}
    (hy : y ∈ (A.chart j).target) {W : Set X} (hW : IsOpen W) (hyW : (A.chart j).symm y ∈ W)
    {G : X → ℂ} (hG : A.HoloOn W G) {a b : X → ℝ} (hab : ∀ z ∈ W, a z - b z = (G z).re)
    (hb : ContDiffAt ℝ 2 (b ∘ (A.chart j).symm) y) (w : Fin e → ℂ) :
    levi (a ∘ (A.chart j).symm) y w = levi (b ∘ (A.chart j).symm) y w := by
  have hGa : AnalyticAt ℂ (G ∘ (A.chart j).symm) y := hG j y ⟨hy, hyW⟩
  have hre : ContDiffAt ℝ 2 (fun z => ((G ∘ (A.chart j).symm) z).re) y :=
    Complex.reCLM.contDiff.contDiffAt.comp y hGa.restrictScalars.contDiffAt
  have hev : (a ∘ (A.chart j).symm) =ᶠ[𝓝 y]
      fun z => (b ∘ (A.chart j).symm) z + 1 * ((G ∘ (A.chart j).symm) z).re := by
    have hmem : ∀ᶠ z in 𝓝 y, (A.chart j).symm z ∈ W :=
      ((A.chart j).continuousAt_symm hy).eventually_mem (hW.mem_nhds hyW)
    filter_upwards [hmem] with z hz
    have := hab _ hz
    simp only [Function.comp]
    linarith
  rw [levi_congr hev, levi_add_smul 1 hb hre, levi_re_analytic hGa]
  ring

theorem exists_re_base {A : FinHolAtlas e X} {P : LocPot X} (hP : IsPotential A P) {x u : X}
    (hu : u ∈ P.U x) : ∃ W : Set X, IsOpen W ∧ u ∈ W ∧ ∃ G : X → ℂ, A.HoloOn W G ∧
      ∀ z ∈ W, P.φ x z - P.φ u z = (G z).re := by
  obtain ⟨W, oW, mW, G, hG, hW⟩ := hP.2 x u u ⟨hu, P.mem_U u⟩
  refine ⟨W ∩ P.U x ∩ P.U u, (oW.inter (P.isOpen_U x)).inter (P.isOpen_U u),
    ⟨⟨mW, hu⟩, P.mem_U u⟩, G, fun k => (hG k).mono fun y hy => ⟨hy.1, hy.2.1.1⟩, ?_⟩
  rintro z hz
  exact hW z hz

theorem exists_re_change {A : FinHolAtlas e X} {th th' : LocPot X} (hth : IsPotential A th)
    (hsame : SamePot A Set.univ th th') {x u : X} (hu : u ∈ th.U x) :
    ∃ W : Set X, IsOpen W ∧ u ∈ W ∧ ∃ G : X → ℂ, A.HoloOn W G ∧
      ∀ z ∈ W, th.φ x z - th'.φ u z = (G z).re := by
  obtain ⟨W, oW, mW, G₁, h₁, e₁⟩ := exists_re_base hth hu
  obtain ⟨V, oV, mV, G₂, h₂, e₂⟩ := hsame u (Set.mem_univ _)
  refine ⟨W ∩ V, oW.inter oV, ⟨mW, mV⟩, fun z => G₁ z + G₂ z, fun k => ?_, ?_⟩
  · exact ((h₁ k).mono (by exact fun y hy => ⟨hy.1, hy.2.1⟩)).add ((h₂ k).mono fun y hy => ⟨hy.1, hy.2.2⟩)
  · rintro z ⟨a, b⟩
    have h1 := e₁ z a
    have h2 := e₂ z b
    simp only [Complex.add_re]
    linarith

theorem isPshOn_transport {A : FinHolAtlas e X} {L : LocPot X} {s : X → X → ℂ} {th th' : LocPot X}
    {ph : X → ℝ} (hs : IsSection A L s) (hth : IsPotential A th) (hth' : IsPotential A th')
    (hsame : SamePot A Set.univ th th') (hsm : A.SmoothOn (bdry s)ᶜ ph)
    (hpsh : IsPshOn A (bdry s)ᶜ (th' + LocPot.ofFun ph)) :
    IsPshOn A (bdry s)ᶜ (th + LocPot.ofFun ph) := by
  intro x j y hy w
  obtain ⟨hyt, hyU, hyb⟩ := hy
  have hyx : (A.chart j).symm y ∈ th.U x := hyU.1
  obtain ⟨W, oW, mW, G, hG, hW⟩ := exists_re_change hth hsame hyx
  have h0 := hpsh ((A.chart j).symm y) j y
    ⟨hyt, ⟨th'.mem_U _, Set.mem_univ _⟩, hyb⟩ w
  have hb : ContDiffAt ℝ 2 ((th' + LocPot.ofFun ph).φ ((A.chart j).symm y) ∘ (A.chart j).symm) y :=
    (contDiffAt_two (hth'.1 _) (th'.isOpen_U _) j hyt (th'.mem_U _)).add
      (contDiffAt_two hsm (isOpen_compl_bdry A L s hs) j hyt hyb)
  rw [levi_eq_of_sub_re A j hyt oW mW hG (a := (th + LocPot.ofFun ph).φ x)
    (b := (th' + LocPot.ofFun ph).φ ((A.chart j).symm y)) (fun z hz => by
      have h1 := hW z hz
      show th.φ x z + ph z - (th'.φ _ z + ph z) = _
      linarith) hb w]
  exact h0

theorem isPsh_transport {A : FinHolAtlas e X} {Θ th th' : LocPot X} {f : X → ℝ} {c : ℝ}
    (hΘ : IsPotential A Θ) (hth : IsPotential A th) (hth' : IsPotential A th')
    (hsame : SamePot A Set.univ th th') (hf : A.Smooth f)
    (hpsh : IsPsh A (th' + LocPot.ofFun f + Θ.rsmul c)) :
    IsPsh A (th + LocPot.ofFun f + Θ.rsmul c) := by
  intro x j y hy w
  obtain ⟨hyt, hyU⟩ := hy
  have hyx : (A.chart j).symm y ∈ th.U x := hyU.1.1
  have hyΘ : (A.chart j).symm y ∈ Θ.U x := hyU.2
  obtain ⟨W₁, o₁, m₁, G₁, h₁, e₁⟩ := exists_re_change hth hsame hyx
  obtain ⟨W₂, o₂, m₂, G₂, h₂, e₂⟩ := exists_re_base hΘ hyΘ
  have h0 := hpsh ((A.chart j).symm y) j y
    ⟨hyt, ⟨⟨th'.mem_U _, Set.mem_univ _⟩, Θ.mem_U _⟩⟩ w
  have hb : ContDiffAt ℝ 2
      ((th' + LocPot.ofFun f + Θ.rsmul c).φ ((A.chart j).symm y) ∘ (A.chart j).symm) y :=
    ((contDiffAt_two (hth'.1 _) (th'.isOpen_U _) j hyt (th'.mem_U _)).add
      (contDiffAt_two hf isOpen_univ j hyt (Set.mem_univ _))).add
      (contDiffAt_const.mul (contDiffAt_two (hΘ.1 _) (Θ.isOpen_U _) j hyt (Θ.mem_U _)))
  have hG : A.HoloOn (W₁ ∩ W₂) fun z => G₁ z + (c : ℂ) * G₂ z := fun k =>
    ((h₁ k).mono (by exact fun y hy => ⟨hy.1, hy.2.1⟩)).add
      ((analyticOnNhd_const (v := (c : ℂ))).mul ((h₂ k).mono fun y hy => ⟨hy.1, hy.2.2⟩))
  rw [levi_eq_of_sub_re A j hyt (o₁.inter o₂) ⟨m₁, m₂⟩ hG
    (a := (th + LocPot.ofFun f + Θ.rsmul c).φ x)
    (b := (th' + LocPot.ofFun f + Θ.rsmul c).φ ((A.chart j).symm y)) (fun z hz => by
      have h1 := e₁ z hz.1
      have h2 := e₂ z hz.2
      show th.φ x z + f z + c * Θ.φ x z -
        (th'.φ _ z + f z + c * Θ.φ _ z) = _
      simp only [Complex.add_re, Complex.re_ofReal_mul]
      rw [← h1, ← h2]
      ring) hb w]
  exact h0

theorem singWeight_regFamily_transport : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (Θ L : LocPot X)
    (s : X → X → ℂ) (th th' : LocPot X) (ph : X → ℝ) (phT : ℝ → X → ℝ) (C₅ C t₀ : ℝ),
    IsPotential A Θ → IsSection A L s → IsPotential A th → IsPotential A th' → SamePot A Set.univ th th' →
    (IsSingWeight A L s th' ph C₅ → IsSingWeight A L s th ph C₅) ∧
      (IsRegFamily A Θ L s th' ph phT C t₀ → IsRegFamily A Θ L s th ph phT C t₀) := by
  intro e X _ A Θ L s th th' ph phT C₅ C t₀ hΘ hs hth hth' hsame
  constructor
  · rintro ⟨_, hsm, hpsh, hb⟩
    exact ⟨hth, hsm, isPshOn_transport hs hth hth' hsame hsm hpsh, hb⟩
  · rintro ⟨h0, h1, hreg⟩
    refine ⟨h0, h1, fun t ht ht' => ?_⟩
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := hreg t ht ht'
    exact ⟨a1, a2, a3, a4, isPsh_transport hΘ hth hth' hsame a1 a5, a6, a7, a8⟩

end GlobalTheory.CompanionTheory.Ar.PB.Transport
