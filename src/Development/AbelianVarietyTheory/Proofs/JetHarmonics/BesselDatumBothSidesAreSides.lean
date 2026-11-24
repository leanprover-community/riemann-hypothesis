module

public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPrAlt
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsHarishChandraParamOfTypeOfUnitaryW
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsQuotientMeasureBesselPeriodSubgroupUnitary
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsHaarOnIffGroupsUnitaryUnipotent
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

open Matrix MeasureTheory Finset in
open scoped InnerProductSpace ENNReal in
private theorem exists_quotient_side_of_isType_lemma (k r : ℕ) (W : Type) [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] (hk : 1 ≤ k)
    (z : Fin (2 * r + k + 1) → ℂ) (π : _root_.Formalism.FourierDecayAlt.B.Mat k r → W →L[ℂ] W) (u : ℕ → ℝ)
    (μW μN μG : Measure (_root_.Formalism.QuantumDeterminants.Mt k r)) (hz : _root_.Formalism.QuantumDeterminants.inWb k r z) (hT : 0 < _root_.Formalism.QuantumDeterminants.Tz k r z)
    (hW : _root_.Formalism.FourierDecayAlt.B.IsHaarOn (_root_.Formalism.QuantumDeterminants.UWset k r z) μW) (hN : _root_.Formalism.FourierDecayAlt.B.IsHaarOn (_root_.Formalism.QuantumDeterminants.Nset k r) μN)
    (hG : _root_.Formalism.FourierDecayAlt.B.IsHaarOn (_root_.BranchingSupport.GG k r) μG) (hπ : _root_.Formalism.FourierDecayAlt.Q.IsType k r z π u) :
    ∃ ν, _root_.BranchingSupport.SideG k r z π u μW μN μG ν := by
  have hW' : _root_.PI.BesselPeriodGGP.IsHaarOn (_root_.Formalism.QuantumDeterminants.UWset k r z) μW :=
    ((_root_.GlobalTheory.HaarNotions.isHaarOn_iff_groups k r μW).2.2 z hz hT hk).2 hW
  have hN' : _root_.PI.BesselPeriodGGP.IsHaarOn (_root_.Formalism.QuantumDeterminants.Nset k r) μN :=
    ((_root_.GlobalTheory.HaarNotions.isHaarOn_iff_groups k r μN).2.1).2 hN
  have hG' : _root_.PI.BesselPeriodGGP.IsHaarOn (_root_.BranchingSupport.GG k r) μG :=
    ((_root_.GlobalTheory.HaarNotions.isHaarOn_iff_groups k r μG).1).2 hG
  obtain ⟨ν, hν⟩ :=
    _root_.GlobalTheory.exists_isQuotMeas_bessel_subgroup k r z μW μN μG hz hT hW' hN' hG'
  obtain ⟨u₀, hu₀⟩ := _root_.GlobalTheory.besType_hcParam k r W z π u hz hT hπ
  exact ⟨ν, hz, hT, ⟨u₀, hu₀⟩, hπ.2.2.2.2.2, hW', hN', hG', hν⟩


open Matrix MeasureTheory Finset in
open scoped InnerProductSpace ENNReal in
theorem _root_.GlobalTheory.exists_sideG_both_of_isType : ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type)
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq]
    (D : _root_.Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (u u' : ℕ → ℝ), _root_.Formalism.FourierDecayAlt.Q.IsType k r D.z D.π u →
    _root_.Formalism.FourierDecayAlt.Q.IsType k r D.z' D.π' u' → ∃ νq νq',
      _root_.BranchingSupport.SideG k r D.z D.π u D.μW D.μN D.μG νq ∧
        _root_.BranchingSupport.SideG k r D.z' D.π' u' D.μW' D.μN D.μG νq' := by
  intro k r Wp _ _ _ _ Wq _ _ _ _ D u u' hp hq
  obtain ⟨z, z', π, π', μG, μW, μN, μW', _, _, hk, hz, hz', hT, hT', _, _, _, _, _, _, hG, hW,
    hN, hW', _, _, _, _⟩ := D
  obtain ⟨ν, hν⟩ := exists_quotient_side_of_isType_lemma k r Wp hk z π u μW μN μG hz hT hW hN hG hp
  obtain ⟨ν', hν'⟩ :=
    exists_quotient_side_of_isType_lemma k r Wq hk z' π' u' μW' μN μG hz' hT' hW' hN hG hq
  exact ⟨ν, ν', hν, hν'⟩

end GlobalTheory
