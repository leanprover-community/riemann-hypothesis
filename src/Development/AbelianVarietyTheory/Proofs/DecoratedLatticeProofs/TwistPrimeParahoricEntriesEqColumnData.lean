module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalVolumeAgreesRowSubgroupUnitaryStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldingIntegralTwistPrimeEqDeepFiniteSumStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge

namespace GlobalTheory.EntryAtTwist

theorem bas_eq_one {R : Ranks} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (s : ℕ) (W : TwData k) (j c : ℕ) (h : j + c = s + 1) : (W.T s R).bas j c h = 1 := by
  first | rfl | (simp [TwData.T, twistChain, Chain.ofTwist])

theorem entryAgree : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → cst.Ok → AtTwist (R := R) sel mu cst σ₀ P ι s W → ∀ (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m), L.Ok Ch sel mu cst G s → EntryAgree Ch sel mu cst σ₀ P ι s W ν L := by
  intro X Pr R Ch sel S₀ mu cst σ₀ P k _ _ _ _ ι s W _ _ ν hν hcst hAt L G hL
  have hSum := GlobalTheory.T.unfoldingIntegral_twistPrime_eq_deep_finite_sum X Pr R Ch sel S₀ mu cst σ₀ P k ι s W ν hν hcst hAt
  have hVol := GlobalTheory.T.local_volume_agrees_row_subgroup_unitary X Pr R Ch sel S₀ mu cst σ₀ P k ι s W ν hν hcst hAt
  intro j c h al be g g' hg hg' e' e he' he x
  have hnm := hAt.nmem
  obtain ⟨A₀, B₀, hAB⟩ := hSum j c h (L.h j al P) (L.h (j + 1) be P) g g' hg hg'
    (hL.boundQ j al P hnm) (hL.boundQ (j + 1) be P hnm) (hL.depthQ' P hnm)
  have hF := hAB (max A₀ cst.A) (max B₀ cst.B) (le_max_left _ _) (le_max_left _ _) e' e he' he x
  rw [hL.deep _ _ (le_max_right _ _) (le_max_right _ _) j (by omega) al be P] at hF
  have hV := (hVol (j + 1) c (by omega) (L.h (j + 1) be P) g' hg').1
  simp only [Chain.entry, xi, bas_eq_one]
  rw [hF, Complex.ofReal_inv, hV]
  simp only [XiAt, map_mul, map_inv₀]
  ring

end GlobalTheory.EntryAtTwist
