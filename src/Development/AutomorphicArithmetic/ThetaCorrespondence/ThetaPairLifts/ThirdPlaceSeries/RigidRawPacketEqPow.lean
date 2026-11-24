module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistDataAgreeAcrossCoefficients
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotMemSqOfRamificationIdx
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsGoodPlacesEveryConjugate
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RawPackEqPow
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotBaseCondFalse
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCharDescent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunKilled

@[expose] public section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.HeightCounting.Rigid
theorem rigid_raw_packet_eq_pow_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ (D₁ D₂ : D7) (p : TwPack D₁) (A : Finset (PlE D₁.host)) (ι : GlobalTheory.Mem.Top.TwChar.RootIso D₁ p.1 p.2.2.1) (χ : HChar D₁.host.E) (cf : CharFrame D₂) (C : NChoice D₂) (tp : TupTied D₂ cf C) (v : D₂.what₂.places.Pl), SameExport D₁ D₂ → BlochKatoReduction.Gen.PsiOk p.1 A p.2.1 p.2.2.1 p.2.2.2 → GlobalTheory.Mem.Top.TwChar.FrobPick p.1 p.2.1 p.2.2.1 p.2.2.2 ι χ → PsiChoiceCompatible D₂ cf C tp → TwistedAt D₂ v → HEq (C.twI v) p.1 → HEq (C.Q v) p.2.1 → C.k' v = p.2.2.1 → HEq (tp.psi v) χ → (∀ z : ℂ, z ^ D₂.what₂.places.resChar v ^ C.k' v = 1 → ∃ x : D₂.what₂.LL, D₂.what₂.embLL x = z) → ∃ a : ℤ, Nat.Coprime a.natAbs (D₁.ntw.l p.1) ∧ HEq (rawPack C v) (GlobalTheory.HeightCounting.twPackPow D₁ a p) := by
  intro hc D₁ D₂ p A ι χ cf C tp v h hO hF hT htw hi hQ hk hχ hL
  obtain ⟨ψ₂, ι₂, A₂, hO₂, hF₂, hl, hpow⟩ := transfer h p A ι χ hO hF (C.twI v) (C.Q v) (C.k' v) (tp.psi v) hi hQ hk hχ
  obtain ⟨a, ha, hψ⟩ := pow_of_tied hc.cheb cf C tp v ψ₂ ι₂ hF₂ hT htw hO₂.2.2.1 hL
  refine ⟨a, by rw [Int.natAbs_natCast, ← hl]; exact ha, ?_⟩
  have e : rawPack C v = (⟨C.twI v, C.Q v, C.k' v, ψ₂ ^ (a : ℤ)⟩ : TwPack D₂) := by
    rw [zpow_natCast, ← hψ]
    rfl
  rw [e]
  exact hpow a
end GlobalTheory.HeightCounting.Rigid
end
end
end
