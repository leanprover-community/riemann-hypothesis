module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftQMk
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineTwistCrystallineCharacterJumpsShift
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JumpIffMultNeZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CentralIdemCoeff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GlobalCore

@[expose] public section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module Classical

noncomputable section

namespace GlobalTheory.UseLoc.TwistCrysW

theorem isTwistRep_twist (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (k : ℕ)
    (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) :
    IsTwistRep (tableLineDegreeTwo.charL (LL := ↥C.LL.1) θ) (matRep (TruncatedSeriesCountingIdentities.locC C M)) (repV C (twistM (locOC C M) θ)) := by
  refine ⟨LinearEquiv.refl _ _, fun g v => ?_⟩
  have hent : ∀ a b, (mapM (algebraMap ↥(OL C.LL) ↥C.LL.1) (twistM (locOC C M) θ) g) a b =
      algebraMap ↥(OL C.LL) ↥C.LL.1 ((θ g : (↥(OL C.LL))ˣ) : ↥(OL C.LL)) * (TruncatedSeriesCountingIdentities.locC C M g) a b := by
    intro a b
    change algebraMap ↥(OL C.LL) ↥C.LL.1 (((θ g : (↥(OL C.LL))ˣ) : ↥(OL C.LL)) * (locOC C M g) a b) = _
    rw [map_mul]
    rfl
  change (mapM (algebraMap ↥(OL C.LL) ↥C.LL.1) (twistM (locOC C M) θ) g).mulVec v =
    algebraMap ↥(OL C.LL) ↥C.LL.1 ((θ g : (↥(OL C.LL))ˣ) : ↥(OL C.LL)) • (TruncatedSeriesCountingIdentities.locC C M g).mulVec v
  funext a
  simp only [Matrix.mulVec, dotProduct, hent, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem isCrys_and_multV : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (k : ℕ) (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ), IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C M)) → IsCrys (Br.PD D.loc D.nbr i w hw) (Formalism.WeaklyAdmissibleFiltrations.charRep (tableLineDegreeTwo.charL (LL := ↥C.LL.1) θ)) → IsCrys (Br.PD D.loc D.nbr i w hw) (repV C (twistM (locOC C M) θ)) ∧ ∀ (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1) (b : ℤ), multV (Br.PD D.loc D.nbr i w hw) (Formalism.WeaklyAdmissibleFiltrations.charRep (tableLineDegreeTwo.charL (LL := ↥C.LL.1) θ)) τ b ≠ 0 → ∀ a : ℤ, multV (Br.PD D.loc D.nbr i w hw) (repV C (twistM (locOC C M) θ)) τ (a + b) = multV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C M)) τ a := by
  intro D i w hw C k M θ hM hθ
  have key := GlobalTheory.TwistRepCrys.isCrys_and_multV_twist (D.nd.l i) (D.loc _) (D.locA _) (D.locT _) (D.nbr i w hw).Kw C.LL
    (Fin k → ↥C.LL.1) (matRep (TruncatedSeriesCountingIdentities.locC C M)) (Fin k → ↥C.LL.1) (repV C (twistM (locOC C M) θ))
    (tableLineDegreeTwo.charL (LL := ↥C.LL.1) θ) (isTwistRep_twist D i w hw C k M θ) hθ hM
  refine ⟨key.1, fun τ b hb a => key.2 τ a b ?_⟩
  exact (GlobalTheory.Per.JumpMult.jump_iff_mult_ne_zero (D.nd.l i) (D.loc _) (D.locA _) (D.locT _) (D.nbr i w hw).Kw C.LL
    ↥C.LL.1 (Formalism.WeaklyAdmissibleFiltrations.charRep (tableLineDegreeTwo.charL (LL := ↥C.LL.1) θ)) τ b).2.2.2 hb

end GlobalTheory.UseLoc.TwistCrysW
