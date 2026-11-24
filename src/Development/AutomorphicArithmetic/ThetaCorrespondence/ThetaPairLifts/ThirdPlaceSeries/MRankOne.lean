module

public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.AbsCentralAlt
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TeichmullerInertiaLabelCondition
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LabLPIsLabelActK
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FixedNeBotOfEquiv
public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.GoodLem
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoeffRingsHaveRootsOfUnity
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameInertiaRepresentativeResidue

@[expose] public section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.DepthZeroRankOneLabel
open ValuativeRel
variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {g : ℕ} [Fact g.Prime]
variable (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i)
end GlobalTheory.DepthZeroRankOneLabel
namespace GlobalTheory.DepthZeroRankOneLabel
open ValuativeRel GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {g : ℕ} [Fact g.Prime]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
end GlobalTheory.DepthZeroRankOneLabel
namespace GlobalTheory.DepthZeroRankOneLabel
open GlobalTheory.TameRes
end GlobalTheory.DepthZeroRankOneLabel
namespace GlobalTheory.DepthZeroRankOneLabel
end GlobalTheory.DepthZeroRankOneLabel
open GlobalTheory.WeilDeligne in
theorem GlobalTheory.DepthZeroRankOneLabel.wild_trivial_m_alt (D : D7) (k : Fin 2) (v : D.nd.PlG k)
    (μ : ((D.naut.plGw k v).adicCompletion D.host.E)ˣ →* ℂˣ) (hμ : GlobalTheory.SmGL.IsSmoothChar μ) (hT : GlobalTheory.SplitWeil.IsTame μ)
    (a : Weil (D.nd.plOm.2 (D.naut.plGw k v)) →* ((D.naut.plGw k v).adicCompletion D.host.E)ˣ)
    (ha : GlobalTheory.LocLanglands.IsLocalArtin (D.nd.plOm.2 (D.naut.plGw k v)) a)
    (ε : GlobalTheory.LocLanglands.EpsFamily (D.nd.plOm.1 (D.naut.plGw k v)))
    (rc : GlobalTheory.LocGL.IrrGL (k := (D.naut.plGw k v).adicCompletion D.host.E) → WD (D.nd.plOm.2 (D.naut.plGw k v)))
    (hl : _root_.UpperTheory.One.M.LawsM a ha ε rc) :
    ∀ σ : Weil (D.nd.plOm.2 (D.naut.plGw k v)),
      (σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om) ∈ Wild D.host.E (D.nd.plOm.1 (D.naut.plGw k v)) → (μ.comp a) σ = 1 := by
  have htame := GlobalTheory.SerSys.LabDepth.tame_of_isTameWD (_root_.UpperTheory.One.M.LawsM.depth hl (GlobalTheory.LocGL.IrrGL.ofChar μ hμ) (UpperTheory.One.M.good_ofChar μ hμ) (by
    refine GlobalTheory.LocLanglands.fixed_ne_bot_of_equiv
      (GlobalTheory.SmGL.IrrRep.nonempty_equiv_rep (Irr.ofDet 1 μ hμ).toIrrRep).some.symm ?_
    refine (Submodule.ne_bot_iff _).2 ⟨(show (Irr.ofDet 1 μ hμ).V from (1 : ℂ)), GlobalTheory.Parabolic.mem_fixed.2 fun u hu => ?_,
      (one_ne_zero : (1 : ℂ) ≠ 0)⟩
    have hu' : u ∈ GlobalTheory.SplitWeil.KOne ((D.naut.plGw k v).adicCompletion D.host.E) (Fin 1) := hu
    have h1 := GlobalTheory.StepData.mem_KOne.1 hu' 0 0
    rw [Matrix.sub_apply, Matrix.one_apply_eq] at h1
    have h2 : μ (Matrix.GeneralLinearGroup.det u) = 1 := hT _ (by
      have e : ((Matrix.GeneralLinearGroup.det u : (_)ˣ) : (D.naut.plGw k v).adicCompletion D.host.E) = u.val 0 0 := by
        simp [Matrix.det_fin_one]
      rw [e]; exact h1)
    change (GlobalTheory.SmGL.detRep (Fin 1) μ) u (1 : ℂ) = (1 : ℂ)
    simp [GlobalTheory.SmGL.detRep, h2]))
  rw [hl.one, WD.lpOfChar, WD.tame_mk] at htame
  intro σ hσ
  have h2 := LinearMap.congr_fun (htame σ hσ) (fun _ => 1)
  have h3 := congrFun h2 0
  simpa using h3
end
end
