module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CmBaseThetaTensorPowerTranslatesIntegralStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LatticeJetsAreBoundedMomentsProdAndSumStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LatticeJetsAreBoundedMomentsPullbackStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TranslateNormalizedVectorIntegralCombTensorPowerStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitaryPairPullbackLatticesTranslatesStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeakApproximationUnitaryLatticesSplitPrimeStatement
import Formalism.LocalToGlobal.GlobalTheory.GL3.PStdOK
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntStd
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN

namespace GlobalTheory.MomN

theorem contDiff_U {D : D7} {N N' : ℕ} (T : Tor D) (t : VC D N N') {G : VC D N N' → ℂ} (hG : ContDiff ℂ ⊤ G) :
    ContDiff ℂ ⊤ (U D T t G) := by
  have hH : ContDiff ℂ ⊤ fun z : VC D N N' => Hf D T z t := by
    unfold Hf
    refine ContDiff.div_const ?_ _
    refine ContDiff.sum fun τ _ => ContDiff.sum fun i _ => ContDiff.sum fun j _ => ?_
    refine ContDiff.mul ?_ contDiff_const
    fun_prop
  unfold U
  refine ContDiff.mul (hG.comp (contDiff_id.add contDiff_const)) ?_
  exact ContDiff.cexp ((contDiff_const.mul hH).sub contDiff_const)

theorem transPrime_int : (∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : IdE D → ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → B.EqP χ) → ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (q : ℕ) [Fact q.Prime], q ≠ 2 → jacobiSym (-(D.host.d : ℤ)) q = 1 → Nat.Coprime (Ideal.absNorm cc) q → ∀ (ι : ℂ ≃+* ℂ_[q]) (δ₀ : ℂ) (θ : ℂ → ℂ) (Ω : ℂ_[q]), Per D.host.d ι δ₀ θ Ω → ∀ χ : IdE D → ℂ, IsChi D χ → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' → ∀ t : VC D N N', TorsPrime D q (La D B.tor L L') t → LatInt ι (Ω / ι δ₀) (La D B.tor L L') (U D B.tor t (B.eNat χ N N' L L')) := by
  intro hEq D cc δ B hcc hδ q _ hq2 hsplit hcop ι δ₀ θ Ω hPer χ hχ N N' L L' hA t ht
  letI := D.host.cmStar
  obtain ⟨γ, γ', M, M', hAM, hE, hE', rfl, rfl⟩ := GlobalTheory.T.weakApproximation_unitaryLattices_splitPrime D q hq2 hsplit N N' L L' hA
  obtain ⟨hN, hN', hSM, hSM'⟩ := id hAM
  have hcov : pull D B.tor (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E)
      (B.eNat χ N N' M M') =
      B.eNat χ N N' (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) M)
        (SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) M') :=
    (hEq D cc δ B χ hcc hδ hχ).1 N N' ⟨M, hSM⟩ ⟨M', hSM'⟩ hN hN' γ γ'
  obtain ⟨g, hg, hU⟩ := GlobalTheory.T.unitaryPairPullback_lattices_translates D cc δ N N' γ γ' M M'
  have ht' : TorsPrime D q (La D B.tor M M') (g t) := by
    obtain ⟨n, hn, hc, hm⟩ := ht
    refine ⟨n, hn, hc, ?_⟩
    have := hg _ hm
    rwa [map_nsmul] at this
  let lam : Qbar →+* ℂ_[q] := (ι : ℂ →+* ℂ_[q]).comp (algebraMap Qbar ℂ)
  obtain ⟨m, c, s, hc, hs, heq⟩ :=
    GlobalTheory.T.translate_normalized_vector_integral_comb_tensor_power D cc δ B hcc hδ χ hχ q lam N N' M M' hAM hE hE' (g t) ht'
  have hzero : ∀ k, LatInt ι (Ω / ι δ₀) (La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N'))
      (U D B.tor (s k) (B.thZero N N')) := fun k =>
    GlobalTheory.T.cm_base_theta_tensor_power_translates_integral D cc δ B hcc hδ q hq2 hsplit hcop ι δ₀ θ Ω hPer N N' (s k) (hs k)
  have hd : ContDiff ℂ ⊤ (B.thZero N N') :=
    AnalyticOnNhd.contDiff (B.thZeroMem (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.stdOK B hcc hδ) N N').1
  have hsm : ∀ k, ContDiff ℂ ⊤ (U D B.tor (s k) (B.thZero N N')) := fun k => contDiff_U _ _ hd
  have hcn : ∀ k, ‖ι (c k)‖ ≤ 1 := by
    intro k
    obtain ⟨h1, h2⟩ := hc k
    have e : lamC lam (c k) = ι (c k) := by
      unfold lamC
      rw [dite_eq_left h1]
      rfl
    rw [← e]
    exact h2
  have hsum := (GlobalTheory.T.latticeJetsAreBoundedMoments_prod_and_sum q ι (VC D N N') (Ω / ι δ₀) (La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N'))).2
    (Fin m) Finset.univ c (fun k => U D B.tor (s k) (B.thZero N N')) (fun k _ => hsm k) (fun k _ => hcn k)
    (fun k _ => hzero k)
  have hGs : ContDiff ℂ ⊤ fun z => ∑ k, c k * U D B.tor (s k) (B.thZero N N') z :=
    ContDiff.sum fun k _ => contDiff_const.mul (hsm k)
  obtain ⟨a, ha, hsM, hMs⟩ := hE
  obtain ⟨b, hb, hsM', hMs'⟩ := hE'
  have hpull := GlobalTheory.T.latticeJetsAreBoundedMoments_pullback q ι (VC D N N') (VC D N N') (Ω / ι δ₀)
    (La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N'))
    (La D B.tor (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) M)
      (SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) M')) g _ hGs
    (fun x hx => ⟨a * b, Nat.Coprime.mul_left ha hb,
      Formalism.L2.KerInert.ISd.La_smul cc δ a b hsM hMs' (hg x hx)⟩) hsum
  rw [← hcov, show U D B.tor t (pull D B.tor (γ : Matrix (Fin N) (Fin N) D.host.E)
      (γ' : Matrix (Fin N') (Fin N') D.host.E) (B.eNat χ N N' M M')) =
      fun z => U D B.tor (g t) (B.eNat χ N N' M M') (g z) from hU t _, heq]
  exact hpull

end GlobalTheory.MomN
