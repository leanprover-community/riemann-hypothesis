module

public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsSha
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SelmerGroupDualExact
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsBidual
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsDualPf
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsGsEquiv
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsLocal
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsRep
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsShaDict
import GroundTheory.ProfiniteCohomology.PoincareDuality.TensorHomZmodDualIsoZmodMulPairing
import GroundTheory.ProfiniteCohomology.PoitouTate.ZmodToQZCompactCohomologyResMapOfLocalInv
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
  PositivityTheory.PoitouTateConclusion GroundTheory.ProfCoh GroundTheory.Global CategoryTheory

namespace PositivityTheory.Lit1.PTN

abbrev toFS (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K] : FiniteSubfield :=
  ⟨K, inferInstance⟩

section
attribute [local instance 2000] Rep.hV2
theorem finite_dualRep' {G : Type} [Group G] (D A : Rep.{0} (ULift.{0} ℤ) G) [Finite D] [Finite A] :
    Finite (dualRep D A) := inferInstance
end


theorem shaDictFS : ShaDictFS := by
  intro K _ _ l _ r hl hr ζ hζ inv hinv S hS Av hAv μ hμ M _ _ _ _ _ ρ hρ
  have hN : NeZero (l ^ r) := ⟨pow_ne_zero r (Fact.out : l.Prime).ne_zero⟩
  let Kf := toFS K
  let Sf : Set (HeightOneSpectrum (𝓞 K)) := S
  refine (gsEquiv_toGS' K Sf).elim fun e he => ?_
  refine (localCmp' K S Av hAv e he).elim fun ιs hLocalEquiv => ?_
  refine hLocalEquiv.elim fun ev hLocal => ?_
  refine (repCmp e ρ hρ).elim fun A hDiscrete => ?_
  refine hDiscrete.elim fun hAd hRepEquiv => ?_
  refine hRepEquiv.elim fun eM hM => ?_
  have hc' : ContAction (twDual μ ρ) :=
    GlobalTheory.CompanionTheory.GalDual.contAction_twDual K (AlgebraicClosure ℚ) l r M S Av μ ρ hρ hμ
  refine (dualCmp' Kf S hr ζ hζ hS e he μ hμ ρ A eM hM).elim fun eD hdual => ?_
  have hSN : ∀ v : HeightOneSpectrum (𝓞 K), ((l ^ r : ℕ) : 𝓞 K) ∈ v.asIdeal →
      v ∈ Sf := by
    intro v hv
    rw [Nat.cast_pow] at hv
    exact Finset.mem_coe.2 (hS v (v.isPrime.mem_of_pow_mem r hv))
  have hK : Odd (l ^ r) ∨ IsTotallyComplex K :=
    hl.imp (fun h => ((Fact.out : l.Prime).odd_of_ne_two h).pow) id
  let D := gsRoots (K := Kf) Sf (l ^ r)
  have hDZ : Nonempty (D ≃+ ZMod (l ^ r)) :=
    nonempty_addEquiv_gsRoots_of_mem (K := Kf) (S := Sf) hSN
  have hDF : Finite D := finite_of_nonempty_addEquiv (D := D) hDZ
  have hFA : Finite A := Finite.of_equiv M eM.toEquiv
  have htor : ∀ m : A, (l ^ r) • m = 0 := fun m => by
    obtain ⟨x, rfl⟩ := eM.surjective m
    rw [← map_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod (l ^ r)), ZMod.natCast_self, zero_smul,
      map_zero]
  let dualA := dualRep D A
  let bidualA := dualRep D dualA
  have htorDual : ∀ f : dualA, (l ^ r) • f = 0 :=
    nsmul_dualRep_eq_zero (D := D) (M := A) (nsmul_gsRoots (K := Kf) Sf (l ^ r))
  have hDd : IsDiscreteRep D := isDiscreteRep_gsRoots (K := Kf) Sf (l ^ r)
  have hDualDiscrete : IsDiscreteRep dualA := @isDiscreteRep_dualRep _ _ _ _ _ _ D A hDd hAd hFA
  have hDualFinite : Finite dualA := @finite_dualRep' _ _ D A hDF hFA
  have hBidualDiscrete : IsDiscreteRep bidualA :=
    @isDiscreteRep_dualRep _ _ _ _ _ _ D dualA hDd hDualDiscrete hDualFinite
  refine (bidualCmp D A (l ^ r) hDZ htor).elim fun eB hB => ?_
  let eMB : M ≃+ bidualA.V := eM.trans eB
  have hMB : ∀ g m, eMB (ρ g m) = bidualA.ρ (e g) (eMB m) := fun g m =>
    (congrArg (fun a : A.V => eB a) (hM g m)).trans (hB (e g) (eM m))
  let shaIso := @shaIso_of_rep K _ S Av e ιs ev hLocal.1 hLocal.2
  have hDualSha := @shaIso _ _ _ _ _ _ _ (twDual μ ρ) hc' dualA hDualDiscrete eD hdual.1
  have hBidualSha := @shaIso _ _ _ _ _ _ _ ρ hρ bidualA hBidualDiscrete eMB hMB
  have hSha := @shaIso _ _ _ _ _ _ _ ρ hρ A hAd eM hM
  -- The comparison types agree at reducible transparency, avoiding unfolding cohomology.
  with_reducible
    refine ⟨⟨Kf, Sf, inferInstance, ιs, l ^ r, hN, hSN, hK, dualA, hDualDiscrete, hDualFinite, htorDual,
      hDualSha.1, hBidualSha.2⟩,
      ⟨Kf, Sf, inferInstance, ιs, l ^ r, hN, hSN, hK, A, hAd, hFA, htor,
      hSha.1, hDualSha.2⟩⟩

theorem shaCmpFS' : ShaCmpFS := shaCmpFS_of_dict shaDictFS

end PositivityTheory.Lit1.PTN
