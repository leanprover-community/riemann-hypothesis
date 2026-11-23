module

public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.FinalPtfsData
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GelfandSpectralNormalisation.NormalisedInvariants.PoitouTateExactSecond
public import GroundTheory.ProfiniteCohomology.PoitouTate.PtCompactDualMapEqZeroOfPtCompactToGlobalEqZero
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.FinalInv
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.RestrictionSquareDegreeOne
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.TransferCupDegreeZeroTwo
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

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain CategoryTheory MonoidalCategory TensorProduct GroundTheory.ProfCoh
  GroundTheory.Global ReciprocityTheory.Gal Formalism.ConjugateSelfDual GlobalTheory.Published GlobalTheory.Published.PoitouTate

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2



theorem locTr1_C (Kf : FiniteSubfield) [NumberField Kf.1]
    [IsAlgClosure Kf.1 (AlgebraicClosure ℚ)] (S : Finset (HeightOneSpectrum (𝓞 Kf.1))) {l r : ℕ}
    [Fact l.Prime] (hr : 0 < r) (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ (l ^ r))
    (inv : InvFam Kf.1 (AlgebraicClosure ℚ) l r) (hinv : PositivityTheory.PoitouTateConclusion.InvNormalised ζ inv)
    (hS : ContainsAbove S l) (Av : S → ValuationSubring (AlgebraicClosure ℚ))
    (hAv : ∀ v, IsPlaceOver (Av v) v.1)
    (μ : GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))) →* (ZMod (l ^ r))ˣ)
    (hμ : μ.comp (toGS (AlgebraicClosure ℚ) _) = cycMod Kf.1 (AlgebraicClosure ℚ) l r)
    {M : Type} [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M]
    [DiscreteTopology M]
    (ρ : Representation (ZMod (l ^ r)) (GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))) M)
    (hρ : ContAction ρ) (d : FoundData Kf S l r ζ Av μ M ρ) [IsDiscreteRep d.A] [Finite d.A] (v : S)
    [IsDiscreteRep (Rep.res (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩).toMonoidHom
      (dualRep (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A))]
    (E : H1 (ρ.comp (locFam S Av v)) ≃+ cohomology (Rep.res (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩).toMonoidHom d.A) 1)
    (hE : ∀ (z : ↥(Z1 (ρ.comp (locFam S Av v)))) (x : cocycles (Rep.res (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩).toMonoidHom d.A) 1),
      (∀ s, cochainOf _ (cocycleι _ 1 x) s = d.eM (z.1 (d.ev v (s 0)))) → E (Submodule.Quotient.mk z) = cohomologyπ _ 1 x)
    (E' : H1 ((twDual μ ρ).comp (locFam S Av v)) ≃+ cohomology (Rep.res (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩).toMonoidHom (dualRep (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A)) 1)
    (hE' : ∀ (z : ↥(Z1 ((twDual μ ρ).comp (locFam S Av v)))) (x : cocycles (Rep.res (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩).toMonoidHom (dualRep (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A)) 1),
      (∀ s, cochainOf _ (cocycleι _ 1 x) s = d.eD (z.1 (d.ev v (s 0)))) → E' (Submodule.Quotient.mk z) = cohomologyπ _ 1 x)
    (a : H1 (ρ.comp (locFam S Av v))) (b : H1 ((twDual μ ρ).comp (locFam S Av v))) :
    zmodToQZ (l ^ r) (invAt S Av μ hμ inv v (cupH1H1TwistedDual μ ρ (locFam S Av v) (hρ.comp' (continuous_locFam S Av v)) b a)) =
      gsLocalInvRootsQZ (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs (l ^ r) ⟨v.1, Finset.mem_coe.2 v.2⟩ (cupPairing (ptLocalEval (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs) (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A ⟨v.1, Finset.mem_coe.2 v.2⟩) (rfl : 1 + 1 = 2) (E a) (E' b)) := by
  classical
  let places : Set (HeightOneSpectrum (𝓞 Kf.1)) := S
  let place : places := ⟨v.1, Finset.mem_coe.2 v.2⟩
  let family := gsFinFamily places d.ιs
  let localHom := (family place).toMonoidHom
  let roots := gsRoots places (l ^ r)
  let localM := Rep.res localHom d.A
  let localDual := Rep.res localHom (dualRep roots d.A)
  let localRoots := Rep.res localHom roots
  let pairing := ptLocalEval family roots d.A place
  let φ := locFam S Av v
  let ev := d.ev v
  let ρM := ρ.comp φ
  let ρD := (twDual μ ρ).comp φ
  let ρchar := (charRep μ).comp φ
  let jp := (zmodToQZ (l ^ r)).comp (invAt S Av μ hμ inv v).toAddMonoidHom
  let J := gsLocalInvRootsQZ places d.ιs (l ^ r) place
  let rel (c : ZMod (l ^ r)) (y : localRoots.V) : Prop :=
    let root : rootsOfUnity (l ^ r) (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) places) :=
      Additive.toMul y
    root.val.val.val = ζ ^ c.val
  have hc1 : Continuous ev.toMonoidHom := (d.hev_cont v).1
  have heM := hloc2 ρ φ ev (fun g => d.e g) d.A d.eM d.hM localHom (d.hev v)
  have heD := hloc2 (twDual μ ρ) φ ev (fun g => d.e g)
    (dualRep roots d.A) d.eD d.hD localHom (d.hev v)
  have hbμ (x : M) (y : TDual (ZMod (l ^ r)) M) :
      rel (evalPair x y) (pairing.hom (d.eM x ⊗ₜ[ULift.{0} ℤ] d.eD y)) :=
    d.hDζ y x
  have hJ (W : Z2 ρchar) (x : cocycles localRoots 2)
      (h : ∀ s, rel (W.1 (ev (s 0), ev (s 1))) (cochainOf localRoots (cocycleι localRoots 2 x) s)) :
      jp (Submodule.Quotient.mk W) = - J (cohomologyπ localRoots 2 x) :=
    @invCmp Kf ‹_› ‹_› places inferInstance l r ‹_› hr
      (fun w hw => Finset.mem_coe.2 (hS w hw)) ζ hζ inv hinv d.ιs place (Av v) (hAv v)
      ev (d.hιs v) hc1
      (cocycles2Map ρchar (muLoc Kf.1 l r (Av v)) LinearMap.id continuous_id
        (locFam_apply_eq S Av μ hμ v) W) x h
  have hTransfer := transfer_cup_one_one_general
    (R := ZMod (l ^ r)) (M := TDual (ZMod (l ^ r)) M) (M' := M) (P := ZMod (l ^ r)) (Q := QZ)
    ev hc1 ρD ρM ρchar evalPair.flip continuous_of_discreteTopology
    (fun g y x => evalPair_equiv μ ρ (φ g) x y) (hρ.comp' (continuous_locFam S Av v))
    localDual localM localRoots d.eD d.eM heD heM pairing rel hbμ E' hE' E hE jp J hJ a b
  -- Kernel conversion avoids a costly elaborator comparison of the cohomology types.
  run_tac Lean.Elab.Tactic.withMainContext do
    let proof ← Lean.Elab.Tactic.getFVarId (Lean.mkIdent `hTransfer)
    let goal ← Lean.Elab.Tactic.getMainGoal
    let actual ← Lean.instantiateMVars (← proof.getType)
    let expected ← Lean.instantiateMVars (← goal.getType)
    let context ← Lean.instantiateLCtxMVars (← Lean.getLCtx)
    match Lean.Kernel.isDefEq (← Lean.getEnv) context actual expected with
    | .ok true => goal.assign (.fvar proof)
    | .ok false => throwError "kernel conversion failed for the transfer result"
    | .error e => throwError "{e.toMessageData (← Lean.getOptions)}"

end PositivityTheory.Lit1.PTN
