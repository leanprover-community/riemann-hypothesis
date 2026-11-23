module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineAndJumps
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineTwistCrystallineCharacterJumpsShift
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrysInclusion
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitsOfConjugatesMem
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistLocC
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

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.DualTwistCrys

theorem crys_chi (D : D7) (i : D.nd.Loc) (hChi : GlobalTheory.PtCore.ChiOneE D i) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) :
    IsCrys (Br.PD D.loc D.nbr i w hw) (Formalism.WeaklyAdmissibleFiltrations.charRep (TruncatedSeriesCountingIdentities.chi1C C)⁻¹) := hChi w hw C.LL C.le

theorem card_emb (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) :
    Nat.card (↥(D.nbr i w hw).Kw.1 →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1) =
      Module.finrank ℚ_[D.nd.l i] ↥(D.nbr i w hw).Kw.1 := by
  have := D.nd.lPrime i
  have := C.LL.2
  have := (D.nbr i w hw).Kw.2
  have h2 := (GlobalTheory.splits_of_conjugates_mem _ (D.nbr i w hw).Kw C.LL (fun τ y => C.le
    ((D.nbr i w hw).LL_split τ y)) inferInstance).2
  rw [Nat.card_eq_fintype_card, h2]

theorem twist_crys (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw)
    (x : D.nd.X i)
    (hchi : IsCrys (Br.PD D.loc D.nbr i w hw) (Formalism.WeaklyAdmissibleFiltrations.charRep (TruncatedSeriesCountingIdentities.chi1C C)⁻¹))
    (hcC : IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r x)))) :
    IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (twistM (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r x)) (TruncatedSeriesCountingIdentities.chi1C C)⁻¹)) := by
  have := D.nd.lPrime i
  have := C.LL.2
  refine (GlobalTheory.TwistRepCrys.isCrys_and_multV_twist (D.nd.l i) (D.loc _) (D.locA _) (D.locT _)
    (D.nbr i w hw).Kw C.LL _ (matRep (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r x))) _
    (matRep (twistM (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r x)) (TruncatedSeriesCountingIdentities.chi1C C)⁻¹)) (TruncatedSeriesCountingIdentities.chi1C C)⁻¹
    ⟨LinearEquiv.refl _ _, fun g v => ?_⟩ hchi hcC).1
  rw [LinearEquiv.refl_apply, LinearEquiv.refl_apply, GlobalTheory.TateDualCrys.matRep_apply,
    GlobalTheory.TateDualCrys.matRep_apply]
  exact Matrix.smul_mulVec _ _ _

theorem crys_coef (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw)
    (x : D.nd.X i)
    (hcw : IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (Br.loc D.nbr i w hw (rO D.nd i r x)))) :
    IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r x))) := by
  have := D.nd.lPrime i
  exact GlobalTheory.CrysCoef.isCrys_inclusion (D.nd.l i) (D.loc _) (D.nbr i w hw).Kw (D.nbr i w hw).LL C.LL C.le _ _ hcw

theorem dual_crys (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw)
    (x : D.nd.X i)
    (htw : IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r x)))) :
    IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rDuO D.nd i r x))) := by
  have := D.nd.lPrime i
  exact (GlobalTheory.TateDualCrys.tateDual (D.locT _) (D.nbr i w hw).Kw C.LL (card_emb D i w hw C) _ _
    (GlobalTheory.TateDualCrys.loc_rDuO D i w hw C.LL C.le r x) htw).1

theorem tw_crys (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw)
    (x : D.nd.X i)
    (hchi : IsCrys (Br.PD D.loc D.nbr i w hw) (Formalism.WeaklyAdmissibleFiltrations.charRep (TruncatedSeriesCountingIdentities.chi1C C)⁻¹))
    (hcC : IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r x)))) :
    IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r x))) := by
  rw [← GlobalTheory.AmbientDual.twist_locC]
  exact twist_crys D i r w hw C x hchi hcC

end GlobalTheory.DualTwistCrys
