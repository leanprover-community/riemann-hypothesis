module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.WsLink
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.IsAlgClosureField
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.MapApi
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.CharpolyGspConjInvScaled
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.CharpolySmulUnit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.ConjPlace
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.CpCont
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.CpRedProdScaleRoots
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.PhiDet
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.PhiFlag
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.PhiUnr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.PpSingle
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.ResLeMemDec
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.ResidueEqOneOfMap
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.SpacePsiMul
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime

@[expose] public section




section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp
private theorem chi_map {n : ℕ} {A A' G : Type} [CommRing A] [CommRing A'] [Group G] (E : W.GDet n A G) (f : A →+* A') (g : G) :
    (E.map f).chi (MonoidAlgebra.single g 1) = (E.chi (MonoidAlgebra.single g 1)).map f := by
  rw [← (AlgebraTools.Det.mapApi E f).1, MonoidAlgebra.mapRingHom_single, map_one]
theorem UpperTheory.V.Ws.exists_phi_universal_ordinary_det_ring_of_link :
    _root_.UpperTheory.V.Ws.UnramifiedInputs → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → T.Deep → ∀ (c' : Coef l) (h : c.O ≤ c'.O) (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (n : ℕ), (∃ B : W.UniversalOrdinaryDeterminantRing K.r, True) ∧ ∀ B : W.UniversalOrdinaryDeterminantRing K.r, ∃ φ : B.B →ₐ[c'.O] X.B, K.IsPhi X n B φ := by
  intro U Ω _ _ _ l _ c D T _ _ c' h K X n
  obtain ⟨hs, hq, hk⟩ := phiKer K.V
  obtain ⟨E, hE, hcp, hc⟩ := phiDet (maximalIdeal X.B) (algebraMap X.B X.A) X.inj K.V.pr hs hq (K.rho X n) (K.cpT X n)
    (fun g => (phiCpMap K X n g).2.2.2) (phiCpCont K X n)
    fun U hU hle => hk U hU fun A v hA hv => (phiUnr K X n A v hA hv).trans hle
  obtain ⟨ψ, hψ⟩ := phiPsiEx K X n
  obtain ⟨p, hD, hp⟩ := phiPair K.r X.inj (by norm_num) K.V.pr hs (K.rho X n) E ψ hE hc
    (fun g => (congrArg _ (hcp g)).trans (phiCpRed K X n g)) (phiIsPsi K X n ψ hψ) (phiPol K X n)
    (fun v => ⟨_, rfl, phiFlag K X n ψ hψ v⟩) (phiIne K X n)
  obtain ⟨B₀⟩ := U.b0 l T.L Ω K.s K.V c' 4 K.r X.B ⟨p⟩
  refine ⟨⟨B₀, trivial⟩, fun B => ?_⟩
  obtain ⟨φ, ⟨h1, h2⟩, -⟩ := B.univ X.B p
  refine ⟨φ, fun g => ?_, fun v i g => ?_⟩
  · have e := chi_map B.u.D (φ : B.B →+* X.B) (K.V.pr g)
    rw [h1, hD] at e
    exact e.symm.trans (hcp g)
  · have e := congrArg Units.val (DFunLike.congr_fun (h2 v i) g)
    rw [hp] at e
    exact e.trans (hψ v i g)
end
