module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGL
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
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.ContinuousTorusCharacter

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.W (Plc)

private theorem eq_finGL {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {w : Plc E} {g : UA E n}
    (hg : g ∈ locU n w) (k : GL (Fin n) (Af E))
    (hk : ∀ u, cLoc u g = Matrix.GeneralLinearGroup.map (pLoc E u) k) : (g : GA E n) = finGL E n k := by
  have hinf : cInf g = 1 := MonoidHom.mem_ker.1 (Subgroup.mem_inf.1 hg).1
  refine ga_ext (hinf.trans (pInf_finGL k).symm) ?_
  rw [pFin_finGL]
  refine Units.ext (GlobalTheory.SplitPts.matAf_ext fun u => ?_)
  exact congrArg Units.val (hk u)

private theorem cLoc_off {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {w u : Plc E} {g : UA E n}
    (hg : g ∈ locU n w) (hu : u.under (𝓞 (maximalRealSubfield E)) ≠ w.under (𝓞 (maximalRealSubfield E))) :
    cLoc u g = 1 :=
  MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hg).2 u) hu)

theorem UpperTheory.detCharacter_eq_localDet_split_nonsplit :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (ν : HChar E), GlobalTheory.ThetaPull.thetaChar ν = ν → ∀ (w : Plc E), ∀ g ∈ locU n w, (IsSplitAt w → chiDet n ν (g : UA E n) = CuspSub.locDet n (ν * ν) w (cLoc w g)) ∧ (¬ IsSplitAt w → chiDet n ν (g : UA E n) = CuspSub.locDet n ν w (cLoc w g)) := by
  intro E _ _ _ n ν hν w g hg
  refine ⟨fun hw => ?_, fun hw => ?_⟩
  · obtain ⟨hne, hun, hover⟩ := GlobalTheory.SplitPts.over_split hw
    set w' := conjSrc (GlobalTheory.SplitPts.conjE E) w with hw'
    have e : (g : GA E n) = finGL E n (locGL E n w (cLoc w g) * locGL E n w' (cLoc w' g)) := by
      refine eq_finGL hg _ fun u => ?_
      rw [map_mul]
      by_cases h1 : u = w
      · rw [h1, pLoc_locGL, pLoc_locGL_of_ne (Ne.symm hne), mul_one]
      · by_cases h2 : u = w'
        · rw [h2, pLoc_locGL, pLoc_locGL_of_ne hne, one_mul]
        · rw [pLoc_locGL_of_ne h1, pLoc_locGL_of_ne h2, one_mul]
          exact cLoc_off hg fun h => (hover u h).elim h1 h2
    have hd : Units.map (conjLoc (GlobalTheory.SplitPts.conjE E) w).toMonoidHom (Matrix.GeneralLinearGroup.det (cLoc w' g)) =
        (Matrix.GeneralLinearGroup.det (cLoc w g))⁻¹ := by
      refine eq_inv_of_mul_eq_one_left (Units.ext ?_)
      have h := congrArg Matrix.det (GlobalTheory.SplitPts.comp_eq g w)
      rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
      refine Eq.trans ?_ h
      exact congrArg (· * _) (RingHom.map_det (conjLoc (GlobalTheory.SplitPts.conjE E) w) _)
    have h2 : CuspSub.locDet n ν w' (cLoc w' g) = CuspSub.locDet n ν w (cLoc w g) := by
      change ν.1 (localIdele E w' (Matrix.GeneralLinearGroup.det (cLoc w' g))) =
        ν.1 (localIdele E w (Matrix.GeneralLinearGroup.det (cLoc w g)))
      have h3 := GlobalTheory.ThetaPull.thetaChar_apply ν (localIdele E w' (Matrix.GeneralLinearGroup.det (cLoc w' g)))
      rw [hν, GlobalTheory.ThetaPull.conjAd_localIdele, hd, map_inv, map_inv, inv_inv] at h3
      exact h3
    rw [e, map_mul, map_mul, CuspSub.chiDet_locGL, CuspSub.chiDet_locGL, h2]
    rfl
  · have e : (g : GA E n) = finGL E n (locGL E n w (cLoc w g)) := by
      refine eq_finGL hg _ fun u => ?_
      by_cases h1 : u = w
      · rw [h1, pLoc_locGL]
      · rw [pLoc_locGL_of_ne h1]
        exact cLoc_off hg fun h => hw ⟨u, h1, h⟩
    rw [e, CuspSub.chiDet_locGL]
