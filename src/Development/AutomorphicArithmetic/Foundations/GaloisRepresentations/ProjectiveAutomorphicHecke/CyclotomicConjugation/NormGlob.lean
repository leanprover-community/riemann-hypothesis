module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CyclotomicConjugation.QuadConjAlt
public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.CompletionsOverBasisRepr
public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.InfiniteAdeleRingMapInfiniteAdeleRingMap
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

@[expose] public section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.L2.Host GlobalTheory.HeckeGal
open GlobalTheory.SplitPts (conjE)
open GroundTheory.Global.AdeleBaseChange (finiteAdeleMap)
open UpperTheory.Gal.CertificateRingHomMap UpperTheory.Gal.CertificateRingHomMap.ZetaNonvanishing₂

private noncomputable abbrev sn (K : Type) [Field K] [NumberField K] : GroundTheory.Global.IdeleGroup K →* (Af K)ˣ :=
  Units.map (MonoidHom.snd (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K))

private noncomputable abbrev fi (K : Type) [Field K] [NumberField K] : (Af K)ˣ →* GroundTheory.Global.IdeleGroup K :=
  Units.map (MonoidHom.inr (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K))

private theorem sn_norm (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (x : GroundTheory.Global.IdeleGroup L) :
    sn K (GroundTheory.Global.ideleNorm K L x) = fN K L (sn L x) := by
  apply Units.ext
  apply RestrictedProduct.ext
  intro v
  exact (GroundTheory.Global.ideleNorm_snd x v).trans (GroundTheory.Global.ideleNorm_snd (fi L (sn L x)) v).symm

private theorem continuous_sn (K : Type) [Field K] [NumberField K] : Continuous (sn K) :=
  Continuous.units_map _ continuous_snd

private theorem continuous_fi (K : Type) [Field K] [NumberField K] : Continuous (fi K) :=
  Continuous.units_map _ (continuous_const.prodMk continuous_id)

theorem UpperTheory.Gal.CertificateRingHomMap.ZetaNonvanishing₂.normGlob :
    UpperTheory.Gal.CertificateRingHomMap.ZetaNonvanishing₂.NormGlob := by
  intro K L _ _ _ _ _
  refine ⟨(continuous_sn K).comp (GroundTheory.Global.continuous_ideleNorm.comp (continuous_fi L)), fun k => ?_, ?_⟩
  · have h : diagF L k = sn L (GroundTheory.Global.IdeleGroup.diagonal L k) := by
      apply Units.ext
      rfl
    rw [h, ← sn_norm, GroundTheory.Global.ideleNorm_diagonal]
    rfl
  · intro M _ _ _ _ _ y
    have h := sn_norm K L (GroundTheory.Global.ideleNorm L M (fi M y))
    rw [GroundTheory.Global.ideleNorm_ideleNorm] at h
    exact h.symm
