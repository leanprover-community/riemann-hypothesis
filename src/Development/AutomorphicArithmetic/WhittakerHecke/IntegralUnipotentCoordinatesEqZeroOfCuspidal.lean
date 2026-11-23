module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.IsotypQuot
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.NormWfLe
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.EqAmOfBarEq
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Dynamics.Ergodic.Action.Regular
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
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.ThInf
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ConjInv

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.TA
open UpperTheory.ConvolutionTheory.R2.G (FS2 nE)
open scoped Classical


open GroundTheory.Automorphic.FourierWhittaker in
private noncomputable def latE' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (D : Dat F E) :
    vecLattice F (Fin 2) ≃ AdeleRing.principalSubgroup (𝓞 E) E where
  toFun g := ⟨D.coE.symm g.1, by
    obtain ⟨_, ξ, rfl⟩ := g
    refine ⟨algebraMap F E (ξ 0) + algebraMap F E (ξ 1) * D.θ, ?_⟩
    exact (D.mkE_rt (ξ 0) (ξ 1)).symm⟩
  invFun y := ⟨D.coE y.1, by
    obtain ⟨_, z, rfl⟩ := y
    exact mem_vecLattice.2 ⟨fun i => D.b.repr z i, funext fun i => (D.co_rt z i).symm⟩⟩
  left_inv g := Subtype.ext (D.coE.apply_symm_apply g.1)
  right_inv y := Subtype.ext (D.coE.symm_apply_apply y.1)

theorem UpperTheory.integral_unipotentCoordinates_eq_zero_of_cuspidal :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (f : GL (Fin 2) (A E) → ℂ), Pp.Lf f →
        (∀ g, ∫ b in fundamentalSet E, f (gl (nU b) * g) ∂(adeleMeasure E) = 0) →
        ∀ h, ∫ u in FS2 ℚ, f (nE D u * h) ∂(adeleMeasurePi ℚ) = 0 := by
  intro E _ _ D Φ hL h0 h
  have hl := hL.2
  let β : (Fin 2 → A ℚ) ≃ₜ+ A E := D.coE.symm
  let m := β.toHomeomorph.toMeasurableEquiv
  haveI : (adeleMeasurePi ℚ (ι := Fin 2)).IsAddHaarMeasure := inferInstanceAs (Measure.pi fun _ : Fin 2 => adeleMeasure ℚ).IsAddHaarMeasure
  haveI : ((adeleMeasurePi ℚ (ι := Fin 2)).map m).IsAddHaarMeasure := β.isAddHaarMeasure_map (adeleMeasurePi ℚ)
  have hF : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 E) E) (m '' FS2 ℚ) ((adeleMeasurePi ℚ (ι := Fin 2)).map m) :=
    (isAddFundamentalDomain_vecDomain (K := ℚ) (ι := Fin 2)).image_of_equiv m.toEquiv
      (MeasurePreserving.symm m ⟨m.measurable, rfl⟩).quasiMeasurePreserving (latE' D).symm
      fun y x => by
        change β (D.coE y.1 + x) = y.1 + β x
        rw [map_add (f := _)]
        congr 1
        exact D.coE.symm_apply_apply y.1
  have hF' : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 E) E) (m '' FS2 ℚ) (adeleMeasure E) :=
    hF.mono (Measure.absolutelyContinuous_isAddHaarMeasure _ _)
  have hper : ∀ (g : AdeleRing.principalSubgroup (𝓞 E) E) (x : A E),
      Φ (gl (nU (g +ᵥ x)) * h) = Φ (gl (nU x) * h) := by
    rintro ⟨_, k, rfl⟩ x
    obtain ⟨γ, hγ⟩ := Pp.rat_n k
    change Φ (gl (nU (rt k + x)) * h) = _
    rw [Pp.n_add, ← hγ, mul_assoc, hl]
  haveI : Countable (AdeleRing.principalSubgroup (𝓞 E) E) := (latE' D).symm.injective.countable
  have h1 := (isAddFundamentalDomain_fundamentalSet E).setIntegral_eq hF' (f := fun x => Φ (gl (nU x) * h)) hper
  have h2 : ∫ x in fundamentalSet E, Φ (gl (nU x) * h) ∂(adeleMeasure E) = 0 := h0 h
  have hc := (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure (adeleMeasure E) ((adeleMeasurePi ℚ (ι := Fin 2)).map m)).ne'
  rw [h1, Measure.isAddLeftInvariant_eq_smul (adeleMeasure E) ((adeleMeasurePi ℚ (ι := Fin 2)).map m), Measure.restrict_smul,
    integral_smul_nnreal_measure, m.measurableEmbedding.setIntegral_map, m.injective.preimage_image] at h2
  exact (smul_eq_zero.1 h2).resolve_left hc
