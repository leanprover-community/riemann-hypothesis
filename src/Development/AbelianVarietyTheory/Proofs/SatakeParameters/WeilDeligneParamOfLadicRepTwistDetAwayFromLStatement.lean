module

public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WeilDeligneParamMonodromyEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParamOfLadicRepTwistDetAwayFromL
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsReadingLaws
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import ReciprocityTheory.Automorphisms.PlaceA

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.WeilDeligne GlobalTheory.WeilDeligne.TwistAway in

theorem _root_.GlobalTheory.T.weilDeligneParamOfLadicRep_twist_det_awayFrom_l : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver (F := E) A w) (l : ℕ) [Fact l.Prime] (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (ι : Qbar l ≃+* ℂ) (a : ℕ) (ρ : G E Ω →* GL (Fin a) (Qbar l)) (χ : G E Ω →* GL (Fin 1) (Qbar l)), Continuous (fun g => ((ρ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))) → Continuous (fun g => ((χ g : GL (Fin 1) (Qbar l)) : Matrix (Fin 1) (Fin 1) (Qbar l))) → GlobalTheory.WeilDeligne.wdOf (h := h) hl ι (Formalism.MainNotions.SumRepresentations.At.twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)) = (GlobalTheory.WeilDeligne.wdOf (h := h) hl ι ρ).lpChar (GlobalTheory.WeilDeligne.wdOf (h := h) hl ι χ) := by
  intro E Ω _ _ _ _ _ A w h l _ hl ι a ρ χ hρ hχ
  have ht := isTameChar_tameL h hl
  obtain ⟨N, hN⟩ := exists_isMonodromy h hl ht hρ
  obtain ⟨Nχ, hNχ⟩ := exists_isMonodromy h hl ht hχ
  have hχ0 := isMonodromy_zero_of_line hNχ
  have hN' := isMonodromy_twGL hN hχ0
  obtain ⟨a₀, ha, ea⟩ := hN.wdOf_spec hl ht (deg_frob (h := h)) ι
  obtain ⟨b₀, hb, eb⟩ := hχ0.wdOf_spec hl ht (deg_frob (h := h)) ι
  obtain ⟨d, hd, ed⟩ := hN'.wdOf_spec hl ht (deg_frob (h := h)) ι
  rw [ea, eb, ed, WD.lpChar_mk]
  refine WD.sound (WDRep.Iso.symm ?_)
  rw [map_zero] at hb
  refine (isFrobSS_tensor_line ha hb).iso hd (lineEquiv _) (fun g v => ?_) (fun v => ?_)
  · induction v using TensorProduct.inductionOn with
    | tmul x y =>
      simp only [TensorProduct.map_tmul, lineEquiv_tmul, IsMonodromy.rep_apply, wdMat_twGL,
        wdMat_zero, toEndC_smul, map_smul, LinearMap.smul_apply]
      rw [smul_smul]
      congr 1
      simp [toEndC_apply, Matrix.mulVec, dotProduct, mul_comm]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  · induction v using TensorProduct.inductionOn with
    | tmul x y => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
