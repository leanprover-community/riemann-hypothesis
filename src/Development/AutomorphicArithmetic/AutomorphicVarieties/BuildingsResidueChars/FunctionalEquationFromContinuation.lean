module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Formalism.DoubleCosetMeasures.Statement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.PairGOps
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.AdjointEta.EtaOK
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.WinUpDown
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import GroundTheory.AutomorphicForms.GL2.GodementSectionFactor
public import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.CyclicCharacterEigen.ToIdeleSq

@[expose] public section

open NumberField IsDedekindDomain Polynomial Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.LocGL GlobalTheory.SplitWeil GlobalTheory.SmGL
open UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter GlobalTheory.HenQ UpperTheory.V.Z.Inf UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.Ad
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.LocalField
open GroundTheory.Automorphic.GodementSection (localChar)
open Ad3P.DihedralUnramifiedPlaces (toH)
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

private lemma ne_of_pos {s : ℂ} (hs : 0 < s.re) : s ≠ 0 := by
  rintro rfl; simp at hs

private lemma glue (F G : ℂ → ℂ) (hF : ∀ s : ℂ, 1 / 4 < s.re → DifferentiableAt ℂ F s)
    (hG : ∀ s : ℂ, s.re < 3 / 4 → DifferentiableAt ℂ G s)
    (h : ∀ s : ℂ, 1 / 4 < s.re → s.re < 3 / 4 → F s = G s) :
    ∃ Z : ℂ → ℂ, Differentiable ℂ Z ∧ (∀ s : ℂ, 1 / 4 < s.re → Z s = F s) ∧ ∀ s : ℂ, s.re < 3 / 4 → Z s = G s := by
  have a : ∀ s : ℂ, 1 / 4 < s.re → (if 1 / 4 < s.re then F s else G s) = F s := fun s hs => if_pos hs
  have b : ∀ s : ℂ, s.re < 3 / 4 → (if 1 / 4 < s.re then F s else G s) = G s := fun s hs => by
    split_ifs with h'
    · exact h s h' hs
    · rfl
  refine ⟨fun s => if 1 / 4 < s.re then F s else G s, fun s => ?_, a, b⟩
  by_cases hs : 1 / 4 < s.re
  · refine (hF s hs).congr_of_eventuallyEq ?_
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz using a z hz
  · have hs' : s.re < 3 / 4 := by linarith [not_lt.mp hs]
    refine (hG s hs').congr_of_eventuallyEq ?_
    filter_upwards [(isOpen_lt Complex.continuous_re continuous_const).mem_nhds hs'] with z hz using b z hz
