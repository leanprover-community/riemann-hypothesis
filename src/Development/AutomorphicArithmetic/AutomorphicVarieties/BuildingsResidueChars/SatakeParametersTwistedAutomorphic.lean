module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.PolFacts
import Formalism.DoubleCosetMeasures.Statement
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
import Mathlib.Tactic.NormNum.Prime
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.MatchIndOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.AdjointEta.EtaOK
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

private theorem cnt_zero {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (s : Multiset (IrrGL (k := k))) (χ : kˣ →* ℂˣ) (h : ∀ ζ ∈ chars s, ¬ IsUnram (ζ * χ)) : cnt s χ = 0 := by
  unfold cnt
  rw [Multiset.card_eq_zero, Multiset.filter_eq_nil]
  rintro y hy ⟨ζ, hζ, rfl, hu⟩
  exact h ζ ⟨hζ, hy⟩ hu

private theorem pol_one {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (s : Multiset (IrrGL (k := k))) (χ : kˣ →* ℂˣ) (h : cnt s χ = 0) : pol s χ = 1 := by
  obtain ⟨h0, hd, -⟩ := (polFacts k).2.2.2 s χ
  have e := eq_C_of_natDegree_eq_zero (hd.trans h)
  rw [e, eval_C] at h0
  rw [e, h0, C_1]
