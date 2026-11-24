module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNoetherianModelTorsorOriginStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictHenselisationPrimeEqStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorPointOverStrictHenselisationNoetherianNormStatement
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open IsLocalRing Polynomial

namespace GlobalTheory.KeyOriginCut

theorem keyOrigin : GlobalTheory.LocAcyc.KeyOrigin := by
  have h₁ := GlobalTheory.T.strict_henselisation_prime_eq
  have h₂ := GlobalTheory.T.exists_noetherian_model_torsor_origin
  have h₃ := GlobalTheory.T.torsor_point_over_strictHenselisation_noetherianNormal
  unfold GlobalTheory.LocAcyc.KeyOrigin GlobalTheory.LocAcyc.KeyLocalWith GlobalTheory.LocAcyc.TorsorsTrivial
  intro T O _ _ _ _ _ _ _ _ hT P _ φ hφ hsh hPm hS q hq hqu D _ _ hfin hproj hff act hbij
  obtain ⟨E, _, _, _, _, _, Q, _, hQ, j, hj, ψ, hψ, D₁, _, _, act₁, htors₁, hpull₁⟩ :=
    h₁ T O hT P φ hφ hsh hS q hq hqu D act ⟨hfin, hproj, hff, hbij⟩
  obtain ⟨A, _, _, _, _, _, _, i, hi, hil, hqA, EA, _, _, _, _, _, QA, _, hQA, jA, hjA, ψA, hψA,
    DA, _, _, actA, htorsA, hpullA⟩ := h₂ T O hT q hq hqu E Q hQ j hj ψ hψ D₁ act₁ htors₁
  obtain ⟨σ, hσ⟩ :=
    h₃ T O hT P φ hφ hsh hS q hq hqu A i hi hil hqA EA QA hQA jA hjA ψA hψA DA actA htorsA
  obtain ⟨σ₁, hσ₁⟩ := hpullA σ hσ
  exact hpull₁ σ₁ hσ₁

end GlobalTheory.KeyOriginCut
