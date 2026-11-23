module

public import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CutoffPolynomialConjugationDerivMemShapeSpan
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpGContinuousInv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndefiniteUnitaryGroupHaarIsMulRightInvariantStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndefiniteUnitaryLieAlgebraMemIffEntriesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalIntegralZeroOfDerivativeAlongConjCurve
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PseudoCoeffShapeSmoothCompactSupportStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsMulCommutativeCentRealUJ
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory GlobalTheory.Orb GlobalTheory.PsCo.Pc1
open Formalism.REAL (UJ KG toM expG inG)

namespace GlobalTheory.PsCo.Pc1

theorem orbInt_adSpan_eq_zero : GlobalTheory.PsCo.Pc1.StOrbAd := by
  intro n ε μ _ s hs dt _ _ φ hφ
  haveI : μ.IsMulRightInvariant := GlobalTheory.T.indefiniteUnitaryGroup_haar_isMulRightInvariant n ε μ
  have hp := isProperOrbit_realUJ hs
  induction hφ using Submodule.span_induction with
  | mem φ hφ =>
    obtain ⟨Z, H, P, hZ, hH, rfl⟩ := hφ
    have hZ' : inG ε Z := (GlobalTheory.T.indefiniteUnitaryLieAlgebra_mem_iff_entries n ε Z).2 hZ
    obtain ⟨hc, hinv⟩ := GlobalTheory.expG_continuous_inv n ε Z hZ'
    obtain ⟨hsh, hd⟩ := GlobalTheory.PsCo.Pc1.B.cutoffPolynomial_conjugation_deriv_mem_shapeSpan n ε Z H P hZ hH
    have hb : bas ε H P ∈ ShapeM ε P.totalDegree := Submodule.subset_span ⟨H, P, hH, le_rfl, rfl⟩
    obtain ⟨-, -, h1, h2⟩ := GlobalTheory.T.pseudoCoeffShape_smooth_compactSupport n ε _ _ hb
    obtain ⟨-, -, h3, h4⟩ := GlobalTheory.T.pseudoCoeffShape_smooth_compactSupport n ε _ _ hsh
    refine hasOrbInt_zero_of_hasDerivAt_conj (UJ ε) μ s hp dt (fun t => expG ε Z t) hc _ _ h1 h2 h3 h4 fun g u => ?_
    have e : ∀ v : ℝ, toM ((expG ε Z v)⁻¹ * g * expG ε Z v) =
        NormedSpace.exp (-((v : ℂ) • Z)) * toM g * NormedSpace.exp ((v : ℂ) • Z) := fun v => by
      rw [← hinv v, ← Formalism.REAL.toM_expG ε Z v hZ']
      rfl
    simp only [e]
    exact hd (toM g) u
  | zero =>
    have h := (hp.hasOrbInt (dh := μ) (dt := dt) (f := fun _ => (0 : ℂ)) continuous_const HasCompactSupport.zero).smul 0
    rw [zero_mul, zero_smul] at h
    exact h
  | add φ ψ _ _ h1 h2 =>
    have h := h1.add h2
    rw [add_zero] at h
    exact h
  | smul a φ _ h1 =>
    have h := h1.smul a
    rw [mul_zero] at h
    exact h

end GlobalTheory.PsCo.Pc1
