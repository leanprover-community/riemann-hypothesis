module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.StGlob
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGL
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.smoothAt_pf :
    UpperTheory.Gal.Gen.SmoothAt := by
  intro E _ _ _ a w₀ hw W f
  obtain ⟨e, he⟩ := GlobalTheory.locU_equiv_GL E a w₀ hw
  let p : GL (Fin a) (w₀.adicCompletion E) → finU (E := E) (n := a) := fun y =>
    ⟨(e.symm y).1, (Subgroup.mem_inf.1 (e.symm y).2).1⟩
  have hp : Continuous p :=
    Continuous.subtype_mk (continuous_subtype_val.comp e.symm.continuous) _
  have hp1 : p 1 = 1 := by
    apply Subtype.ext
    simp [p]
  have hS : IsOpen {k : finU (E := E) (n := a) | algRep W k f = f} := GlobalTheory.DefU.isSmooth_algRep W f
  refine ⟨p ⁻¹' {k : finU (E := E) (n := a) | algRep W k f = f},
    (hS.preimage hp).mem_nhds (by simp [hp1]), fun x hx hxN v g => ?_⟩
  have h1 : e.symm (cLoc w₀ x) = ⟨x, hx⟩ := by
    rw [← he ⟨x, hx⟩]
    exact e.symm_apply_apply _
  have h2 : algRep W (p (cLoc w₀ x)) f = f := hxN
  have h3 : (p (cLoc w₀ x)).1 = x := by
    simp only [p, h1]
  have h4 := congrArg (fun F : algForms W => F.1 v g) h2
  change f.1 v (g * (p (cLoc w₀ x)).1) = f.1 v g at h4
  rwa [h3] at h4
