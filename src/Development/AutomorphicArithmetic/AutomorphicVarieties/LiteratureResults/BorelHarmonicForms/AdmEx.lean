module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.InfinitesimalCharacterPullback.HasInfCharPullSub
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.AdmAbs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.IsOpenUnits
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

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

theorem UpperTheory.V.Lit.Bor.admEx :
    UpperTheory.V.Lit.Bor.AdmEx := by
  intro E _ _ _ a Ξ
  obtain ⟨R, D, hRD, hD⟩ := cxExt E a Ξ
  obtain ⟨G, hG, hadj⟩ := admissible_abs_bound (E →+* ℂ) a Ξ.d R D hRD
  refine ⟨G, hG, fun X => ?_⟩
  have hs : (star X).map (emb E) = star (X.map (emb E)) := by
    ext i j τ
    exact UpperTheory.V.FieldIso.coord_star τ (X j i)
  rw [← hD, ← hD, hs]
  exact hadj _
