module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShapeFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcPolar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.BcAtt0
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.QuadBCwOfQuadBC0
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open UpperTheory.V.Af UpperTheory.V.Af.Bc in
theorem UpperTheory.V.Sd.upQuad :
    UpperTheory.V.Af.Hypotheses₂ → UpperTheory.V.Sd.UpQuad := by
  intro hP F E Ω _ _ _ _ _ _ _ _ _ _ _ _ l _ ι hE n _ hn r hr ⟨π, hreg, hatt⟩ hirr
  obtain ⟨P, hBC⟩ := (UpperTheory.V.Br.quadBCw hP F E hE n hn π hreg).resolve_left
    fun ⟨η, hη, ht⟩ => Bc.noTwist hP F E Ω l ι hE n r π hr hatt hirr η hη ht
  have h := UpperTheory.V.Br.bcAtt0 F E Ω l ι n r π P hBC.toIsBC0
  exact ⟨P, h.1 hreg, h.2 hatt ((Bc.irrBasic.1 _ Unit _ n _).2.1 hirr)⟩
