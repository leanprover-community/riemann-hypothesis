module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CongruenceNumberRankThree
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.SplitDescentOfImagQuadDescent
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

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af

namespace UpperTheory.V.Z.Bc

def Down2 : Prop :=
  ∀ (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [IsAbelianGalois ℚ L] [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]
    [Algebra L Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (W : G ℚ Ω →* GL (Fin 2) (Qbar l)), Continuous W →
    IsCycWt l 0 (Matrix.GeneralLinearGroup.det.comp W) → IsIrr (W.comp (resG ℚ L Ω)) →
    (∃ (η : G ℚ Ω →* ℤˣ) (σ : G ℚ Ω), IsConjEl σ ∧ η σ = -1 ∧ ∀ s : G L Ω, η (resG ℚ L Ω s) = 1) →
    (∃ π : CuspSub L 2, (CG.mk π).IsRegAlg ∧ AttC ι (W.comp (resG ℚ L Ω)) π) → IsAutR ι W

def Desc2 : Prop := DescS ∨ Down2

end UpperTheory.V.Z.Bc
