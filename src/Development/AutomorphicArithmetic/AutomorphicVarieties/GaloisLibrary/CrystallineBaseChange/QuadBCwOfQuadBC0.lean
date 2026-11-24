module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.ExistenceOfGaloisRepresentationsOfHyp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.RealExistenceFromPublished
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.SplitOf
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

open NumberField Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published

namespace UpperTheory.V.Br

theorem quadBCw_of_quadBC0 (hN : GlobalTheory.Mem.LiteralAutomorphy.LitN) (hC : ExC) (hR : ExR) (h : QuadBC0) : QuadBCw := by
  intro F E _ _ _ _ _ _ _ h2 a _ ha π hr
  refine (h F E h2 a ha π hr).imp_right fun ⟨P, hP⟩ => ⟨P, hP, fun hreg ⟨χ, hχ⟩ => ?_⟩
  haveI : Algebra.IsQuadraticExtension F E := { finrank_eq_two' := h2 }
  haveI : IsCMField E := IsCMField.ofCMExtension F E
  exact splitOf hN hC hR F E h2 a ha π χ P hreg hχ hP

theorem quadBCw (P : Hypotheses₂) : QuadBCw :=
  quadBCw_of_quadBC0 P.litN (galoisExistence_from_published P) (realExistence_from_published P) P.bc

end UpperTheory.V.Br
