module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat
public import Development.DiscreteGroups.GlobalIrreducibility.DzGalW
public import Development.DiscreteGroups.GlobalIrreducibility.DzIsoRes
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.GelfandKazhdanReal
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.MatchCut

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.InertialTypesAlt.baseQ :
    CardRes → BaseQ := by
  intro _ E _ _ v g _ i hi
  have e : 𝓀[v.adicCompletion E] ≃+* ZMod g :=
    (Ideal.quotEquivOfEq (DiscreteGroups.sglob.DzIso.ker_redO i hi).symm).trans
      (RingHom.quotientKerEquivOfSurjective (DiscreteGroups.sglob.DzIso.redO_surjective i hi))
  exact ⟨DiscreteGroups.sglob.DzType.g_not_mem_sq v g i hi, by rw [Nat.card_congr e.toEquiv, Nat.card_zmod], ⟨e⟩⟩
