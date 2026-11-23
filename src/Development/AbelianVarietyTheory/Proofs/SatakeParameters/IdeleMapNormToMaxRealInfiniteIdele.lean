module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousAdeleNorm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ApplyIdeleMapInfIdeleNegOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
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
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsAlgebraicHeckeCharOfWeightOfIntegerExpo
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Published GlobalTheory.ContraPair
open GlobalTheory.CuspRep.InfType GlobalTheory.CuspRep.AlgExpo

namespace GlobalTheory.GalReal

theorem ideleMap_ideleNorm_infId (E : Type) [Field E] [NumberField E] [IsCMField E] (u : (Cinf E)ˣ) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E (ideleNorm E (infId E u)) =
      infId E (u * Units.map (starRingEnd (Cinf E)).toMonoidHom u) := by
  have h1 : ∀ t : (Cinf E)ˣ, pInf E (infId E t).val = t.val := fun t => by
    change (infEq E).symm (1 - infEq E 1 + infEq E t.val) = _
    simp
  have h2 : ∀ t : (Cinf E)ˣ, pFin E (infId E t).val = 1 := fun t => by
    change (1 : Af E) - 0 + 0 = 1
    simp
  rw [GlobalTheory.GalOfCusp.ideleMap_ideleNorm, GlobalTheory.PolChar.ideleConj_eq, map_mul]
  congr 1
  refine Units.ext (ad_ext ?_ ?_)
  · change pInf E (GlobalTheory.UnitaryBC.conjAd E (infId E u).val) = _
    rw [GlobalTheory.ThetaPull.pInf_conjAd, h1, h1]
    rfl
  · change pFin E (GlobalTheory.UnitaryBC.conjAd E (infId E u).val) = _
    rw [GlobalTheory.ThetaPull.pFin_conjAd, h2, h2, map_one]

end GlobalTheory.GalReal
