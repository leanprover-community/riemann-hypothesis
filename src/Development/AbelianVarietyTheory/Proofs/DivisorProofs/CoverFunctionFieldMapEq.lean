module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JGenSpecializes
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAlgAtlasAtlasOf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernLeviEqConstant
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad

namespace GlobalTheory.Mean4O.Cover

theorem φ_eq_fnMap {F : Type} [Field F] [NumberField F] {Y : Var F} (V : Cover Y) :
    ∃ hη : V.π (genericPoint V.G) ⤳ genericPoint Y.X, V.φ = GlobalTheory.TrueGeo.SmallSec.fnMap V.π hη := by
  have e : V.π (genericPoint V.G) = genericPoint Y.X := by
    have hc : (spMap V.φ) (IsLocalRing.closedPoint (V.G.presheaf.stalk (genericPoint V.G))) =
        IsLocalRing.closedPoint (Y.X.presheaf.stalk (genericPoint Y.X)) :=
      Subsingleton.elim (α := PrimeSpectrum (Y.X.presheaf.stalk (genericPoint Y.X))) _ _
    refine (congrArg V.π Scheme.fromSpecStalk_closedPoint.symm).trans ?_
    refine (Scheme.Hom.comp_apply _ _ _).symm.trans ?_
    refine (congrArg (fun f => f (IsLocalRing.closedPoint (V.G.presheaf.stalk (genericPoint V.G)))) V.φ_spec).trans ?_
    refine (Scheme.Hom.comp_apply _ _ _).trans ?_
    rw [hc]
    exact Scheme.fromSpecStalk_closedPoint
  refine ⟨specializes_of_eq e, ?_⟩
  have key : Spec.map (CommRingCat.ofHom V.φ) =
      Spec.map (Y.X.presheaf.stalkSpecializes (specializes_of_eq e) ≫ V.π.stalkMap (genericPoint V.G)) := by
    rw [← cancel_mono (Y.X.fromSpecStalk (genericPoint Y.X)), Spec.map_comp, Category.assoc,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk, Scheme.SpecMap_stalkMap_fromSpecStalk]
    exact V.φ_spec.symm
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective key)

end GlobalTheory.Mean4O.Cover
