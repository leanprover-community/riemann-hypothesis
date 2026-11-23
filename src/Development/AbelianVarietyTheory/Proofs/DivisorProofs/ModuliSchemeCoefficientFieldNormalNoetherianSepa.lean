module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsOverIff
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DivMemOfForallPowSuccDivPowMem

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin

theorem xF_charZero_residueField {X : Scheme.{0}} {K : Type} [Field K] [CharZero K] (s : X ⟶ Sp K) (x : X) :
    CharZero (X.residueField x) := by
  let φ : K →+* X.residueField x :=
    (X.residue x).hom.comp ((X.presheaf.germ ⊤ x trivial).hom.comp
      (s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom))
  exact (RingHom.charZero_iff φ.injective).1 inferInstance

theorem xF_props : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) , Geo.Tor.IsNormalScheme (Xo.XF c) ∧ IsLocallyNoetherian (Xo.XF c) ∧ (∀ x : Xo.XF c, CharZero ((Xo.XF c).residueField x)) ∧ IsSeparated (pullback.snd _ _ : Xo.XF c ⟶ Sp c.F) ∧ LocallyOfFiniteType (pullback.snd _ _ : Xo.XF c ⟶ Sp c.F) ∧ QuasiCompact (pullback.snd _ _ : Xo.XF c ⟶ Sp c.F) := by
  intro E _ _ _ H Dw l Xo c
  obtain ⟨N, i, hi, hq, hc⟩ := Xo.qproj
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth Dw.dim _
  have : IsProper (PSpace.str (KA l) N) := isProper_str (KA l) N
  have : IsSeparated Xo.s := by rw [← hc]; infer_instance
  have : QuasiCompact Xo.s := by rw [← hc]; infer_instance
  have hsm : Smooth (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) := inferInstance
  obtain ⟨-, hn, hl⟩ := isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _ _ hsm
  exact ⟨hn, hl, fun x => xF_charZero_residueField (pullback.snd _ _) x, inferInstance, inferInstance, inferInstance⟩

end GlobalTheory.UMin
