module

public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.NonemptyGtAnOfToric
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ArcDictExpZeroSection
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.AnalyticTorusPointBaseEqHolUnifEx
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.SectionsEquivAnArcTheta
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

@[expose] public section

noncomputable section
namespace GlobalTheory.ArcDictModel
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HostModel

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l)
  (bF : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ]

end

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {c : Coeff l}
  {O : Type} [CommRing O] {β : O →+* c.F} [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ]
  {b : O →+* ℂ} {a : ArcIn D l β ℂ b} (Λ : GtAn₀ a)

end

section Bridge
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {c : Coeff l}
  {O : Type} [CommRing O] {β : O →+* c.F} [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ]
  {b : O →+* ℂ} {a : ArcIn D l β ℂ b}

theorem nonempty_of_frameValues (Λ : letI := H.starRing; ArcPts.GtAn a) : Nonempty (GtAn a) := by
  letI := H.starRing
  have h := fun (j : ℕ) (hj : NeZero j) (α : Λ.A.X) =>
    TwistedTheta.sections_equiv_anArc_theta Λ.A a.D₀ Λ.u _ Λ.lam (fun _ _ e => congrArg Λ.A.chi (Subtype.ext e)) Λ.ah j
      (Nat.one_le_iff_ne_zero.2 hj.out) (fun θ hθ => ((Λ.pow j).2 θ hθ).exists) (Λ.ε α) α (Λ.ct α)
  choose e _ he using h
  refine ⟨⟨⟨GtAnModel.toDict Λ, fun x y => (Λ.be_eq x y).symm⟩, ⟨fun j hj α => (e j hj α).toEquiv, ?_⟩⟩⟩
  intro j hj α s z i hi
  refine (he j hj α s z i hi).trans (congrArg (_ * ·) ?_)
  refine Eq.trans ?_ (Fin.prod_univ_four _).symm
  exact congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg₂ (· * ·) rfl (zpow_one _).symm) (zpow_neg_one _).symm)
    (zpow_one _).symm

end Bridge

variable {O : Type} [CommRing O] [StarRing O] [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ]
  {D₀ : Out.DegPre ℂ} [Module O D₀.X] {oa : D₀.OAct O} (d : GtDict D₀ oa)


end GlobalTheory.ArcDictModel
