module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFramesSectionValuesRatioRootOfUnity
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFrameRatio
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberLiesOverRescaleFrames
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep
open GlobalTheory.UT.CoefBasic

theorem _root_.GlobalTheory.T.thetaMember_lies_over_rescale_frames : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (Y : Type) [AddCommGroup Y] (t : Y → V) (δ : I → Y → Y) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev Y t δ) (w₀ : W0 𝔪.U.toUnifPre) (g : GtPtF 𝔪.D.toPre (FractionRing V)) (w w' : Frm 𝔪.D.toPre (FractionRing V) 1 g.b) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A) (e e' : FrAt x) (l : FractionRing V), l ≠ 0 → (∀ z J, Good 𝔪.A.L z J → (Geo.Tor.val e' (𝟙 _) z J).val = GlobalTheory.Poinc.TorsRatio.cstK z l * (Geo.Tor.val e (𝟙 _) z J).val) → (∀ z J, Good 𝔪.D.toPre.P.L z J → (val w (𝟙 _) z J).val = cstH (R := V) z l * (val w' (𝟙 _) z J).val) → 𝔪.Over' w₀ g w x e → 𝔪.Over' w₀ g w' x e' := by
  first | exact @GlobalTheory.GSep.over_rescale | exact GlobalTheory.GSep.over_rescale | (intros; apply GlobalTheory.GSep.over_rescale <;> assumption)
