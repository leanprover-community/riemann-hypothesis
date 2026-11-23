module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FourthSideRespectsRigSymmetryCube
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

theorem _root_.GlobalTheory.T.fourthSide_respects_rig_symmetry_cube : ∀ (hG : GlobalFnsSt) (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (I : Ideal R) (I' : Ideal V) (φ : R →+* V), I.map φ ≤ I' → ∀ (D : DegPre R) (D' : DegPre V) (A : PolAV (Sp (FractionRing R))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of V))) [GrpObj G'] [IsCommMonObj G'] (U : PreU I D A G) (P' : CP G') (F : G'.left ⟶ G.left) (hF : F ≫ G.hom = G'.hom ≫ spMap φ) (wL : LB.Iso P'.L.L (U.P.L.L.pull F)), IsCPMap P' U.P (spMap φ) F hF wL → ∀ (β : D'.P.A.left ⟶ D.P.A.left) (hβ : β ≫ D.P.A.hom = D'.P.A.hom ≫ spMap φ) (v : LB.Iso D'.P.L (D.P.L.pull β)), IsCPMap (CP.ofDegPre hG D') (CP.ofDegPre hG D) (spMap φ) β hβ v → ∀ (e : ℕ) (g' : GtCoord I' D' e G') (h : (thickObj V I' e G').left ⟶ (thickObj R I e G).left), h ≫ (fstG I e G).left = (fstG I' e G').left ≫ F → g'.pG.left ≫ β = h ≫ (U.gt e).pG.left → ∀ w' : LB.Iso (P'.L.L.pull (fstG I' e G').left) (D'.P.L.pull g'.pG.left), (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj V I' e G').left) (z : Z) (jM : D.P.L.ι) (jM' : D'.P.L.ι) (jL : U.P.L.L.ι) (jL' : P'.L.L.ι), β (g'.pG.left (r z)) ∈ D.P.L.U jM → g'.pG.left (r z) ∈ D'.P.L.U jM' → F ((fstG I' e G').left (r z)) ∈ U.P.L.L.U jL → (fstG I' e G').left (r z) ∈ P'.L.L.U jL' → gw v (r ≫ g'.pG.left) z jM jM' * gw w' r z jM' (fun _ => jL') = gw (U.w e) (r ≫ h) z jM (fun _ => jL) * gw wL (r ≫ (fstG I' e G').left) z jL jL') → ∀ (T : Over (Spec (CommRingCat.of (V ⧸ I' ^ (e + 1))))) (z : T.left) (JG : (T.left ⟶ G'.left) → P'.L.L.ι) (J : (T.left ⟶ D'.P.A.left) → D'.P.L.ι), Good P'.L.L z JG → Good D'.P.L z J → ∀ W : (T ⟶ thickObj V I' e G') → (T.left.presheaf.stalk z)ˣ, (∀ x, W x = gw w' x.left z (J (x.left ≫ g'.pG.left)) (fun _ => JG (x.left ≫ (fstG I' e G').left))) → (val (L := D'.P.L) (φ := fun _ : PUnit => eSec D'.P.A) (ε := fun _ => 1) D'.rig (T.hom ≫ thick V I' e) z J = W 1 * val (L := P'.L.L) (φ := fun _ : PUnit => eSec G') (ε := fun _ => 1) P'.L.rig (T.hom ≫ thick V I' e) z JG) ∧ (∀ x : T ⟶ thickObj V I' e G', val D'.sym (x.left ≫ g'.pG.left) z J * W x = W x⁻¹ * val P'.sym (x.left ≫ (fstG I' e G').left) z JG) ∧ ∀ x y u : T ⟶ thickObj V I' e G', @id (T.left.presheaf.stalk z)ˣ (cubV D'.cub (T := (Over.map (thick V I' e)).obj T) z J ((Over.map (thick V I' e)).map x ≫ g'.pG) ((Over.map (thick V I' e)).map y ≫ g'.pG) ((Over.map (thick V I' e)).map u ≫ g'.pG)) * W (x * y) * W (x * u) * W (y * u) * W 1 = W (x * y * u) * W x * W y * W u * @id (T.left.presheaf.stalk z)ˣ (cubV P'.c (T := (Over.map (thick V I' e)).obj T) z JG ((Over.map (thick V I' e)).map x ≫ fstG I' e G') ((Over.map (thick V I' e)).map y ≫ fstG I' e G') ((Over.map (thick V I' e)).map u ≫ fstG I' e G')) := by
  first | exact @GlobalTheory.LN.FourthSide.fourth_side_vals | exact GlobalTheory.LN.FourthSide.fourth_side_vals | (intros; apply GlobalTheory.LN.FourthSide.fourth_side_vals <;> assumption)
