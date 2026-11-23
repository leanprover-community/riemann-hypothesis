module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RelAmpleOfLocallyOnBase
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLinearHomPull
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsInvDer
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeB

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KSObj

def chartPullComp {X X' Y' : Scheme.{0}} (L : LB X) (F : X' ⟶ X) (h : Y' ⟶ X') :
    ChartPull (L.pull (h ≫ F)) (L.pull F) h :=
  have hm : ∀ (y : Y') (J : PUnit → L.ι), y ∈ (L.pull (h ≫ F)).U J → h y ∈ (L.pull F).U J := fun y J hy =>
    (mem_pull (L := L) (F := F) (x := h y) (J := J)).2 ((mem_pull (L := L) (F := h ≫ F) (x := y) (J := J)).1 hy)
  { idx := fun J => J
    le := fun J y hy => hm y J hy
    g := fun y J J' hj hj' => (gm_pull_g L (h ≫ F) (𝟙 _) y J J' hj hj').trans
      (by rw [Category.id_comp]; exact (gm_pull_g L F h y J J' (hm y J hj) (hm y J' hj')).symm) }

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem relAmple_of_map {S X : Scheme.{0}} {t : SAB H X} {u : SAB H S} {f : X ⟶ S} (m : SABMap t u f)
    (hp : IsProper u.G.hom) (hA : Out.RelAmple u.G u.PP.L) : Out.RelAmple t.G t.PP.L := by
  have hpt : IsProper t.G.hom := MorphismProperty.of_isPullback m.cart.1 hp
  obtain ⟨w, hw, -⟩ := m.lin
  refine GlobalTheory.AmpleLocal.relAmple_of_locally X t.G t.PP.L t.PP.isLB inferInstance inferInstance fun x => ?_
  obtain ⟨V, hV, hx, -⟩ := exists_isAffineOpen_mem_and_subset (X := S) (U := ⊤) (x := f x) trivial
  refine ⟨f ⁻¹ᵁ V, hx, ?_⟩
  have Hp : IsPullback ((t.G.hom ⁻¹ᵁ (f ⁻¹ᵁ V)).ι ≫ m.φ) (t.G.hom ∣_ (f ⁻¹ᵁ V)) u.G.hom ((f ⁻¹ᵁ V).ι ≫ f) :=
    (isPullback_morphismRestrict t.G.hom (f ⁻¹ᵁ V)).flip.paste_horiz m.cart.1
  obtain ⟨w', hw'⟩ : LBIso (t.PP.L.pull (t.G.hom ⁻¹ᵁ (f ⁻¹ᵁ V)).ι)
      (u.PP.L.pull ((t.G.hom ⁻¹ᵁ (f ⁻¹ᵁ V)).ι ≫ m.φ)) :=
    LBIso.chartPull (chartPullPull t.PP.L _) (chartPullComp u.PP.L m.φ _) ⟨w, hw⟩
  exact relAmple_pull (A' := Over.mk (t.G.hom ∣_ (f ⁻¹ᵁ V))) Hp u.PP.isLB (pull_isLB t.PP.isLB _)
    ((isGen_iff w').1 hw') V hV (fun y => y.2) hA

theorem proper_ample_kTriv {Dw : Datum H} {l : Geo.Tor.Level H} {B : Type} [CommRing B] {b : Base l B}
    {S : Scheme.{0}} {s : S ⟶ Sp B} (o : Obj Dw l b s) {X : Scheme.{0}} {t : SAB H X} {f : X ⟶ S}
    (m : SABMap t o.t f) :
    IsProper t.G.hom ∧ Out.RelAmple t.G t.PP.L ∧ Out.KTriv t.G t.PP.L := by
  obtain ⟨w, hw, -⟩ := m.lin
  exact ⟨MorphismProperty.of_isPullback m.cart.1 o.proper, relAmple_of_map m o.proper o.ample,
    kTriv_pull m.cart o.t.PP.isLB t.PP.isLB ((isGen_iff w).1 hw) o.ktriv⟩

end GlobalTheory.KSObj
