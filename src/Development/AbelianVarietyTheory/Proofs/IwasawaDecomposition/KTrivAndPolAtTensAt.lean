module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModuliModelUltrametricPoints
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
import Mathlib.Tactic.NormNum.Prime
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.ShFam GlobalTheory.LocM
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LocM.PolFibre

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {S : Scheme.{0}}
  {t : SAB H S} {K : Type} [Field K] {x : Sp K ⟶ S} {u : SAB H (Sp K)}

theorem exists_to_fibre (m : SABMap u t x) :
    ∃ φ : u.G.left ⟶ ((Over.pullback x).obj t.G).left, IsGrpPullback u.G ((Over.pullback x).obj t.G) (𝟙 _) φ ∧
      LBIso u.PP.L ((t.PP.L.pull (pullback.fst t.G.hom x)).pull φ) := by
  have hM := LB.isLB_pull t.PP.isLB (pullback.fst t.G.hom x)
  obtain ⟨φ, hφ, e, -⟩ := GlobalTheory.Ex.UnifModel.exists_cancel (g := 𝟙 _) (f := x) (m.cart.congr (Category.id_comp _).symm rfl)
    (isGrpPullback_pullback t.G x) t.PP.isLB hM u.PP.isLB (GlobalTheory.Ex.UnifModel.iso_of_map m)
    ⟨Out.CubePf.idIsoL _, Out.CubePf.idIsoL_isGen hM⟩
  exact ⟨φ, hφ, e⟩

theorem exists_of_fibre (m : SABMap u t x) :
    ∃ φ : ((Over.pullback x).obj t.G).left ⟶ u.G.left, IsGrpPullback ((Over.pullback x).obj t.G) u.G (𝟙 _) φ ∧
      LBIso (t.PP.L.pull (pullback.fst t.G.hom x)) (u.PP.L.pull φ) := by
  have hM := LB.isLB_pull t.PP.isLB (pullback.fst t.G.hom x)
  obtain ⟨φ, hφ, e, -⟩ := GlobalTheory.Ex.UnifModel.exists_cancel (g := 𝟙 _) (f := x)
    ((isGrpPullback_pullback t.G x).congr (Category.id_comp _).symm rfl) m.cart t.PP.isLB u.PP.isLB hM
    ⟨Out.CubePf.idIsoL _, Out.CubePf.idIsoL_isGen hM⟩ (GlobalTheory.Ex.UnifModel.iso_of_map m)
  exact ⟨φ, hφ, e⟩

theorem ample_kTriv_of_polAt (m : SABMap u t x) (hp : GlobalTheory.LN.PolAt t x) :
    RelAmple u.G u.PP.L ∧ KTriv u.G u.PP.L := by
  obtain ⟨φ, hφ, e⟩ := exists_to_fibre m
  exact amplePt _ _ (𝟙 _) _ _ φ hφ _ _ (LB.isLB_pull t.PP.isLB _) u.PP.isLB e hp.2.1 hp.2.2

theorem polAt_of_map (m : SABMap u t x) (hp : IsProper (pullback.snd t.G.hom x)) (hA : RelAmple u.G u.PP.L)
    (hK : KTriv u.G u.PP.L) : GlobalTheory.LN.PolAt t x := by
  obtain ⟨φ, hφ, e⟩ := exists_of_fibre m
  have h := amplePt _ _ (𝟙 _) _ _ φ hφ _ _ u.PP.isLB (LB.isLB_pull t.PP.isLB _) e hA hK
  exact ⟨hp, h.1, h.2⟩

end GlobalTheory.LocM.PolFibre
