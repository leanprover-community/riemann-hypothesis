module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomProdPow
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrincipalSiegelOfGenericPrincipalSpecialAmple
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleFormBundlePowerOfPosDef
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
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.SiegelFamilyZetaUnit
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSymplecticOfTranslFixed
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings
open GlobalTheory.CechPic

noncomputable section
namespace GlobalTheory.PowFormProps

def preQ {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (Q : LB (A ⊗ A).left) (hQ : QHyp A Q) :
    SiegPre 0 1 (0 : ℤ) (specZIsTerminal.from S) where
  A := A
  ab := hQ.1
  P := Q
  isLB := hQ.2.1
  rig₁ := hQ.2.2.1
  rig₂ := hQ.2.2.2.1
  symm := hQ.2.2.2.2.1
  lev := fun _ => 1
  lev_add := fun _ _ => (_root_.mul_one _).symm
  lev_tors := fun _ => one_pow _
  geom := fun k _ _ x β z _ hz => by
    rw [map_zero] at hz
    exact absurd hz z.ne_zero

theorem formLB_props : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (Q : LB (A ⊗ A).left), QHyp A Q →
    ∀ (r : ℕ) (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef →
      IsAbelianScheme (Out.powObj A r) ∧ (formLB A Q (Out.powPr A (n := r)) W).IsLB ∧
      Out.Rigidified (Out.powObj A r) (formLB A Q (Out.powPr A (n := r)) W) ∧
      Out.RelAmple (Out.powObj A r) (formLB A Q (Out.powPr A (n := r)) W) := by
  intro S A _ _ Q hQ r W hW
  let c := preQ A Q hQ
  have hA' : Out.RelAmple c.A c.diag := hQ.2.2.2.2.2
  let pr : Fin r → (Out.powObj A r ⟶ A) := Out.powPr A
  have hmon : ∀ u, IsMonHom (pr u) := fun u => inferInstance
  have huniv : ∀ (T : Over S) (y : Fin r → (T ⟶ A)), ∃! x : T ⟶ Out.powObj A r, ∀ u, x ≫ pr u = y u := fun T y =>
    ⟨(Out.powIsLimit A r).lift (Fan.mk T y), fun u => (Out.powIsLimit A r).fac (Fan.mk T y) ⟨u⟩,
      fun x hx => (Out.powIsLimit A r).uniq (Fan.mk T y) x fun u => hx u.as⟩
  have hL : (formLB A Q pr W).IsLB := LB.isLB_linComb hQ.2.1 _ _
  have hLW : cls (formLB A Q pr W) hL = PrincipalIntegral.quad (cls c.P c.isLB) W pr := cls_linComb hQ.2.1 _ _ _
  have hadd := PrincipalIntegral.pair_mul c SemiRigid.globalFns hA'
  exact ⟨GlobalTheory.isAbelianScheme_powObj_of_isAbelianScheme A hQ.1 r, hL,
    PrincipalIntegral.rigidified hadd hmon hL hLW,
    PosDefAmple.relAmple_linComb_of_posDef SemiRigid.globalFns 0 1 r ℤ 0 S _ c (Out.powObj A r) pr W hmon huniv hA' hW⟩

end GlobalTheory.PowFormProps
